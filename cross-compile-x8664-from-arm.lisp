(in-package :ccl)
;; Break some circular dependencies w.r.t package definitions.
(defpackage :x86 (:use :cl))
(defpackage :x8632 (:use :cl))
(defpackage :x8664 (:use :cl))
(defpackage :x86-linux64 (:use :cl))

(push (lambda (n)
        (require-module (intern (string n) :ccl) t))
      *module-provider-functions*)

(setf ccl::*warn-if-redefine-kernel* nil)

;; Gotta patch ARM2-NLEXIT, we generate a huge VDIFF which
;; the assembler can't pack into one immediate.
(defun arm2-nlexit (seg xfer &optional (nlevels 0))
  (let* ((numnthrow 0)
         (n *arm2-undo-count*)
         (cstack *arm2-cstack*)
         (vstack *arm2-vstack*)
         (target-cstack)
         (target-vstack)
         (lastcatch n)
         (i nil)
         (returning (eq xfer $backend-return))
         (junk1 nil)
         (unbind ())
         (dest (%i- n nlevels))
         (retval *arm2-returning-values*)
         reason)
    (declare (ignorable junk1))
    (with-arm-local-vinsn-macros (seg)
      (when (neq 0 nlevels)
        (let* ((numnlispareas 0))
          (declare (fixnum numnlispareas))
          (flet ((popnlispareas ()
                   (dotimes (i numnlispareas)
                     (! discard-temp-frame)))
                 (throw-through-numnthrow-catch-frames ()
                   (when (neq 0 numnthrow)
                     (arm2-lri seg arm::imm0 (ash numnthrow *arm2-target-fixnum-shift*))
                     (if retval
                       (! nthrowvalues)
                       (! nthrow1value))
                     (setq numnthrow 0)
                     (multiple-value-setq (junk1 cstack vstack)
                       (arm2-decode-stack (aref *arm2-undo-stack* lastcatch))))))
            (while (%i> n dest)
              (cond ((eql $undocatch (setq reason (aref *arm2-undo-because* (setq n (%i- n 1)))))
                     (popnlispareas)
                     (setq numnthrow (%i+ numnthrow 1) lastcatch n))
                    ((eql $undostkblk reason)
                     (throw-through-numnthrow-catch-frames)
                     (incf numnlispareas))
                    ((eql $undo-arm-c-frame reason)
                     (! discard-c-frame))))
            (throw-through-numnthrow-catch-frames)
            (setq i lastcatch)
            (while (%i> i dest)
              (let ((reason (aref *arm2-undo-because* (setq i (%i- i 1)))))
                (if (or (eql reason $undospecial)
                        (eql reason $undointerruptlevel))
                  (push reason unbind))))
            (if unbind
              (arm2-dpayback-list seg (nreverse unbind)))
            (when (and (neq lastcatch dest)
                       (%i>
                        vstack
                        (setq target-vstack 
                              (nth-value 2 (arm2-decode-stack (aref *arm2-undo-stack* dest)))))
                       (neq retval t))
              (unless returning
                (let ((vdiff (%i- vstack target-vstack)))
                  (if retval
                    (progn
                      (arm2-lri seg arm::imm0 vdiff)
                      (! slide-values))
                    ;; Move VSP chunk-wise so that we don't run out of
                    ;; immediate encoding.
                    (progn
                      (loop with chunk-size = 256
                            while (> vdiff chunk-size)
                            do (! adjust-vsp chunk-size)
                               (decf vdiff chunk-size))
                      (! adjust-vsp vdiff))))))
            (setq numnlispareas 0)
            (while (%i> lastcatch dest)
              (let ((reason (aref *arm2-undo-because* (setq lastcatch (%i- lastcatch 1)))))
                (setq target-cstack (nth-value 1
                                               (arm2-decode-stack (aref *arm2-undo-stack* lastcatch))))
                (if (eq reason $undostkblk)
                  (incf numnlispareas))
                (if (%i> cstack target-cstack)
                  (with-arm-local-vinsn-macros (seg)
                    (! adjust-sp (%i- cstack target-cstack))))
                                        ; else what's going on? $sp-stkcons, for one thing
                (setq cstack target-cstack)))
            (popnlispareas)))
        vstack))))

;; Recompile the FASL dumper, we changed the layout.
(require-module 'nfcomp t)
;; We also added a GC trap to allocate in the code area.
(require-module 'arch t)
;; And we added an AREA-CODE constant.
(require-module 'lispequ t)

(defun target-xcompile-ccl (target &optional force)
  (let* ((*target-backend* *host-backend*))
    (require-update-modules *sysdef-modules* force)) ;in the host
  (let* ((backend (or (find-backend target) *target-backend*))
	 (arch (backend-target-arch-name backend)))
    ;; NXENV won't compile if we don't have any vinsns handy.
    (require-module 'x8664-vinsns t)
    (target-compile-modules 'nxenv target force)
    (target-compile-modules *compiler-modules* target force)
    (target-compile-modules (target-compiler-modules arch) target force)
    ;; l1-utils won't compile if we lack X86-LINUX64::EXPAND-FF-CALL.
    (require-module 'ffi-linuxx8664 t)
    ;; We also need x86-lapmacros earlier.
    (require-module 'x86-lapmacros t)
    (target-compile-modules (target-level-1-modules target) target force)
    (target-compile-modules (target-lib-modules target) target force)
    (target-compile-modules *sysdef-modules* target force)
    (target-compile-modules (set-difference *aux-modules* '(core-files dominance)) target force)
    (target-compile-modules *code-modules* target force)
    (target-compile-modules (target-xdev-modules arch) target force)))

(mapc #'require '(:x8664-arch :x8632-arch :x862 :x8664-backend :xfasload))
(load "ccl:xdump;heap-image.lisp")
(cross-compile-ccl :linuxx8664)

(defun cross-xload-level-0 (target &optional (recompile t))
  (with-cross-compilation-target (target)
    (let* ((*target-backend* (find-backend target)))
      (require-module 'x8664-vinsns t)
      (require-module 'ffi-linuxx8664 t)
      (load "ccl:xdump;xx8664-fasload.lisp")
      (target-xload-level-0 target recompile))))

(setf *x862-generate-casejump* nil)
(cross-xload-level-0 :linuxx8664)
