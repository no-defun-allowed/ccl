(require :uiop)

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

(mapc #'require '(:x8664-arch :x8632-arch :x862 :x8664-backend :xfasload :x8664-vinsns))

(in-package :cl-user)
(defun xdisassemble (xfunction)
  (let ((byte-vector (ccl::uvref xfunction 0)))
    (uiop:with-temporary-file (:pathname p)
      (with-open-file (s p :direction :output :element-type '(unsigned-byte 8))
        (map 'nil (lambda (b) (write-byte b s)) (subseq byte-vector 7)))
      (uiop:run-program `("/home/raspberry/binutils-gdb/binutils/objdump"
                          "-b" "binary" "-m" "i386:x86-64" "-M" "intel"
                          "-D" ,(namestring p))
                        :output *debug-io* :error-output *debug-io*))
    (loop for n from 1 below (ccl::uvsize xfunction)
          do (format *debug-io* "~&~18<[r13+0x~X]:~>  ~S~%"
                     (+ (ash n x8664::word-shift) x8664::misc-function-offset)
                     (ccl::uvref xfunction n)))))

(defun xcompile (form &key name)
  (let ((f (ccl::compile-named-function form :target :linuxx8664 :name name)))
    (xdisassemble f)
    f))

(defmacro xdefun (name lambda-list &body body)
  `(xcompile '(lambda ,lambda-list (block ,name ,@body))))

(let ((ccl::*target-backend* (ccl::find-backend :linuxx8664)))
  (require :x86-lapmacros))

(defmacro xlap (name arglist &body body)
  `(xdisassemble
    (let ((ccl::*target-backend* (ccl::find-backend :linuxx8664)))
      (ccl::%define-x8664-lap-function ',name '((let ,arglist ,@body))))))
