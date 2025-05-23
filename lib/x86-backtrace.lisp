;;;-*-Mode: LISP; Package: CCL -*-
;;;
;;; Copyright 2006-2009 Clozure Associates
;;;
;;; Licensed under the Apache License, Version 2.0 (the "License");
;;; you may not use this file except in compliance with the License.
;;; You may obtain a copy of the License at
;;;
;;;     http://www.apache.org/licenses/LICENSE-2.0
;;;
;;; Unless required by applicable law or agreed to in writing, software
;;; distributed under the License is distributed on an "AS IS" BASIS,
;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;; See the License for the specific language governing permissions and
;;; limitations under the License.


(in-package "CCL")


;;; Returns two values:
;;;  [nil, nil] if it can be reliably determined that function uses no registers at PC
;;;  [mask, saved-location]  if it can be reliably determined that the registers specified by "mask"
;;;      were saved at "saved-location" in the function's stack frame
;;;  [mask, nil] if registers in "mask" MAY have been saved, but we don't know how to restore them
;;;      (perhaps because the "at-pc" argument wasn't specified.


(defun registers-used-by (function &optional at-pc)
  (multiple-value-bind (mask stack-location rpc)
      (%function-register-usage function)
    (if (or (null mask)
            (and at-pc rpc (<= at-pc rpc)))
      (values nil nil)
      (values (canonicalize-register-mask mask) (if (and at-pc rpc) stack-location)))))

(defun canonicalize-register-mask (mask)
  (dpb (ldb (byte 2 14) mask) (byte 2 2) (ldb (byte 2 11) mask)))

(defun xcf-p (p)
  (eql 0 (%fixnum-ref p target::lisp-frame.return-address)))

(defun %current-xcf ()
  (do* ((q (%get-frame-ptr) (%%frame-backlink q)))
       ((zerop q))
    (declare (fixnum q))
    (when (xcf-p q) (return q))))

;;; Try to determine the program counter value, relative to an xcf's nominal function.
(defun pc-from-xcf (xcf)
  (let* ((nominal-function (%fixnum-ref xcf target::xcf.nominal-function))
         (containing-object (%fixnum-ref xcf target::xcf.containing-object)))
    (when (typep nominal-function 'function)
      (if (eq containing-object (function-to-function-vector nominal-function))
        (- (%fixnum-ref xcf target::xcf.relative-pc)
	   #+x8632-target x8632::fulltag-misc
	   #+x8664-target x8664::tag-function)
        (let* ((tra (%fixnum-ref xcf target::xcf.ra0)))
          #+x8632-target
          (if #+x8632-target
              (and (= (fulltag tra) x8632::fulltag-tra)
                   (eq nominal-function (%return-address-function tra)))
              (%return-address-offset tra))
          #+x8664-target
          (%fixnum-ref xcf target::xcf.relative-pc))))))
            
(defun cfp-lfun (p)
  (if (xcf-p p)
    (values
     (%fixnum-ref p target::xcf.nominal-function)
     (pc-from-xcf p))
    (%cfp-lfun p)))

;;; On PPC, some frames on the control stack are associated with catch
;;; frames rather than with function calls.  The whole concept doesn't
;;; really apply here (e.g., nothing we encounter while walking frame
;;; pointer links belongs to a catch frame.)
(defun catch-csp-p (p context)
  (declare (ignore p context)))

(defun %raw-frame-ref (frame context idx bad)
  (declare (fixnum frame idx))
  (let* ((base (parent-frame frame context))
         (raw-size (- base frame)))
    (declare (fixnum base raw-size))
    (if (and (>= idx 0)
             (< idx raw-size))
      (let* ((addr (- (the fixnum (1- base))
                      idx
                      #+x8664-target 1)))
        (multiple-value-bind (db-count first-db last-db)
            (count-db-links-in-frame frame base context)
          (let* ((is-db-link
                  (unless (zerop db-count)
                    (do* ((last last-db (previous-db-link last first-db)))
                         ((null last))
                      (when (= addr last)
                        (return t))))))
            (if is-db-link
              (oldest-binding-frame-value context addr)
              (%fixnum-ref addr)))))
      bad)))

(defun %raw-frame-set (frame context idx new)
  (declare (fixnum frame idx))
  (let* ((base (parent-frame frame context))
         (raw-size (- base frame)))
    (declare (fixnum base raw-size))
    (if (and (>= idx 0)
             (< idx raw-size))
      (let* ((addr (- (the fixnum (1- base))
                      idx)))
        (multiple-value-bind (db-count first-db last-db)
            (count-db-links-in-frame frame base context)
          (let* ((is-db-link
                  (unless (zerop db-count)
                    (do* ((last last-db (previous-db-link last first-db)))
                         ((null last))
                      (when (= addr last)
                        (return t))))))
            (if is-db-link
              (setf (oldest-binding-frame-value context addr) new)
              (setf (%fixnum-ref addr) new))))))))

(defun %stack< (index1 index2 &optional context)
  (let* ((tcr (if context (bt.tcr context) (%current-tcr)))
         (vs-area (%fixnum-ref tcr (- target::tcr.vs-area
				      target::tcr-bias))))
    (and (%ptr-in-area-p index1 vs-area)
         (%ptr-in-area-p index2 vs-area)
         (< (the fixnum index1) (the fixnum index2)))))




(defun register-number->saved-register-index (regnum)
  (break "regnum = ~s" regnum))


(defun get-register-value (address last-catch index)
  (if address
    (%fixnum-ref address)
    (uvref last-catch (+ index 
			 #+x8632-target
			 x8632::catch-frame.db-link-cell
			 #+x8664-target
			 x8664::catch-frame.db-link-cell))))

;;; Inverse of get-register-value

(defun set-register-value (value address last-catch index)
  (if address
    (%fixnum-set address value)
    (setf (uvref last-catch (+ index
			       #+x8632-target
			       x8632::catch-frame.db-link-cell
			       #+x8664-target
                               x8664::catch-frame.db-link-cell))
          value)))

(defun %find-register-argument-value (context cfp regval bad)
  (let* ((last-catch (last-catch-since cfp context))
         (index (register-number->saved-register-index regval)))
    (do* ((frame cfp (child-frame frame context))
          (first t))
         ((null frame))
      (if (xcf-p frame)
        (with-macptrs (xp)
          (%setf-macptr-to-object xp (%fixnum-ref frame x8664::xcf.xp))
          (return-from %find-register-argument-value
            (encoded-gpr-lisp xp regval)))
        (progn
          (unless first
            (multiple-value-bind (lfun pc)
                (cfp-lfun frame)
              (when lfun
                (multiple-value-bind (mask where)
                    (registers-used-by lfun pc)
                  (when (if mask (logbitp index mask))
                    (return-from %find-register-argument-value
                      (if where
                        (let ((offset (logcount (logandc2 mask (1- (ash 1 (1+ index)))))))
                          (raw-frame-ref frame context (+ where offset) bad))
                        bad)))))))
          (setq first nil))))
    (get-register-value nil last-catch index)))

(defun %set-register-argument-value (context cfp regval new)
  (let* ((last-catch (last-catch-since cfp context))
         (index (register-number->saved-register-index regval)))
    (do* ((frame cfp (child-frame frame context))
          (first t))
         ((null frame))
      (if (xcf-p frame)
        (with-macptrs (xp)
          (%setf-macptr-to-object xp (%fixnum-ref frame x8664::xcf.xp))
          (return-from %set-register-argument-value
            (setf (encoded-gpr-lisp xp regval) new)))
        (progn
          (unless first
            (multiple-value-bind (lfun pc)
                (cfp-lfun frame)
              (when lfun
                (multiple-value-bind (mask where)
                    (registers-used-by lfun pc)
                  (when (if mask (logbitp index mask))
                    (incf where (logcount (logandc2 mask (1- (ash 1 (1+ index))))))

                    (return-from %set-register-argument-value
                      (raw-frame-set frame context where new)))))))
          (setq first nil))))
    (set-register-value new nil last-catch index)))

;;; Used for printing only.
(defun index->address (p)
  (ldb (byte #+32-bit-target 32 #+64-bit-target 64 0)  (ash p target::fixnumshift)))

(defun exception-frame-p (x)
  (and x (xcf-p x)))

;;; Function has failed a number-of-arguments check; return a list
;;; of the actual arguments.
;;; On x86-64, the kernel has finished the frame and pushed everything
;;; for us, so all that we need to do is to hide any inherited arguments.
(defun arg-check-call-arguments (fp function)
  (when (xcf-p fp)
    (with-macptrs (xp)
      (%setf-macptr-to-object xp (%fixnum-ref fp target::xcf.xp))
      (let* ((numinh (ldb $lfbits-numinh (lfun-bits function)))
             (nargs (- (xp-argument-count xp) numinh))
             (p (- (%fixnum-ref fp target::xcf.backptr)
                   (* target::node-size numinh))))
        (declare (fixnum numinh nargs p))
        (collect ((args))
          (dotimes (i nargs (args))
            (args (%fixnum-ref p (- target::node-size)))
            (decf p)))))))

(defun vsp-limits (frame context)
  (let* ((parent (parent-frame frame context)))
    (if (xcf-p frame)
      (values (+ frame (ash target::xcf.size (- target::word-shift)))
              parent)
      (let* ((tra (%fixnum-ref frame target::lisp-frame.return-address)))
        (values (+ frame 2 (if (eq tra (%get-kernel-global ret1valaddr)) 1 0))
                parent)))))

(defun last-catch-since (fp context)
  (let* ((tcr (if context (bt.tcr context) (%current-tcr)))
         (catch (%catch-top tcr))
         (last-catch nil))
    (loop
      (unless catch (return last-catch))
      (let ((catch-fp (uvref catch
			     #+x8632-target
			     x8632::catch-frame.ebp-cell
			     #+x8664-target
			     x8664::catch-frame.rbp-cell)))
        (when (%stack< fp catch-fp context) (return last-catch))
        (setq last-catch catch
              catch (next-catch catch))))))

(defun last-xcf-since (target-fp start-fp context)
  (do* ((last-xcf nil)
        (fp start-fp (parent-frame fp context)))
       ((or (eql fp target-fp)
            (null fp)
            (%stack< target-fp fp)) last-xcf)
    (if (xcf-p fp) (setq last-xcf fp))))

(defun match-local-name (cellno info pc)
  (when info
    (let* ((syms (%car info))
           (ptrs (%cdr info)))
      (dotimes (i (length syms))
        (let ((j (%i+ i (%i+ i i ))))
          (and (eq (uvref ptrs j) (%ilogior (%ilsl (+ 6 target::word-shift) cellno) #o77))
               (%i>= pc (uvref ptrs (%i+ j 1)))
               (%i< pc (uvref ptrs (%i+ j 2)))
               (return (aref syms i))))))))

(defun apply-in-frame (frame function arglist &optional context)
  (setq function (coerce-to-function function))
  (let* ((parent (parent-frame frame context)))
    (when parent
      (if (xcf-p parent)
        (error "Can't unwind to exception frame ~s" frame)
        (setq frame parent))
      (if (or (null context)
              (eq (bt.tcr context) (%current-tcr)))
        (%apply-in-frame frame function arglist)
        (let* ((process (tcr->process (bt.tcr context))))
          (if process
            (process-interrupt process #'%apply-in-frame frame function arglist)
            (error "Can't find process for backtrace context ~s" context)))))))

(defun return-from-frame (frame &rest values)
  (apply-in-frame frame #'values values nil))
    

(defun last-tsp-before (target)
  (declare (fixnum target))
  (do* ((tsp (%fixnum-ref (%current-tcr) (- target::tcr.save-tsp
					    target::tcr-bias))
             (%fixnum-ref tsp target::tsp-frame.backptr)))
       ((zerop tsp) nil)
    (declare (fixnum tsp))
    (when (> (the fixnum (%fixnum-ref tsp #+x8632-target x8632::tsp-frame.ebp
				          #+x8664-target x8664::tsp-frame.rbp))
             target)
      (return tsp))))

    


;;; We can't determine this reliably (yet).
(defun last-foreign-sp-before (target)
  (declare (fixnum target))
  (do* ((cfp (%fixnum-ref (%current-tcr) (- target::tcr.foreign-sp
					    target::tcr-bias))
             (%fixnum-ref cfp target::csp-frame.backptr)))
       ((zerop cfp))
    (declare (fixnum cfp))
    (let* ((rbp (%fixnum-ref cfp #+x8632-target x8632::csp-frame.ebp
			         #+x8664-target x8664::csp-frame.rbp)))
      (declare (fixnum rbp))
      (if (> rbp target)
        (return cfp)
        (if (zerop rbp)
          (return nil))))))


(defun %tsp-frame-containing-progv-binding (db)
  (declare (fixnum db))
  (do* ((tsp (%fixnum-ref (%current-tcr) (- target::tcr.save-tsp
					    target::tcr-bias)) next)
        (next (%fixnum-ref tsp target::tsp-frame.backptr)
              (%fixnum-ref tsp target::tsp-frame.backptr)))
       ()
    (declare (fixnum tsp next))
    (let* ((rbp (%fixnum-ref tsp #+x8632-target x8632::tsp-frame.ebp
			         #+x8664-target x8664::tsp-frame.rbp)))
      (declare (fixnum rbp))
      (if (zerop rbp)
        (return (values nil nil))
        (if (and (> db tsp)
                 (< db next))
          (return (values tsp rbp)))))))

        




(defun last-binding-before (frame)
  (declare (fixnum frame))
  (do* ((db (%current-db-link) (%fixnum-ref db 0))
        (tcr (%current-tcr))
        (vs-area (%fixnum-ref tcr (- target::tcr.vs-area
				     target::tcr-bias)))
        (vs-low (%fixnum-ref vs-area target::area.low))
        (vs-high (%fixnum-ref vs-area target::area.high)))
       ((eql db 0) nil)
    (declare (fixnum db vs-low vs-high))
    (if (and (> db vs-low)
             (< db vs-high))
      (if (> db frame)
        (return db))
      ;; db link points elsewhere; PROGV uses the temp stack
      ;; to store an indefinite number of bindings.
      (multiple-value-bind (tsp rbp)
          (%tsp-frame-containing-progv-binding db)
        (if tsp
          (if (> rbp frame)
            (return db)
            ;; If the tsp frame is too young, we can skip
            ;; all of the bindings it contains.  The tsp
            ;; frame contains two words of overhead, followed
            ;; by a count of binding records in the frame,
            ;; followed by the youngest of "count" binding
            ;; records (which happens to be the value of
            ;; "db".)  Skip "count" binding records.
            (dotimes (i (the fixnum (%fixnum-ref tsp target::dnode-size)))
              (setq db (%fixnum-ref db 0))))
          ;; If the binding record wasn't on the temp stack and wasn't
          ;; on the value stack, that probably means that things are
          ;; seriously screwed up.  This error will be almost
          ;; meaningless to the user.
          (error "binding record (#x~16,'0x/#x~16,'0x) not on temp or value stack" (index->address db) db))))))
          


(defun find-x8664-saved-nvrs (frame start-fp context)
  (declare (ignore frame start-fp context)))
                                         
              
         
(defun %apply-in-frame (frame function arglist)
  (declare (ignore frame function arglist))
  (target-arch-case
   (:x8632 (error "%apply-in-frame doesn't work for x8632 yet"))
   (:x8664
    (error "%apply-in-frame has bitrotted"))))

            
    
