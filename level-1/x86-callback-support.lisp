;;;
;;; Copyright 2005-2009 Clozure Associates
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


#+x8664-target  
(defun make-callback-trampoline (index &optional info)
  (declare (ignore info))
  (let* ((p (%allocate-callback-pointer 16))
         (addr #.(subprim-name->offset '.SPcallback)))
    (setf (%get-unsigned-byte p 0) #x41 ; movl $n,%r11d
          (%get-unsigned-byte p 1) #xc7
          (%get-unsigned-byte p 2) #xc3
          (%get-unsigned-byte p 3) (ldb (byte 8 0) index)
          (%get-unsigned-byte p 4) (ldb (byte 8 8) index)
          (%get-unsigned-byte p 5) (ldb (byte 8 16) index)
          (%get-unsigned-byte p 6) (ldb (byte 8 24) index)
          (%get-unsigned-byte p 7) #xff  ; jmp *
          (%get-unsigned-byte p 8) #x24
          (%get-unsigned-byte p 9) #x25
          (%get-unsigned-byte p 10) (ldb (byte 8 0) addr)
          (%get-unsigned-byte p 11) (ldb (byte 8 8) addr)
          (%get-unsigned-byte p 12) (ldb (byte 8 16) addr)
          (%get-unsigned-byte p 13) (ldb (byte 8 24) addr))
    p))
          
#+x8632-target          
(defun make-callback-trampoline (index &optional info)
  (let* ((p (%allocate-callback-pointer 12))
         (addr #.(subprim-name->offset '.SPcallback)))
    ;; If the optional info parameter is supplied, it will contain
    ;; some stuff in bits 23 through 31.
    ;;
    ;; If bit 23 is set, that indicates that the caller will pass a
    ;; "hidden" argument which is a pointer to appropriate storage for
    ;; holding a returned structure.  .SPcallback will have to discard
    ;; this extra argument upon return.
    ;;
    ;; The high 8 bits denote the number of words that .SPcallback
    ;; will have to discard upon return (used for _stdcall on
    ;; Windows).  Bit 23 won't be set in this case: we will have
    ;; already added in the extra word to discard if that's necessary.
    ;; 
    ;; These bits are be packed into the value that .SPcallback
    ;; receives in %eax.  Bits 0 through 22 are the callback index.
    (if info
      (setf (ldb (byte 23 0) info) index)
      (setq info index))
    (setf (%get-unsigned-byte p 0) #xb8 ; movl $n,%eax
          (%get-unsigned-byte p 1) (ldb (byte 8 0) info)
          (%get-unsigned-byte p 2) (ldb (byte 8 8) info)
          (%get-unsigned-byte p 3) (ldb (byte 8 16) info)
          (%get-unsigned-byte p 4) (ldb (byte 8 24) info)
          (%get-unsigned-byte p 5) #xff  ; jmp *
          (%get-unsigned-byte p 6) #x24
          (%get-unsigned-byte p 7) #x25
          (%get-unsigned-byte p 8) (ldb (byte 8 0) addr)
          (%get-unsigned-byte p 9) (ldb (byte 8 8) addr)
          (%get-unsigned-byte p 10) (ldb (byte 8 16) addr)
          (%get-unsigned-byte p 11) (ldb (byte 8 24) addr))
    p))

;;; This function is magic, and it can only be called from
;;; an unwind-protect cleanup form (making it even more magic.)
;;; If we can tell that we reached the unwind-protect via THROW,
;;; return a list of the target catch tag and all values being
;;; thrown.
(defun %throwing-through-cleanup-p ()
  ;; when we enter and unwind-protect cleanup on x8664, the
  ;; top frame on the tstack contains state information that's
  ;; used both by THROW and by normal exit from the protected
  ;; form.  That state information contains a count of the number
  ;; of catch/unwind-protect frames still to be processed (non-zero
  ;; only in the case where we're actually throwing), the value(s)
  ;; being thrown, and a return address that isn't interesting to
  ;; us.
  ;; A tstack frame is always doubleword aligned, and the first two
  ;; words are a backpointer to the previous tstack frame and a
  ;; pointer into the main lisp stack.  We have 3 fixed words (value
  ;; count, return address, frame count) with the values following
  ;; the frame count (value 0 follows immediately.)
  ;; A cleanup form is always called from either .SPnthrowvalues
  ;; of .SPnthrow1value, and those subprims can be called either
  ;; by .SPthrow (in which case the return address in the frame
  ;; will not be in the code area) or by Lisp code
  ;; (in which case it will.)
  ;; We (have to) just assume that the frame on top of the temp
  ;; stack is context info for the nthrow stuff.  Tracing this
  ;; function may violate this assumption and cause misbehavior
  ;; here.
  (let* ((frame (%current-tsp))
         (frame-count (%lisp-word-ref frame 4))
         (address (%fixnum-address-of (%lisp-word-ref frame 3)))
         (throwing (zerop (external-call "in_code_area" :unsigned-long address :boolean))))
    (declare (fixnum frame))
    (if throwing
      (collect ((info))
        (info (nth-catch-frame-tag frame-count))
        (let* ((valptr (+ frame 5)))
          (declare (fixnum valptr))
          (dotimes (i (%lisp-word-ref frame 2))
            (declare (fixnum i))
            (info (%lisp-word-ref valptr i))))
        (info)))))
