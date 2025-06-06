;;;-*- Mode: Lisp; Package: CCL -*-
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

#+x8664-target
(progn

;;; It's easier to keep this is LAP; we want to play around with its
;;; constants.


;;; This just maps a SLOT-ID to a SLOT-DEFINITION or NIL.
;;; The map is a vector of (UNSIGNED-BYTE 8); this should
;;; be used when there are fewer than 255 slots in the class.
(defx86lapfunction %small-map-slot-id-lookup ((slot-id arg_z))
  (movq (@ 'map (% nfn)) (% temp1))
  (svref slot-id slot-id.index arg_x)
  (vector-length temp1 imm0)
  (xorl (%l imm1) (%l imm1))
  (rcmpq (% arg_x) (% imm0))
  (movq (@ 'table (% nfn)) (% temp0))
  (ja @have-table-index)
  (movq (% arg_x) (% imm1))
  (shrq ($ x8664::word-shift) (% imm1))
  (movzbl (@ x8664::misc-data-offset (% temp1) (% imm1)) (%l imm1))
  @have-table-index
  (movq (@ x8664::misc-data-offset (% temp0) (% imm1) 8) (% arg_z))
  (single-value-return))

;;; The same idea, only the map is a vector of (UNSIGNED-BYTE 32).
(defx86lapfunction %large-map-slot-id-lookup ((slot-id arg_z))
  (movq (@ 'map (% nfn)) (% temp1))
  (svref slot-id slot-id.index arg_x)
  (vector-length temp1 imm0)
  (xorl (%l imm1) (%l imm1))
  (rcmpq (% arg_x) (% imm0))
  (movq (@ 'table (% nfn)) (% temp0))
  (ja @have-table-index)
  (movq (% arg_x) (% imm1))
  (shrq ($ 1) (% imm1))
  (movl (@ x8664::misc-data-offset (% temp1) (% imm1)) (%l imm1))
  @have-table-index
  (movq (@ x8664::misc-data-offset (% temp0) (% imm1) 8) (% arg_z))
  (single-value-return))


(defx86lapfunction %small-slot-id-value ((instance arg_y) (slot-id arg_z))
  (movq (@ 'map (% nfn)) (% temp1))
  (svref slot-id slot-id.index arg_x)
  (vector-length temp1 imm0)
  (xorl (%l imm1) (%l imm1))
  (rcmpq (% arg_x) (% imm0))
  (movq (@ 'table (% nfn)) (% temp0))
  (ja @missing)
  (movq (% arg_x) (% imm1))
  (shrq ($ x8664::word-shift) (% imm1))
  (movzbl (@ x8664::misc-data-offset (% temp1) (% imm1)) (%l imm1))
  (testl (%l imm1) (%l imm1))
  (je @missing)
  (movq (@ x8664::misc-data-offset (% temp0) (% imm1) 8) (% arg_z))
  (movq (@ 'class (% nfn)) (% arg_x))
  (set-nargs 3)
  (jump-function (@ '%maybe-std-slot-value-using-class (% nfn)))
  @missing                              ; (%slot-id-ref-missing instance id)
  (set-nargs 2)
  (jump-function (@ '%slot-id-ref-missing (% nfn))))

(defx86lapfunction %large-slot-id-value ((instance arg_y) (slot-id arg_z))  
  (movq (@ 'map (% nfn)) (% temp1))
  (svref slot-id slot-id.index arg_x)
  (vector-length temp1 imm0)
  (xorl (%l imm1) (%l imm1))
  (rcmpq (% arg_x) (% imm0))
  (movq (@ 'table (% nfn)) (% temp0))
  (ja @missing)
  (movq (% arg_x) (% imm1))
  (shrq ($ 1) (% imm1))
  (movl (@ x8664::misc-data-offset (% temp1) (% imm1)) (%l imm1))
  (testl (%l imm1) (%l imm1))
  (je @missing)
  (movq (@ x8664::misc-data-offset (% temp0) (% imm1) 8) (% arg_z))
  (movq (@ 'class (% nfn)) (% arg_x))
  (set-nargs 3)
  (jump-function (@ '%maybe-std-slot-value-using-class (% nfn)))
  @missing                              ; (%slot-id-ref-missing instance id)
  (set-nargs 2)
  (jump-function (@ '%slot-id-ref-missing (% nfn))))

  
(defx86lapfunction %small-set-slot-id-value ((instance arg_x)
                                             (slot-id arg_y)
                                             (new-value arg_z))
  (movq (@ 'map (% nfn)) (% temp1))
  (svref slot-id slot-id.index imm1)
  (vector-length temp1 imm0)
  (rcmpq (% imm1) (% imm0))
  (movq (@ 'table (% nfn)) (% temp0))
  (ja @missing)
  (shrq ($ x8664::word-shift) (% rdx))
  (movzbl (@ x8664::misc-data-offset (% temp1) (% imm1)) (%l imm1))
  (testl (%l imm1) (%l imm1))
  (je @missing)
  (popq (% ra0))
  (push-reserved-frame)
  (pushq (@ 'class (% nfn)))
  (movq (@ x8664::misc-data-offset (% temp0) (% imm1) 8) (% arg_y))
  (set-nargs 4)
  (pushq (% ra0))
  (jump-function (@ '%maybe-std-setf-slot-value-using-class (% nfn)))
  @missing                              ; (%slot-id-set-missing instance id new-value)
  (set-nargs 3)
  (jump-function (@ '%slot-id-set-missing (% nfn))))


(defx86lapfunction %large-set-slot-id-value ((instance arg_x)
                                             (slot-id arg_y)
                                             (new-value arg_z))
  (movq (@ 'map (% nfn)) (% temp1))
  (svref slot-id slot-id.index imm1)
  (vector-length temp1 imm0)
  (rcmpq (% imm1) (% imm0))
  (movq (@ 'table (% nfn)) (% temp0))
  (ja @missing)
  (shrq ($ 1) (% rdx))
  (movl (@ x8664::misc-data-offset (% temp1) (% imm1)) (%l imm1))
  (testl (%l imm1) (%l imm1))
  (je @missing)
  (popq (% ra0))
  (push-reserved-frame)
  (pushq (@ 'class (% nfn)))
  (pushq (% ra0))
  (movq (@ x8664::misc-data-offset (% temp0) (% imm1) 8) (% arg_y))
  (set-nargs 4)
  (jump-function (@ '%maybe-std-setf-slot-value-using-class (% nfn)))
  @missing                              ; (%slot-id-set-missing instance id new-value)
  (set-nargs 3)
  (jump-function (@'%slot-id-ref-missing (% nfn))))


;;; All of the generic function trampoline functions have to be
;;; exactly the same size (x8664::gf-code-size) in words.  The
;;; largest of these - the general-case *GF-PROTO* - is currently
;;; "really" a little under 15 words, so X8664::GF-CODE-SIZE is
;;; just a little bigger than that.
(defparameter *gf-proto*
  (nfunction
   gag
   (lambda (&lap &lexpr args)
     (x86-lap-function 
      gag 
      ()
      (:fixed-constants (class-wrapper slots dispatch-table dcode hash))
      (:code-size x8664::gf-code-size)
      #+count-gf-calls
      (progn
        (lock)
        (addq ($ x8664::fixnumone) (@ 'hash (% nfn))))
      (movq (@ (% rsp)) (% ra0))
      ;; Make a LEXPR frame
      (save-frame-variable-arg-count)
      (push-argregs)
      (pushq (%q nargs))
      (movq (% rsp) (% arg_z))
      (ref-global.l ret1valaddr imm0)
      (cmpq (% ra0) (% imm0))
      (je @multiple)
      (ref-global.l lexpr-return1v ra0)
      (jmp @call)
      @multiple
      (pushq (@ (+ (target-nil-value) (x8664::%kernel-global 'lexpr-return))))
      (movq (% imm0) (% ra0))
      @call
      (push (% ra0))
      (movq (@ 'dispatch-table (% fn)) (% arg_y))
      (set-nargs 2)
      (jump-function (@ 'dcode (% fn))))))) ; dcode function

;;; is a winner - saves ~15%
(defx86lapfunction gag-one-arg ((arg arg_z))
  (:fixed-constants (class-wrapper slots dispatch-table dcode hash))
  (:code-size x8664::gf-code-size)
  #+count-gf-calls
  (progn
    (lock)
    (addq ($ x8664::fixnumone) (@ 'hash (% nfn))))
  (check-nargs 1)
  (movq (@ 'dispatch-table (% nfn)) (% arg_y))
  (set-nargs 2)
  (jump-function (@ 'dcode (% nfn))))

(defx86lapfunction gag-two-arg ((arg0 arg_y) (arg1 arg_z))
  (:fixed-constants (class-wrapper slots dispatch-table dcode hash))
  (:code-size x8664::gf-code-size)
  #+count-gf-calls
  (progn
    (lock)
    (addq ($ x8664::fixnumone) (@ 'hash (% nfn))))
  (check-nargs 2)
  (movq (@ 'dispatch-table (% nfn)) (% arg_x))
  (set-nargs 3)
  (jump-function (@ 'dcode (% nfn))))


(defx86lapfunction funcallable-trampoline ()
  (:fixed-constants (class-wrapper slots dispatch-table dcode hash))
  (:code-size x8664::gf-code-size)
  (jump-function (@ 'dcode (% nfn))))


;;; This is in LAP so that it can reference itself in the error message.
;;; (It needs to be cloned, so %fn will be unique to each copy.)
;;; It can't work for this to reference any of its own constants.
(defx86lapfunction unset-fin-trampoline ()
  (:code-size x8664::gf-code-size)
  (save-frame-variable-arg-count)
  (call-subprim .SPheap-rest-arg)
  (pop (% arg_z))
  (movq ($ '#.$XNOFINFUNCTION) (% arg_x))
  (movq (% fn) (% arg_y))
  (set-nargs 3)
  (call-subprim .SPksignalerr)
  ;(movq ($ (target-nil-value)) (% arg_z))
  (leave)
  (single-value-return))



(defparameter *cm-proto*
  (nfunction
   gag
   (lambda (&lap &lexpr args)
     (x86-lap-function 
      gag 
      ()
      (:fixed-constants (thing dcode gf bits))
      (movq (@ (% rsp)) (% ra0))
      (save-frame-variable-arg-count)
      (push-argregs)
      (pushq (%q nargs))
      (movq (% rsp) (% arg_z))
      (ref-global ret1valaddr imm0)
      (cmpq (% ra0) (% imm0))
      (je @multiple)
      (ref-global lexpr-return1v ra0)
      (jmp @call)
      @multiple
      (pushq (@ (+ (target-nil-value) (x8664::%kernel-global 'lexpr-return))))
      (movq (% imm0) (% ra0))
      @call
      (push (% ra0))
      (movq (@ 'thing (% fn)) (% arg_y))
      (set-nargs 2)
      (jump-function (@ 'dcode (% fn)))))))




) ; #+x8664-target
