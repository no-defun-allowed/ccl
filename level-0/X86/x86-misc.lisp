;;; -*- Mode: Lisp; Package: CCL -*-
;;;
;;; Copyright 1994-2009 Clozure Associates
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

;;; level-0;x86;x86-misc.lisp


(in-package "CCL")
#+x8664-target
(progn

;;; Copy N bytes from pointer src, starting at byte offset src-offset,
;;; to ivector dest, starting at offset dest-offset.
;;; It's fine to leave this in lap.
;;; Depending on alignment, it might make sense to move more than
;;; a byte at a time.
;;; Does no arg checking of any kind.  Really.

(defx86lapfunction %copy-ptr-to-ivector ((src (* 2 x8664::node-size) )
                                         (src-byte-offset (* 1 x8664::node-size))
                                         #|(ra 0)|#
                                         (dest arg_x)
                                         (dest-byte-offset arg_y)
                                         (nbytes arg_z))
  (let ((rsrc temp0)
        (rsrc-byte-offset temp1))
    (testq (% nbytes) (% nbytes))
    (movq (@ src-byte-offset (% rsp)) (% rsrc-byte-offset))         ; boxed src-byte-offset
    (movq (@ src (% rsp)) (% rsrc))     ; src macptr
    (jmp @test)
    @loop
    (unbox-fixnum rsrc-byte-offset imm0)
    (addq ($ '1) (% rsrc-byte-offset))
    (addq (@ x8664::macptr.address (% rsrc)) (% imm0))
    (movb (@ (% imm0)) (%b imm0))
    (unbox-fixnum dest-byte-offset imm1)
    (addq ($ '1) (% dest-byte-offset))
    (movb (%b imm0) (@ x8664::misc-data-offset (% dest) (% imm1)))
    (subq ($ '1) (% nbytes))
    @test
    (jne @loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))

(defx86lapfunction %copy-ivector-to-ptr ((src (* 2 x8664::node-size))
                                         (src-byte-offset (* 1 x8664::node-size))
                                         #|(ra 0)|#
                                         (dest arg_x)
                                         (dest-byte-offset arg_y)
                                         (nbytes arg_z))
  (let ((rsrc temp0)
        (rsrc-byte-offset imm0)
        (rdestptr imm1)
        (rdata imm2))
    (movq (@ src-byte-offset (% rsp)) (% rsrc-byte-offset))
    (sarq ($ x8664::word-shift) (% rsrc-byte-offset))
    (movq (% dest-byte-offset) (% rdestptr))
    (sarq ($ x8664::word-shift) (% rdestptr))
    (addq (@ target::macptr.address (% dest)) (% rdestptr))
    (movq (@ src (% rsp)) (% rsrc))
    (testq (% nbytes) (% nbytes))
    (jmp @test)
    @loop
    (movb (@ x8664::misc-data-offset (% rsrc) (% imm0)) (%b rdata))
    (addq ($ 1) (% rsrc-byte-offset))
    (movb (%b rdata) (@ (% rdestptr)))
    (addq ($ 1) (% rdestptr))
    (subq ($ '1) (% nbytes))
    @test
    (jne @loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))


(defun %copy-ivector-to-ivector (src src-byte-offset dest dest-byte-offset nbytes)
  (declare (fixnum src-byte-offset dest-byte-offset nbytes))
  (if (or (not (eq src dest))
          (< dest-byte-offset src-byte-offset)
          (>= dest-byte-offset (the fixnum (+ src-byte-offset nbytes))))
    (%copy-ivector-to-ivector-postincrement src src-byte-offset dest dest-byte-offset nbytes)
    (if (and (eq src dest)
             (eql src-byte-offset dest-byte-offset))
      dest
      (%copy-ivector-to-ivector-predecrement src
                                             (the fixnum (+ src-byte-offset nbytes))
                                             dest
                                             (the fixnum (+ dest-byte-offset nbytes))
                                             nbytes)))
  dest)

(defun %copy-ivector-to-ivector-postincrement (src src-byte-offset dest dest-byte-offset nbytes)
  (declare (fixnum src-byte-offset dest-byte-offset nbytes))
  
  (cond ((or (< nbytes 8)
             (not (= (logand src-byte-offset 3)
                     (logand dest-byte-offset 3))))
         (%copy-ivector-to-ivector-postincrement-8bit src src-byte-offset dest dest-byte-offset nbytes))
        ((= (logand src-byte-offset 7) (logand dest-byte-offset 7))
         (let* ((prefix-size (- 8 (logand src-byte-offset 7))))
           (declare (fixnum prefix-size))
           (unless (= 8 prefix-size)
             (%copy-ivector-to-ivector-postincrement-8bit src src-byte-offset dest dest-byte-offset prefix-size)
             (incf src-byte-offset prefix-size)
             (incf dest-byte-offset prefix-size)
             (decf nbytes prefix-size)))
         (let* ((tail-size (logand nbytes 7))
                (fullword-size (- nbytes tail-size)))
           (declare (fixnum tail-size fullword-size))
           (unless (zerop fullword-size)
             (%copy-ivector-to-ivector-postincrement-64bit src src-byte-offset dest dest-byte-offset fullword-size))
           (unless (zerop tail-size)
             (%copy-ivector-to-ivector-postincrement-8bit src (the fixnum (+ src-byte-offset fullword-size)) dest (the fixnum (+ dest-byte-offset fullword-size)) tail-size))))
        (t
         (let* ((prefix-size (- 4 (logand src-byte-offset 3))))
           (declare (fixnum prefix-size))
           (unless (= 4 prefix-size)
             (%copy-ivector-to-ivector-postincrement-8bit src src-byte-offset dest dest-byte-offset prefix-size)
             (incf src-byte-offset prefix-size)
             (incf dest-byte-offset prefix-size)
             (decf nbytes prefix-size)))
         (let* ((tail-size (logand nbytes 3))
                (fullword-size (- nbytes tail-size)))
           (declare (fixnum tail-size fullword-size))
           (unless (zerop fullword-size)
             (%copy-ivector-to-ivector-postincrement-32bit src src-byte-offset dest dest-byte-offset fullword-size))
           (unless (zerop tail-size)
             (%copy-ivector-to-ivector-postincrement-8bit src (the fixnum (+ src-byte-offset fullword-size)) dest (the fixnum (+ dest-byte-offset fullword-size)) tail-size))))))

(defun %copy-ivector-to-ivector-predecrement (src src-byte-offset dest dest-byte-offset nbytes)
  (declare (fixnum src-byte-offset dest-byte-offset nbytes))
  (cond ((or (< nbytes 8)
             (not (= (logand src-byte-offset 3)
                     (logand dest-byte-offset 3))))
         (%copy-ivector-to-ivector-predecrement-8bit src src-byte-offset dest dest-byte-offset nbytes))
	((= (logand src-byte-offset 7) (logand dest-byte-offset 7))
	 (let* ((suffix-size (logand src-byte-offset 7)))
	   (declare (fixnum suffix-size))
	   (unless (zerop suffix-size)
	     (%copy-ivector-to-ivector-predecrement-8bit src src-byte-offset dest dest-byte-offset suffix-size)
	     (decf src-byte-offset suffix-size)
	     (decf dest-byte-offset suffix-size)
	     (decf nbytes suffix-size)))
	 (let* ((head-size (logand nbytes 7))
		(fullword-size (- nbytes head-size)))
	   (declare (fixnum head-size fullword-size))
	   (unless (zerop fullword-size)
	     (%copy-ivector-to-ivector-predecrement-64bit src src-byte-offset dest dest-byte-offset fullword-size))
	   (unless (zerop head-size)
	     (%copy-ivector-to-ivector-predecrement-8bit src (the fixnum (- src-byte-offset fullword-size)) dest (the fixnum (- dest-byte-offset fullword-size)) head-size))))
	(t
	 (let* ((suffix-size (logand src-byte-offset 3)))
	   (declare (fixnum suffix-size))
	   (unless (zerop suffix-size)
	     (%copy-ivector-to-ivector-predecrement-8bit src src-byte-offset dest dest-byte-offset suffix-size)
	     (decf src-byte-offset suffix-size)
	     (decf dest-byte-offset suffix-size)
	     (decf nbytes suffix-size)))
	 (let* ((head-size (logand nbytes 3))
		(fullword-size (- nbytes head-size)))
	   (declare (fixnum head-size fullword-size))
	   (unless (zerop fullword-size)
	     (%copy-ivector-to-ivector-predecrement-32bit src src-byte-offset dest dest-byte-offset fullword-size))
	   (unless (zerop head-size)
	     (%copy-ivector-to-ivector-predecrement-8bit src (the fixnum (- src-byte-offset fullword-size)) dest (the fixnum (- dest-byte-offset fullword-size)) head-size))))))

(defx86lapfunction %copy-ivector-to-ivector-postincrement-8bit ((src 16) (src-byte-offset 8) #||(ra 0)||# (dest arg_x) (dest-byte-offset arg_y) (nbytes arg_z))
  (let ((rsrc temp0)
        (srcidx imm0)
        (destidx imm1)
        (data imm2))
    (movq (@ src (% rsp)) (% rsrc))
    (movq (@ src-byte-offset (% rsp)) (% srcidx))
    (sarq ($ target::fixnumshift) (% srcidx))
    (movq (% dest-byte-offset) (% destidx))
    (sarq ($ target::fixnumshift) (% destidx))
    (jmp @test)
    @loop
    (movzbl (@ target::misc-data-offset (% rsrc) (% srcidx)) (%l data))
    (movb (%b data) (@ target::misc-data-offset (% dest) (% destidx)))
    (lea (@ 1 (% destidx)) (% destidx))
    (lea (@ 1 (% srcidx)) (% srcidx))
    @test
    (subq ($ '1) (% nbytes))
    (jge @loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))



(defx86lapfunction %copy-ivector-to-ivector-predecrement-8bit ((src 16) (src-byte-offset 8) #||(ra 0)||# (dest arg_x) (dest-byte-offset arg_y) (nbytes arg_z))
  (let ((rsrc temp0)
        (srcidx imm0)
        (destidx imm1)
        (data imm2))
    (movq (@ src (% rsp)) (% rsrc))
    (movq (@ src-byte-offset (% rsp)) (% srcidx))
    (sarq ($ target::fixnumshift) (% srcidx))
    (movq (% dest-byte-offset) (% destidx))
    (sarq ($ target::fixnumshift) (% destidx))
    (jmp @test)
    @loop
    (lea (@ -1 (% destidx)) (% destidx))
    (lea (@ -1 (% srcidx)) (% srcidx))
    (movzbl (@ target::misc-data-offset (% rsrc) (% srcidx)) (%l data))
    (movb (%b data) (@ target::misc-data-offset (% dest) (% destidx)))
    @test
    (subq ($ '1) (% nbytes))
    (jge @loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))


(defx86lapfunction %copy-ivector-to-ivector-postincrement-32bit ((src 16) (src-byte-offset 8) #||(ra 0)||# (dest arg_x) (dest-byte-offset arg_y) (nbytes arg_z))
  (let ((rsrc temp0)
        (srcidx imm0)
        (destidx imm1)
        (data imm2))
    (movq (@ src (% rsp)) (% rsrc))
    (movq (@ src-byte-offset (% rsp)) (% srcidx))
    (sarq ($ target::fixnumshift) (% srcidx))
    (movq (% dest-byte-offset) (% destidx))
    (sarq ($ target::fixnumshift) (% destidx))
    (jmp @test)
    @loop
    (movl (@ target::misc-data-offset (% rsrc) (% srcidx)) (%l data))
    (movl (%l data) (@ target::misc-data-offset (% dest) (% destidx)))
    (lea (@ 4 (% destidx)) (% destidx))
    (lea (@ 4 (% srcidx)) (% srcidx))
    @test
    (subq ($ '4) (% nbytes))
    (jge @loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))

(defx86lapfunction %copy-ivector-to-ivector-predecrement-32bit ((src 16) (src-byte-offset 8) #||(ra 0)||# (dest arg_x) (dest-byte-offset arg_y) (nbytes arg_z))
  (let ((rsrc temp0)
        (srcidx imm0)
        (destidx imm1)
        (data imm2))
    (movq (@ src (% rsp)) (% rsrc))
    (movq (@ src-byte-offset (% rsp)) (% srcidx))
    (sarq ($ target::fixnumshift) (% srcidx))
    (movq (% dest-byte-offset) (% destidx))
    (sarq ($ target::fixnumshift) (% destidx))
    (jmp @test)
    @loop
    (lea (@ -4 (% destidx)) (% destidx))
    (lea (@ -4 (% srcidx)) (% srcidx))
    (movl (@ target::misc-data-offset (% rsrc) (% srcidx)) (%l data))
    (movl (%l data) (@ target::misc-data-offset (% dest) (% destidx)))
    @test
    (subq ($ '4) (% nbytes))
    (jge @loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))

(defx86lapfunction %copy-ivector-to-ivector-postincrement-64bit ((src 16) (src-byte-offset 8) #||(ra 0)||# (dest arg_x) (dest-byte-offset arg_y) (nbytes arg_z))
  (let ((rsrc temp0)
        (srcidx temp1)
        (destidx dest-byte-offset)
        (data0 imm0)
        (data1 imm1))
    (movq (@ src (% rsp)) (% rsrc))
    (movq (@ src-byte-offset (% rsp)) (% srcidx))
    ;; srcidx and destidx are multiples of 8, so it's safe to right-shift
    ;; them here (they remain fixnums).
    (sarq ($ target::word-shift) (% srcidx))
    (sarq ($ target::word-shift) (% destidx))
    (testq ($ '8) (% nbytes))
    (jz @test)
    (movq (@ target::misc-data-offset (% rsrc) (% srcidx)) (% data0))
    (movq (% data0) (@ target::misc-data-offset (% dest) (% destidx)))
    (lea (@ 8 (% destidx)) (% destidx))
    (lea (@ 8 (% srcidx)) (% srcidx))
    (subq ($ '8) (% nbytes))    
    (jmp @test)
    @loop
    (movq (@ target::misc-data-offset (% rsrc) (% srcidx)) (% data0))
    (movq (@ (+ 8 target::misc-data-offset) (% rsrc) (% srcidx)) (% data1))
    (movq (% data0) (@ target::misc-data-offset (% dest) (% destidx)))
    (movq (% data1) (@ (+ 8 target::misc-data-offset) (% dest) (% destidx)))
    (lea (@ 16 (% destidx)) (% destidx))
    (lea (@ 16 (% srcidx)) (% srcidx))
    @test
    (subq ($ '16) (% nbytes))
    (jge @loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))

(defx86lapfunction %copy-ivector-to-ivector-predecrement-64bit ((src 16) (src-byte-offset 8) #||(ra 0)||# (dest arg_x) (dest-byte-offset arg_y) (nbytes arg_z))
  (let ((rsrc temp0)
        (srcidx temp1)
        (destidx dest-byte-offset)
        (data0 imm0)
        (data1 imm1))
    (movq (@ src (% rsp)) (% rsrc))
    (movq (@ src-byte-offset (% rsp)) (% srcidx))
    ;; srcidx and destidx are multiples of 8, so it's safe to right-shift
    ;; them here (they remain fixnums).
    (sarq ($ target::word-shift) (% srcidx))
    (sarq ($ target::word-shift) (% destidx))
    (testq ($ '8) (% nbytes))
    (jz @test)
    (lea (@ -8 (% destidx)) (% destidx))
    (lea (@ -8 (% srcidx)) (% srcidx))
    (movq (@ target::misc-data-offset (% rsrc) (% srcidx)) (% data0))
    (movq (% data0) (@ target::misc-data-offset (% dest) (% destidx)))
    (subq ($ '8) (% nbytes))    
    (jmp @test)
    @loop
    (lea (@ -16 (% destidx)) (% destidx))
    (lea (@ -16 (% srcidx)) (% srcidx))
    (movq (@ target::misc-data-offset (% rsrc) (% srcidx)) (% data0))
    (movq (@ (+ 8 target::misc-data-offset) (% rsrc) (% srcidx)) (% data1))
    (movq (% data0) (@ target::misc-data-offset (% dest) (% destidx)))
    (movq (% data1) (@ (+ 8 target::misc-data-offset) (% dest) (% destidx)))
    @test
    (subq ($ '16) (% nbytes))
    (jge @loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))

(defx86lapfunction %copy-gvector-to-gvector ((src (* 2 x8664::node-size))
					     (src-element (* 1 x8664::node-size))
                                             #|(ra 0)|#
					     (dest arg_x)
					     (dest-element arg_y)
					     (nelements arg_z))
  (let ((rsrc temp0)
        (rsrc-element imm1)
        (val temp1))
    (movq (@ src-element (% rsp)) (% rsrc-element))
    (movq (@ src (% rsp)) (% rsrc))
    (cmpq (% rsrc) (% dest))
    (jne @front)
    (rcmp (% rsrc-element) (% dest-element))
    (jl @back)
    @front
    (testq (% nelements) (% nelements))
    (jmp @front-test)
    @front-loop
    (movq (@ x8664::misc-data-offset (% rsrc) (% rsrc-element)) (% val))
    (addq ($ '1) (% rsrc-element))
    (movq (% val) (@ x8664::misc-data-offset (% dest) (% dest-element)))
    (addq ($ '1) (% dest-element))
    (subq ($ '1) (% nelements))
    @front-test
    (jne @front-loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)
    @back
    (addq (% nelements) (% rsrc-element))
    (addq (% nelements) (% dest-element))
    (testq (% nelements) (% nelements))
    (jmp @back-test)
    @back-loop
    (subq ($ '1) (% rsrc-element))
    (movq (@ x8664::misc-data-offset (% rsrc) (% rsrc-element)) (% val))
    (subq ($ '1) (% dest-element))
    (movq (% val) (@ x8664::misc-data-offset (% dest) (% dest-element)))
    (subq ($ '1) (% nelements))
    @back-test
    (jne @back-loop)
    (movq (% dest) (% arg_z))
    (single-value-return 4)))

(defx86lapfunction %heap-bytes-allocated ()
  (movq (:rcontext x8664::tcr.save-allocptr) (% temp1))
  (movq (:rcontext x8664::tcr.last-allocptr) (% temp0))
  (cmpq ($ -16) (% temp1))
  (movq (:rcontext x8664::tcr.total-bytes-allocated) (% imm0))
  (jz @go)
  (movq (% temp0) (% temp2))
  (subq (% temp1) (% temp0))
  (testq (% temp2) (% temp2))
  (jz @go)
  (add (% temp0) (% imm0))
  @go
  (jmp-subprim .SPmakeu64))


(defx86lapfunction values ()
  (:arglist (&rest values))
  (save-frame-variable-arg-count)
  (push-argregs)
  (jmp-subprim .SPnvalret))

(defx86lapfunction rdtsc ()
  (:byte #x0f)                          ;two-byte rdtsc opcode
  (:byte #x31)                          ;is #x0f #x31
  (shlq ($ 32) (% rdx))
  (orq (% rdx) (% rax))
  (imul ($ (* 2 target::node-size)) (% rax) (% arg_z))
  (shrq ($ 1) (% arg_z))
  (single-value-return))

(defx86lapfunction rdtscp ()
  (:byte #x0f)                          ;three-byte rdtscp opcode
  (:byte #x01)                         ;is #x0f #x01 xf9
  (:byte #xf9)
  (shlq ($ 32) (% rdx))
  (orq (% rdx) (% rax))
  (imul ($ (* 2 target::node-size)) (% rax) (% arg_z))
  (shrq ($ 1) (% arg_z))
  (shlq ($ target::fixnumshift) (% rcx))
  (push (% arg_z))
  (push (% rcx))
  (set-nargs 2)
  (lea (@ '2 (% rsp)) (% temp0))
  (jmp-subprim .SPvalues))

;;; Return all 64 bits of the time-stamp counter as an unsigned integer.
(defx86lapfunction rdtsc64 ()
  (:byte #x0f)                          ;two-byte rdtsc opcode
  (:byte #x31)                          ;is #x0f #x31
  (shlq ($ 32) (% rdx))
  (orq (% rdx) (% rax))
  (jmp-subprim .SPmakeu64))

;;; It would be nice if (%setf-macptr macptr (ash (the fixnum value)
;;; ash::fixnumshift)) would do this inline.

(defx86lapfunction %setf-macptr-to-object ((macptr arg_y) (object arg_z))
  (check-nargs 2)
  (trap-unless-typecode= macptr x8664::subtag-macptr)
  (movq (% object) (@ x8664::macptr.address (% macptr)))
  (single-value-return))

(defx86lapfunction %fixnum-from-macptr ((macptr arg_z))
  (check-nargs 1)
  (trap-unless-typecode= arg_z x8664::subtag-macptr)
  (movq (@ x8664::macptr.address (% arg_z)) (% imm0))
  (trap-unless-lisptag= imm0 x8664::tag-fixnum imm1)
  (movq (% imm0) (% arg_z))
  (single-value-return))


(defx86lapfunction %%get-unsigned-longlong ((ptr arg_y) (offset arg_z))
  (trap-unless-typecode= ptr x8664::subtag-macptr)
  (macptr-ptr ptr imm1)
  (unbox-fixnum offset imm0)
  (movq (@ (% imm1) (% imm0)) (% imm0))
  (jmp-subprim .SPmakeu64))


(defx86lapfunction %%get-signed-longlong ((ptr arg_y) (offset arg_z))
  (trap-unless-typecode= ptr x8664::subtag-macptr)
  (macptr-ptr ptr imm1)
  (unbox-fixnum offset imm0)
  (movq (@ (% imm1) (% imm0)) (% imm0))
  (jmp-subprim .SPmakes64))




(defx86lapfunction %%set-unsigned-longlong ((ptr arg_x)
                                            (offset arg_y)
                                            (val arg_z))
  (save-simple-frame)
  (trap-unless-typecode= ptr x8664::subtag-macptr)
  (call-subprim .SPgetu64)
  (macptr-ptr ptr imm2)
  (unbox-fixnum offset imm1)
  (movq (% imm0) (@ (% imm2) (% imm1)))
  (restore-simple-frame)
  (single-value-return))


(defx86lapfunction %%set-signed-longlong ((ptr arg_x)
                                          (offset arg_y)
                                          (val arg_z))
  (save-simple-frame)
  (trap-unless-typecode= ptr x8664::subtag-macptr)
  (call-subprim .SPgets64)
  (macptr-ptr ptr imm2)
  (unbox-fixnum offset imm1)
  (movq (% imm0) (@ (% imm2) (% imm1)))
  (restore-simple-frame)
  (single-value-return))

(defx86lapfunction interrupt-level ()
  (movq (:rcontext x8664::tcr.tlb-pointer) (% imm1))
  (movq (@ x8664::interrupt-level-binding-index (% imm1)) (% arg_z))
  (single-value-return))

(defx86lapfunction set-interrupt-level ((new arg_z))
  (movq (:rcontext x8664::tcr.tlb-pointer) (% imm1))
  (trap-unless-fixnum new)
  (movq (% new) (@ x8664::interrupt-level-binding-index (% imm1)))
  (single-value-return))

(defx86lapfunction %current-tcr ()
  (movq (:rcontext x8664::tcr.linear) (% arg_z))
  (single-value-return))

(defx86lapfunction %tcr-toplevel-function ((tcr arg_z))
  (check-nargs 1)
  (cmpq (% tcr) (:rcontext x8664::tcr.linear))
  (movq (% rsp) (% imm0))
  (movq (@ x8664::tcr.vs-area (% tcr)) (% temp0))
  (movq (@ x8664::area.high (% temp0)) (% imm1))
  (jz @room)
  (movq (@ x8664::area.active (% temp0)) (% imm0))
  @room
  (cmpq (% imm1) (% imm0))
  (movl ($ (target-nil-value)) (%l arg_z))
  (cmovneq (@ (- x8664::node-size) (% imm1)) (% arg_z))
  (single-value-return))

(defx86lapfunction %set-tcr-toplevel-function ((tcr arg_y) (fun arg_z))
  (check-nargs 2)
  (cmpq (% tcr) (:rcontext x8664::tcr.linear))
  (movq (% rsp) (% imm0))
  (movq (@ x8664::tcr.vs-area (% tcr)) (% temp0))
  (movq (@ x8664::area.high (% temp0)) (% imm1))
  (jz @room)
  (movq (@ x8664::area.active (% temp0)) (% imm0))
  @room
  (cmpq (% imm1) (% imm0))
  (leaq (@ (- x8664::node-size) (% imm1)) (% imm1))
  (movq ($ 0) (@ (% imm1)))
  (jne @have-room)
  (movq (% imm1) (@ x8664::area.active (% temp0)))
  (movq (% imm1) (@ x8664::tcr.save-vsp (% tcr)))
  @have-room
  (movq (% fun) (@ (% imm1)))
  (single-value-return))

;;; This needs to be done out-of-line, to handle EGC memoization.
(defx86lapfunction %store-node-conditional ((offset 8) #|(ra 0)|# (object arg_x) (old arg_y) (new arg_z))
  (movq (@ offset (% rsp)) (% temp0))
  (save-simple-frame)
  (call-subprim .SPstore-node-conditional)
  (restore-simple-frame)
  (single-value-return 3))

(defx86lapfunction %store-immediate-conditional ((offset 8) #|(ra 0)|# (object arg_x) (old arg_y) (new arg_z))
  (movq (@ offset (% rsp)) (% temp0))
  (unbox-fixnum temp0 imm1)
  (movq (% old) (% rax))
  (lock)
  (cmpxchgq (% new) (@ (% object) (% imm1)))
  (jne @lose)
  (movl ($ (target-t-value)) (%l arg_z))
  (single-value-return 3)
  @lose
  (movl ($ (target-nil-value)) (%l arg_z))
  (single-value-return 3))

;;; AFAICT, this is GC-safe
(defx86lapfunction set-%gcable-macptrs% ((ptr x8664::arg_z))
  @again
  (movq (@ (+ (target-nil-value) (x8664::kernel-global gcable-pointers)))
        (% rax))
  (movq (% rax) (@ x8664::xmacptr.link (% ptr)))
  (lock)
  (cmpxchgq (% ptr) (@ (+ (target-nil-value) (x8664::kernel-global gcable-pointers))))
  (jne @again)
  (single-value-return))

#||
(defun set-%gcable-macptrs% (ptr)
  (with-exception-lock
      (%set-%gcable-macptrs% ptr)))

(defx86lapfunction %set-%gcable-macptrs% ((ptr x8664::arg_z))
  ;; We must own the exception lock here.
  (movq (@ (+ (target-nil-value) (x8664::kernel-global gcable-pointers)))
        (% temp0))
  (movq (% temp0) (@ x8664::xmacptr.link (% ptr)))
  (movq (% ptr) (@ (+ (target-nil-value) (x8664::kernel-global gcable-pointers))))
  (single-value-return))

||#

;;; Atomically increment or decrement the gc-inhibit-count kernel-global
;;; (It's decremented if it's currently negative, incremented otherwise.)
(defx86lapfunction %lock-gc-lock ()
  @again
  (movq (@ (+ (target-nil-value) (x8664::kernel-global gc-inhibit-count))) (% rax))
  (lea (@ '-1 (% rax)) (% temp0))
  (lea (@ '1 (% rax)) (% arg_z))
  (testq (% rax) (% rax))
  (cmovsq (% temp0) (% arg_z))
  (lock)
  (cmpxchgq (% arg_z) (@ (+ (target-nil-value) (x8664::kernel-global gc-inhibit-count))))
  (jz @win)
  (pause)
  (jmp @again)
  @win
  (single-value-return))

;;; Atomically decrement or increment the gc-inhibit-count kernel-global
;;; (It's incremented if it's currently negative, decremented otherwise.)
;;; If it's incremented from -1 to 0, try to GC (maybe just a little.)
(defx86lapfunction %unlock-gc-lock ()
  @again
  (movq (@ (+ (target-nil-value) (x8664::kernel-global gc-inhibit-count)))
        (% rax))
  (lea (@ '1 (% rax)) (% arg_x))
  (cmpq ($ -1) (% rax))
  (lea (@ '-1 (% rax)) (% arg_z))
  (cmovleq (% arg_x) (% arg_z))
  (lock)
  (cmpxchgq (% arg_z) (@ (+ (target-nil-value) (x8664::kernel-global gc-inhibit-count))))
  (je @win)
  (pause)
  (jmp @again)
  @win
  (cmpq ($ '-1) (% rax))
  (jne @done)
  ;; The GC tried to run while it was inhibited.  Unless something else
  ;; has just inhibited it, it should be possible to GC now.
  (mov ($ arch::gc-trap-function-immediate-gc) (% imm0))
  (uuo-gc-trap)
  @done
  (single-value-return))

;;; Return true iff we were able to increment a non-negative
;;; lock._value

(defx86lapfunction %atomic-incf-node ((by arg_x) (node arg_y) (disp arg_z))
  (check-nargs 3)
  (unbox-fixnum disp imm1)
  @again
  (movq (@ (% node) (% imm1)) (% rax))
  (lea (@ (% rax) (% by)) (% arg_z))
  (lock)
  (cmpxchgq (% arg_z) (@ (% node) (% imm1)))
  (je @win)
  (pause)
  (jmp @again)
  @win
  (single-value-return))

(defx86lapfunction %atomic-incf-ptr ((ptr arg_z))
  (macptr-ptr ptr imm2)
  @again
  (movq (@ (% imm2)) (% rax))
  (lea (@ 1 (% rax)) (% imm1))
  (lock)
  (cmpxchgq (% imm1) (@ (% imm2)))
  (je @win)
  (pause)
  (jmp @again)
  @win
  (box-fixnum imm1 arg_z)
  (single-value-return))

(defx86lapfunction %atomic-incf-ptr-by ((ptr arg_y) (by arg_z))
  (macptr-ptr ptr imm2)
  @again
  (movq (@ (% imm2)) (% rax))
  (unbox-fixnum by imm1)
  (add (% rax) (% imm1))
  (lock)
  (cmpxchgq (% imm1) (@ (% imm2)))
  (jz @win)
  (pause)
  (jmp @again)
  @win
  (box-fixnum imm1 arg_z)
  (single-value-return))


(defx86lapfunction %atomic-decf-ptr ((ptr arg_z))
  (macptr-ptr ptr imm2)
  @again
  (movq (@ (% imm2)) (% rax))
  (lea (@ -1 (% rax)) (% imm1))
  (lock)
  (cmpxchgq (% imm1) (@ (% imm2)))
  (jz @win)
  (pause)
  (jmp @again)
  @win
  (box-fixnum imm1 arg_z)
  (single-value-return))

(defx86lapfunction %atomic-decf-ptr-if-positive ((ptr arg_z))
  (macptr-ptr ptr imm2)
  @again
  (movq (@ (% imm2)) (% rax))
  (testq (% rax) (% rax))
  (lea (@ -1 (% rax)) (% imm1))
  (jz @done)
  (lock)
  (cmpxchgq (% imm1) (@ (% imm2)))
  (jz @done)
  (pause)
  (jmp @again)
  @done
  (box-fixnum imm1 arg_z)
  (single-value-return))


(defx86lapfunction %atomic-swap-ptr ((ptr arg_y) (newval arg_z))
  (macptr-ptr arg_y imm1)
  (unbox-fixnum newval imm0)
  (lock)
  (xchgq (% imm0) (@ (% imm1)))
  (box-fixnum imm0 arg_z)
  (single-value-return))

;;; Try to store the fixnum NEWVAL at PTR, if and only if the old value
;;; was equal to OLDVAL.  Return the old value
(defx86lapfunction %ptr-store-conditional ((ptr arg_x) (expected-oldval arg_y) (newval arg_z))
  (macptr-ptr ptr imm2)
  (unbox-fixnum expected-oldval imm0)
  (lock)
  (cmpxchgq (% imm1) (@ (% imm2)))
  (box-fixnum imm0 arg_z)
  (single-value-return))

(defx86lapfunction %ptr-store-fixnum-conditional ((ptr arg_x) (expected-oldval arg_y) (newval arg_z))
  (let ((address imm1))
    (macptr-ptr ptr address)
    (movq (% expected-oldval) (% imm0))
    (lock)
    (cmpxchgq (% newval) (@ (% address)))
    (movq (% imm0) (% arg_z))
    (single-value-return)))

(defx86lapfunction xchgl ((newval arg_y) (ptr arg_z))
  (unbox-fixnum newval imm0)
  (macptr-ptr ptr imm1)
  (lock)                                ; implicit ?
  (xchgl (% imm0.l) (@ (% imm1)))
  (box-fixnum imm0 arg_z)
  (single-value-return))
  
                          


(defx86lapfunction %macptr->dead-macptr ((macptr arg_z))
  (check-nargs 1)
  (movb ($ x8664::subtag-dead-macptr) (@ x8664::misc-subtag-offset (% macptr)))
  (single-value-return))




  
(defx86lapfunction %%save-application ((flags arg_y) (fd arg_z))
  (unbox-fixnum flags imm0)
  (orq ($ arch::gc-trap-function-save-application) (% imm0))
  (unbox-fixnum fd imm1)
  (uuo-gc-trap)
  (single-value-return))



(defx86lapfunction %misc-address-fixnum ((misc-object arg_z))
  (check-nargs 1)
  (lea (@ x8664::misc-data-offset (% misc-object)) (% arg_z))
  (single-value-return))


(defx86lapfunction fudge-heap-pointer ((ptr arg_x) (subtype arg_y) (len arg_z))
  (check-nargs 3)
  (macptr-ptr ptr imm1) ; address in macptr
  (lea (@ 17 (% imm1)) (% imm0))     ; 2 for delta + 15 for alignment
  (andb ($ -16) (%b  imm0))   ; Clear low four bits to align
  (subq (% imm0) (% imm1))  ; imm1 = -delta
  (negw (%w imm1))
  (movw (%w imm1) (@  -2 (% imm0)))     ; save delta halfword
  (unbox-fixnum subtype imm1)  ; subtype at low end of imm1
  (shlq ($ (- x8664::num-subtag-bits x8664::fixnum-shift)) (% len ))
  (orq (% len) (% imm1))
  (movq (% imm1) (@ (% imm0)))       ; store subtype & length
  (lea (@ x8664::fulltag-misc (% imm0)) (% arg_z)) ; tag it, return it
  (single-value-return))

(defx86lapfunction %%make-disposable ((ptr arg_y) (vector arg_z))
  (check-nargs 2)
  (lea (@ (- x8664::fulltag-misc) (% vector)) (% imm0)) ; imm0 is addr = vect less tag
  (movzwq (@ -2 (% imm0)) (% imm1))     ; get delta
  (subq (% imm1) (% imm0))              ; vector addr (less tag)  - delta is orig addr
  (movq (% imm0) (@ x8664::macptr.address (% ptr)))
  (single-value-return))


(defx86lapfunction %vect-data-to-macptr ((vect arg_y) (ptr arg_z))
  (lea (@ x8664::misc-data-offset (% vect)) (% imm0))
  (movq (% imm0) (@ x8664::macptr.address (% ptr)))
  (single-value-return))

(defx86lapfunction %ivector-from-macptr ((ptr arg_z))
  (macptr-ptr ptr imm0)
  (lea (@ (- target::fulltag-misc target::node-size) (% imm0)) (% arg_z))
  (single-value-return))

(defun get-saved-register-values ()
  (values))


(defx86lapfunction %current-db-link ()
  (movq (:rcontext x8664::tcr.db-link) (% arg_z))
  (single-value-return))

(defx86lapfunction %no-thread-local-binding-marker ()
  (movq ($ x8664::subtag-no-thread-local-binding) (% arg_z))
  (single-value-return))


(defx86lapfunction pending-user-interrupt ()
  (xorq (% imm0) (% imm0))
  (ref-global x8664::intflag arg_z)
  ;; If another signal happens now, it will get ignored, same as if it happened
  ;; before whatever signal is in arg_z.  But then these are async signals, so
  ;; who can be sure it didn't actually happen just before...
  (set-global imm0 x8664::intflag)
  (single-value-return))


(defx86lapfunction debug-trap-with-string ((arg arg_z))
  (check-nargs 1)
  (uuo-error-debug-trap-with-string)
  (single-value-return))

(defx86lapfunction %safe-get-ptr ((src arg_y) (dest arg_z))
  (check-nargs 2)
  (save-simple-frame)
  (macptr-ptr src imm0)
  (leaq (@ (:^ @done) (% rip)) (% ra0))
  (movq (% imm0) (:rcontext x8664::tcr.safe-ref-address))
  (movq (@ (% imm0)) (% imm0))
  @done
  (movq ($ 0) (:rcontext x8664::tcr.safe-ref-address))
  (movq (% imm0) (@ x8664::macptr.address (% dest)))
  (restore-simple-frame)
  (single-value-return))

;;; This was intentded to work around a bug in #_nanosleep in early
;;; Leopard test releases.  It's probably not necessary any more; is
;;; it still called ?

(defx86lapfunction %check-deferred-gc ()
  (btq ($ (+ arch::tcr-flag-bit-pending-suspend target::fixnumshift)) (:rcontext x8664::tcr.flags))
  (movl ($ (target-nil-value)) (% arg_z.l))
  (jae @done)
  (ud2a)
  (:byte 3)
  (movl ($ (target-t-value)) (% arg_z.l))
  @done
  (single-value-return))

(defx86lapfunction %%tcr-interrupt ((target arg_z))
  (check-nargs 1)
  (ud2a)
  (:byte 4)
  (box-fixnum imm0 arg_z)
  (single-value-return))

(defx86lapfunction %suspend-tcr ((target arg_z))
  (check-nargs 1)
  (ud2a)
  (:byte 5)
  (movzbl (%b imm0) (%l imm0))
  (testl (%l imm0) (%l imm0))
  (movl ($ (target-nil-value)) (%l arg_z))
  (cmovnel (@ (+ target::t-offset target::symbol.vcell) (% arg_z)) (%l arg_z))
  (single-value-return))

(defx86lapfunction %suspend-other-threads ()
  (check-nargs 0)
  (ud2a)
  (:byte 6)
  (movl ($ (target-nil-value)) (%l arg_z))
  (single-value-return))

(defx86lapfunction %resume-tcr ((target arg_z))
  (check-nargs 1)
  (ud2a)
  (:byte 7)
  (movzbl (%b imm0) (%l imm0))
  (testl (%l imm0) (%l imm0))
  (movl ($ (target-nil-value)) (%l arg_z))
  (cmovnel (@ (+ target::t-offset target::symbol.vcell) (% arg_z)) (%l arg_z))
  (single-value-return))

(defx86lapfunction %resume-other-threads ()
  (check-nargs 0)
  (ud2a)
  (:byte 8)
  (movl ($ (target-nil-value)) (%l arg_z))
  (single-value-return))

(defx86lapfunction %kill-tcr ((target arg_z))
  (check-nargs 1)
  (ud2a)
  (:byte 9)
  (testb (%b imm0) (%b imm0))
  (movl ($ (target-nil-value)) (%l arg_z))
  (cmovnel (@ (+ target::t-offset target::symbol.vcell) (% arg_z)) (%l arg_z))
  (single-value-return))
  

(defx86lapfunction %get-spin-lock ((p arg_z))
  (check-nargs 1)
  (save-simple-frame)
  @again
  (macptr-ptr arg_z imm1)
  (movq (@ '*spin-lock-tries* (% fn)) (% temp0))
  (movq (@ '*spin-lock-timeouts* (% fn)) (% temp1))
  (movq (@ target::symbol.vcell (% temp0)) (% temp0))
  (movq (:rcontext x8664::tcr.linear) (% arg_y))
  @try-swap
  (xorq (% rax) (% rax))
  (lock)
  (cmpxchgq (% arg_y) (@ (% imm1)))
  (je @done)
  @spin
  (pause)
  (cmpq ($ 0) (@ (% imm1)))
  (je @try-swap)
  (subq ($ '1) (% temp0))
  (jne @spin)
  @wait
  (addq ($ x8664::fixnumone) (@ x8664::symbol.vcell (% temp1)))
  (pushq (% arg_z))
  (call-symbol yield 0)
  (popq (% arg_z))
  (jmp @again)
  @done
  (restore-simple-frame)
  (single-value-return))

;;; This is a prototype; it can't easily keep its arguments on the stack,
;;; or in registers, because its job involves unwinding the stack and
;;; restoring registers.  Its parameters are thus kept in constants,
;;; and this protoype is cloned (with the right parameters).

;;; For win64 (which doesn't really have a "save3" register), the code
;;; which instantiates this should always set save3-offset to 0.

  




;;; If x is a static cons, return its index value as a fixnum.
;;; Otherwise return nil.
(defx86lapfunction %staticp ((x arg_z))
  (check-nargs 1)
  (ref-global static-cons-area temp0)
  (movq (% x) (% imm0))
  (movl ($ (target-nil-value)) (% arg_z.l))
  (subq (@ target::area.low (% temp0)) (% imm0))
  (shrq ($ target::dnode-shift) (% imm0))
  (movq (@ target::area.ndnodes (% temp0)) (% imm1))
  (subq (% imm0) (% imm1))
  (lea (@ 128 (% imm1)) (% imm1))
  (leaq (@ (% imm1) target::fixnumone) (% imm1))
  (cmovaq (% imm1) (% arg_z))
  (single-value-return))

;;; Return the static cons corresponding to the index n,
;;; or nil if there's no such static cons (i.e., n is out
;;; of range, or the static cons has been gc'd).
(defx86lapfunction %static-inverse-cons ((n arg_z))
  (check-nargs 1)
  (testl ($ target::tagmask) (% arg_z.l))
  (jne @fail)
  (subq ($ '128) (% arg_z))
  (ref-global static-cons-area temp0)
  (movq (@ target::area.ndnodes (% temp0)) (% imm0))
  (box-fixnum imm0 arg_y)
  (rcmpq (% arg_z) (% arg_y))
  (ja @fail)
  (movq (@ target::area.high (% temp0)) (% imm0))
  (subq (% arg_z) (% imm0))
  (subq (% arg_z) (% imm0))
  (lea (@ x8664::fulltag-cons (% imm0)) (% arg_z))
  (cmpb ($ target::unbound-marker) (@ target::cons.car (% arg_z)))
  (je @fail)
  (single-value-return)
  @fail
  (movl ($ (target-nil-value)) (% arg_z.l))
  (single-value-return))


  

;;; end of x86-misc.lisp
) ; #+x8664-target
