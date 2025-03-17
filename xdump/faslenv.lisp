;;;-*- Mode: Lisp; Package: CCL -*-
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


(in-package "CCL")

;; Compile-time environment for fasl dumper/loader.

; loader state istruct
(def-accessors (faslstate) %svref
  ()
  faslstate.faslfname
  faslstate.faslevec
  faslstate.faslecnt
  faslstate.faslfd
  faslstate.faslval
  faslstate.faslstr
  faslstate.oldfaslstr
  faslstate.faslerr
  faslstate.iobuffer
  faslstate.bufcount
  faslstate.faslversion
  faslstate.faslepush
  faslstate.faslgsymbols
  faslstate.fasldispatch)


(defconstant numfaslops 80 "Number of fasl file opcodes, roughly")
(defconstant $fasl-epush-bit 7)
(defconstant $fasl-file-id #xff00)
(defconstant $fasl-file-id1 #xff01)
(defconstant $faslend #xff)
(defconstant $fasl-buf-len 2048)
(defmacro deffaslop (n arglist &body body)
  `(setf (svref *fasl-dispatch-table* ,n)
         (nfunction ,n (lambda ,arglist ,@body))))

(defvar *fasl-op-names*
  (make-array 256 :initial-element "???"))

(macrolet ((def (name val)
             `(progn
                (defconstant ,name ,val)
                (setf (aref *fasl-op-names* ,val) ,(subseq (string-capitalize name) 6)))))
(def $fasl-noop 0)              ;<nada:zilch>.  
(def $fasl-s32-vector 1)        ;<count> Make a (SIMPLE-ARRAY (SIGNED-BYTE 32) <count>)
(def $fasl-code-vector 2)       ;<count> words of code
(def $fasl-clfun 3)             ;<size:count><codesize:count>code,size-codesize exprs
(def $fasl-lfuncall 4)          ;<lfun:expr> funcall the lfun.
(def $fasl-globals 5)           ;<expr> global symbols vector
(def $fasl-char 6)              ;<char:byte> Make a char
(def $fasl-fixnum 7)            ;<value:long> Make a (4-byte) fixnum
(def $fasl-dfloat 8)            ;<hi:long><lo:long> Make a DOUBLE-FLOAT
(def $fasl-bignum32 9)          ;<count> make a bignum with count digits
(def $fasl-word-fixnum 10)      ;<value:word> Make a fixnum
(def $fasl-double-float-vector 11) ;<count> make a (SIMPLE-ARRAY DOUBLE-FLOAT <count>)
(def $fasl-single-float-vector 12) ;<count> make a (SIMPLE-ARRAY SINGLE-FLOAT <count>)
(def $fasl-bit-vector 13)       ;<count> make a (SIMPLE-ARRAY BIT <count>)
(def $fasl-u8-vector 14)        ;<count> make a (SIMPLE-ARRAY (UNSIGNED-BYTE 8) <count>)
(def $fasl-cons 15)             ;<car:expr><cdr:expr> Make a cons
(def $fasl-s8-vector 16)        ;<count> make a (SIMPLE-ARRAY (SIGNED-BYTE 8) <count>)
(def $fasl-t-vector 17)         ;<count> make a (SIMPLE-ARRAY T <count>)
(def $fasl-nil 18)              ; Make nil
(def $fasl-timm 19)             ;<n:long>
(def $fasl-function 20)         ;<count> Make function
(def $fasl-vstr 21)             ;<vstring> Make a string
(def $fasl-vmksym 22)           ;<vstring> Make an uninterned symbol
(def $fasl-platform 23)         ;<n:byte> Ensure that file's loadable on platform n.
(def $fasl-vetab-alloc 24)      ;<count:count> Make a new expression table
                                        ; with count slots.  Current etab gets lost.
(def $fasl-veref 25)            ;<index:count> Get the value from an etab slot.
(def $fasl-fixnum8 26)          ;<high:long><low:long> Make an 8-byte fixnum.
(def $fasl-symfn 27)            ;<sym:expr> 
(def $fasl-eval 28)             ;<expr> Eval <expr> and return value.
(def $fasl-u16-vector 29)       ;<count> Make a (SIMPLE-ARRAY (UNSIGNED-BYTE 16) <count>)
(def $fasl-s16-vector 30)       ;<count> Make a (SIMPLE-ARRAY (SIGNED-BYTE 16) <count>)
(def $fasl-vintern 31)          ;<vstring> Intern in current pkg.
(def $fasl-vpkg-intern 32)      ;<pkg:expr><vstring> Make a sym in pkg.
(def $fasl-vpkg 33)             ;<vstring> Returns the package of given name
(def $fasl-vgvec 34)            ;<subtype:byte><n:count><n exprs>
(def $fasl-defun 35)            ;<fn:expr><doc:expr>
(def $fasl-macro 37)            ;<fn:expr><doc:expr>
(def $fasl-defconstant 38)      ;<sym:expr><val:expr><doc:expr>
(def $fasl-defparameter 39)     ;<sym:expr><val:expr><doc:expr>
(def $fasl-defvar 40)           ;<sym:expr>
(def $fasl-defvar-init 41)      ;<sym:expr><val:expr><doc:expr>
(def $fasl-vivec 42)            ;<subtype:byte><n:count><n data bytes>
(def $fasl-prog1 43)            ;<expr><expr> - Second <expr> is for side-affects only
(def $fasl-vlist 44)            ;<n:count> <data: n+1 exprs> Make a list
(def $fasl-vlist* 45)           ;<n:count> <data:n+2 exprs> Make an sexpr
(def $fasl-sfloat 46)           ;<long> Make SINGLE-FLOAT from bits
(def $fasl-src 47)              ;<expr> - Set *loading-file-source-file * to <expr>.
(def $fasl-u32-vector 48)       ;<count> Make a (SIMPLE-ARRAY (UNSIGNED-BYTE 32) <count>)
(def $fasl-provide 49)          ;<string:expr>
(def $fasl-u64-vector 50)       ;<count> Make a (SIMPLE-ARRAY (UNSIGNED-BYTE 64) <count>)
(def $fasl-s64-vector 51)       ;<count> Make a (SIMPLE-ARRAY (SIGNED-BYTE 64) <count>)
(def $fasl-istruct 52)          ;<count> Make an ISTRUCT with <count> elements
(def $fasl-complex 53)          ;<real:expr><imag:expr>
(def $fasl-ratio 54)            ;<num:expr><den:expr>
(def $fasl-vector-header 55)    ;<count> Make a vector header
(def $fasl-array-header 56)     ;<count> Make an array header.
(def $fasl-s32 57)              ;<4bytes> Make a (SIGNED-BYTE 32)
(def $fasl-vintern-special 58)  ;<vstring> Intern in current pkg, ensure that it has a special binding index
(def $fasl-s64 59)              ;<8bytes> Make a (SIGNED-BYTE 64)
(def $fasl-vpkg-intern-special 60) ;<pkg:expr><vstring> Make a sym in pkg, ensure that it has a special binding index
(def $fasl-vmksym-special 61)   ;<vstring> Make an uninterned symbol, ensure special binding index
(def $fasl-nvmksym-special 62)  ;<nvstring> Make an uninterned symbol, ensure special binding index
(def $fasl-nvpkg-intern-special 63) ;<pkg:expr><nvstring> Make a sym in pkg, ensure that it has a special binding index
(def $fasl-nvintern-special 64)  ;<nvstring> Intern in current pkg, ensure that it has a special binding index
(def $fasl-nvpkg 65)            ;<vstring> Returns the package of given name
(def $fasl-nvpkg-intern 66)     ;<nvstring> Intern in current pkg.
(def $fasl-nvintern 67)         ;<pkg:expr><nvstring> Make a sym in pkg.
(def $fasl-nvmksym 68)          ;<nvstring> Make a string
(def $fasl-nvstr 69)            ;<nvstring> Make an uninterned symbol
(def $fasl-toplevel-location 70);<expr> - Set *loading-toplevel-location* to <expr>
(def $fasl-istruct-cell 71)     ;<expr> register istruct cell for expr
)

;;; <string> means <size><size bytes> (this is no longer used)
;;; <size> means either <n:byte> with n<#xFF, or <FF><n:word> with n<#xFFFF or
;;;   <FFFF><n:long>
;;; <count> is a variable-length encoding of an unsigned integer, written
;;;  7 bits per octet, the least significant bits written first and the most
;;;  significant octet having bit 7 set, so 127 would be written as #x00 and
;;;  128 as #x00 #x81
;;; <vstring> is a <count> (string length) followed by count octets of
;;; 8-bit charcode data.
;;; <nvstring> is a <count> (string length) followd by count <counts> of
;;;  variable-length charcode data.  This encodes ASCII/STANDARD-CHAR as
;;;  compactly as the <vstring> encoding, which should probably be deprecated.



(defconstant $fasl-end #xFF)    ;Stop reading.

(defconstant $fasl-epush-mask #x80)  ;Push value on etab if this bit is set in opcode.

(defmacro fasl-epush-op (op) `(%ilogior2 ,$fasl-epush-mask ,op))

(provide "FASLENV")
