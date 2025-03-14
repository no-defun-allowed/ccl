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

;; l1-boot-2.lisp
;; Second part of l1-boot

(in-package "CCL")

(macrolet ((l1-load (name)
	     (let* ((namestring
		     (concatenate 'simple-base-string
                                  "./l1-fasls/"
				  (string name)
                                  (namestring (backend-target-fasl-pathname
                                               *target-backend*)))))
               `(let* ((*loading-file-source-file* *loading-file-source-file*)
                       (*loading-toplevel-location* *loading-toplevel-location*))
                  (%fasload ,namestring))))
	   (bin-load (name)
	     (let* ((namestring
		     (concatenate 'simple-base-string
                                  "./bin/"
				  (string name)
                                  (namestring (backend-target-fasl-pathname
                                               *target-backend*)))))
               `(let* ((*loading-file-source-file* *loading-file-source-file*)
                       (*loading-toplevel-location* *loading-toplevel-location*))
                  (%fasload ,namestring)))))


(catch :toplevel
    #+ppc-target
    (l1-load "ppc-error-signal")
    #+x86-target
    (l1-load "x86-error-signal")
    #+arm-target
    (l1-load "arm-error-signal")
    (l1-load "l1-error-signal")
    (l1-load "l1-sockets")
    (setq *LEVEL-1-LOADED* t))

#+ppc-target
(defun altivec-available-p ()
  "Return non-NIL if AltiVec is available."
  (not (eql (%get-kernel-global 'ppc::altivec-present) 0)))

#+ppc-target
(defloadvar *altivec-available* (altivec-available-p)
  "This variable is intitialized each time a Clozure CL session starts based
on information provided by the lisp kernel. Its value is true if AltiVec is
present and false otherwise. This variable shouldn't be set by user code.")

       
(defstatic *auto-flush-streams* ())
(def-ccl-pointers *auto-flush-streams* () (setq *auto-flush-streams* nil))
(defstatic *auto-flush-streams-lock* (make-lock))


(defvar *batch-flag* (not (eql (%get-kernel-global 'batch-flag) 0)))
(defloadvar *quiet-flag* nil)
(defvar *terminal-input* ())
(defvar *terminal-output* ())
(defvar *stdin* ())
(defvar *stdout* ())
(defvar *stderr* ())


(defun set-basic-stream-prototype (class)
  (when (subtypep class 'basic-stream)
    (setf (%class.prototype class) (or (%class.prototype class)
                                       (allocate-basic-stream class)))
    (dolist (subclass (class-direct-subclasses class))
      (set-basic-stream-prototype subclass))))

(set-basic-stream-prototype (find-class 'basic-stream))


;;; The hard parts here have to do with setting up *TERMINAL-IO*.
;;; Note that opening /dev/tty can fail, and that failure would
;;; be reported as a negative return value from FD-OPEN.
;;; It's pretty important that nothing signals an error here,
;;; since there may not be any valid streams to write an error
;;; message to.

(defglobal *interactive-streams-initialized* nil)

#+windows-target
(progn


(defun validate-standard-io-handles ()
  (let* ((in (#_GetStdHandle #$STD_INPUT_HANDLE))
         (out (#_GetStdHandle #$STD_OUTPUT_HANDLE)))
    (when (or (%null-ptr-p in)
              (%null-ptr-p out))
      (let* ((nulldevice (open-null-device)))
        (when nulldevice
          (when (%null-ptr-p in)
            (#_SetStdHandle #$STD_INPUT_HANDLE nulldevice))
          (when (%null-ptr-p out)
            (#_SetStdHandle #$STD_OUTPUT_HANDLE nulldevice)
            (ff-call (ccl::%kernel-import target::kernel-import-open-debug-output)
                     :int (%ptr-to-int nulldevice)
                     :int)))))))
)

(defun initialize-interactive-streams ()
  (let* ((encoding (lookup-character-encoding *terminal-character-encoding-name*))
         (encoding-name (if encoding (character-encoding-name encoding))))
    #+windows-target (validate-standard-io-handles)
    (setq *stdin* (let* ((infd #-windows-target 0
                               #+windows-target (%ptr-to-int
                                                 (#_GetStdHandle #$STD_INPUT_HANDLE))))
                               (make-fd-stream infd
                                  :basic t
                                  :sharing :lock
                                  :direction :input
                                  :interactive (or (not *batch-flag*)
                                                   (< (fd-lseek infd 0 #$SEEK_CUR)                                                      
                                                      0))
                                  :encoding encoding-name
                                  #+windows-target :line-termination #+windows-target :cp/m)))
    (setq *stdout* (make-fd-stream #-windows-target 1
                                   #+windows-target (%ptr-to-int
                                                     (#_GetStdHandle #$STD_OUTPUT_HANDLE))
                                   :basic t :direction :output :sharing :lock :encoding encoding-name #+windows-target :line-termination #+windows-target :msdos))
    (setq *stderr* (make-fd-stream #-windows-target 2
                                   #+windows-target (%ptr-to-int
                                                     (#_GetStdHandle #$STD_ERROR_HANDLE))
                                   :basic t :direction :output :sharing :lock :encoding encoding-name #+windows-target :line-termination #+windows-target :crlf))
    (add-auto-flush-stream *stdout*)
    (add-auto-flush-stream *stderr*)
    (if *batch-flag*
      (let* ((tty-fd
              #-windows-target
               (let* ((fd (fd-open "/dev/tty" #$O_RDWR)))
                 (if (>= fd 0) fd)))
             (can-use-tty #-windows-target (and tty-fd (eql (tcgetpgrp tty-fd) (getpid)))))
        (if can-use-tty
          (progn
            (setq
             *terminal-input* (make-fd-stream tty-fd
                                              :basic t
                                              :direction :input
                                              :interactive t
                                              :sharing :lock
                                              :encoding encoding-name)
             *terminal-output* (make-fd-stream tty-fd :basic t :direction :output :sharing :lock :encoding encoding-name)
             *terminal-io* (make-echoing-two-way-stream
                            *terminal-input* *terminal-output*))
            (add-auto-flush-stream *terminal-output*))
          (progn
            (when tty-fd (fd-close tty-fd))
            (setq *terminal-input* *stdin*
                  *terminal-output* *stdout*
                  *terminal-io* (make-two-way-stream
                                 *terminal-input* *terminal-output*))))
        (setq *standard-input* *stdin*
              *standard-output* *stdout*))
      (progn
        (setq *terminal-input* *stdin*
              *terminal-output* *stdout*
              *terminal-io* (make-echoing-two-way-stream
                             *terminal-input* *terminal-output*))
        (setq *standard-input* (make-synonym-stream '*terminal-io*)
              *standard-output* (make-synonym-stream '*terminal-io*))))
    (setq *error-output* (if (or *batch-flag*
                                 (not (same-fd-p (stream-device *stderr* :output)
                                                 (stream-device *stdout* :output))))
                           (make-synonym-stream '*stderr*)
                           (make-synonym-stream '*terminal-io*)))
    (setq *query-io* (make-synonym-stream '*terminal-io*))
    (setq *debug-io* *query-io*)
    (setq *trace-output* *standard-output*)
    (push *stdout* *auto-flush-streams*)
    (setf (input-stream-shared-resource *terminal-input*)
          (make-shared-resource "Shared Terminal Input")))
  (setq *interactive-streams-initialized* t))

(initialize-interactive-streams)

(def-standard-initial-binding *standard-input*)
(def-standard-initial-binding *standard-output*)
(def-standard-initial-binding *error-output*)
(def-standard-initial-binding *trace-output*)
(def-standard-initial-binding *debug-io*)
(def-standard-initial-binding *query-io*)

;;; Things bound by WITH-STANDARD-IO-SYNTAX (and not otherwise thread-local)
(def-standard-initial-binding *read-base*)
(def-standard-initial-binding *read-default-float-format*)
(def-standard-initial-binding *read-eval*) 
(def-standard-initial-binding *read-suppress*)



(defun set-terminal-encoding (encoding-name)
  #+windows-target (when (atom encoding-name)
                     (setq encoding-name `(:character-encoding ,encoding-name
                                           :line-termination :crlf)))
  (let* ((exformat (normalize-external-format t encoding-name)))
    (setf (stream-external-format *stdin*) exformat
          (stream-external-format *stdout*) exformat
          (stream-external-format *stderr*) exformat
          (stream-external-format *terminal-input*) exformat
          (stream-external-format *terminal-output*) exformat))
  encoding-name)

(catch :toplevel
    (macrolet ((l1-load-provide (module path)
		 `(let* ((*package* *package*))
		   (l1-load ,path)
		   (provide ,module)))
	       (bin-load-provide (module path)
		 `(let* ((*package* *package*))
		   (bin-load ,path)
		   (provide ,module))))
      (bin-load-provide "SORT" "sort")
      (bin-load-provide "NUMBERS" "numbers")
      
      (bin-load-provide "SUBPRIMS" "subprims")
      #+ppc32-target
      (bin-load-provide "PPC32-ARCH" "ppc32-arch") 
      #+ppc64-target
      (bin-load-provide "PPC64-ARCH" "ppc64-arch")
      #+x86-target
      (bin-load-provide "X8632-ARCH" "x8632-arch")
      #+x86-target
      (bin-load-provide "X8664-ARCH" "x8664-arch")
      #+arm-target
      (bin-load-provide "ARM-ARCH" "arm-arch")
      (bin-load-provide "VREG" "vreg")
      
      #+ppc-target
      (bin-load-provide "PPC-ASM" "ppc-asm")
      #+arm-target
      (bin-load-provide "ARM-ASM" "arm-asm")
      
      (bin-load-provide "VINSN" "vinsn")
      (bin-load-provide "REG" "reg")
      
      #+ppc-target
      (bin-load-provide "PPC-LAP" "ppc-lap")
      #+arm-target
      (bin-load-provide "ARM-LAP" "arm-lap")
      (bin-load-provide "BACKEND" "backend")
      (bin-load-provide "NX2" "nx2")
     
      #+ppc-target
      (provide "PPC2")                  ; Lie, load the module manually

      #+x86-target
      (provide "X862")

      #+arm-target
      (provide "ARM2") 
      (bin-load-provide "ACODE-REWRITE" "acode-rewrite")
     
      (l1-load-provide "NX" "nx")
      
      #+ppc-target
      (bin-load "ppc2")

      #+x86-target
      (bin-load "x862")

      #+arm-target
      (bin-load "arm2")
      
      (bin-load-provide "LEVEL-2" "level-2")
      (bin-load-provide "MACROS" "macros")
      (bin-load-provide "SETF" "setf")
      (bin-load-provide "SETF-RUNTIME" "setf-runtime")
      (bin-load-provide "FORMAT" "format")
      (bin-load-provide "STREAMS" "streams")
      (bin-load-provide "OPTIMIZERS" "optimizers")      
      (bin-load-provide "DEFSTRUCT-MACROS" "defstruct-macros")
      (bin-load-provide "DEFSTRUCT-LDS" "defstruct-lds")
      (bin-load-provide "NFCOMP" "nfcomp")
      (bin-load-provide "BACKQUOTE" "backquote")
      (bin-load-provide "BACKTRACE-LDS" "backtrace-lds")
      (bin-load-provide "BACKTRACE" "backtrace")
      (bin-load-provide "READ" "read")
      (bin-load-provide "ARRAYS-FRY" "arrays-fry")
      (bin-load-provide "APROPOS" "apropos")
      (bin-load-provide "SOURCE-FILES" "source-files")
      
      #+ppc-target
      (progn
	(bin-load-provide "PPC-DISASSEMBLE" "ppc-disassemble")
	(bin-load-provide "PPC-LAPMACROS" "ppc-lapmacros"))

      #+x86-target
      (progn
	(bin-load-provide "X86-DISASSEMBLE" "x86-disassemble")
	(bin-load-provide "X86-LAPMACROS" "x86-lapmacros")
	(bin-load "x86-watch"))

      #+arm-target
      (progn
	(bin-load-provide "ARM-DISASSEMBLE" "arm-disassemble")
	(bin-load-provide "ARM-LAPMACROS" "arm-lapmacros"))

      (bin-load-provide "FOREIGN-TYPES" "foreign-types")
      (install-standard-foreign-types *host-ftd*)
      
      #+(and ppc32-target linux-target)
      (bin-load-provide "FFI-LINUXPPC32" "ffi-linuxppc32")
      #+(and ppc32-target darwin-target)
      (bin-load-provide "FFI-DARWINPPC32" "ffi-darwinppc32")
      #+(and ppc64-target darwin-target)
      (bin-load-provide "FFI-DARWINPPC64" "ffi-darwinppc64")
      #+(and ppc64-target linux-target)
      (bin-load-provide "FFI-LINUXPPC64" "ffi-linuxppc64")
      #+(and x8632-target darwin-target)
      (bin-load-provide "FFI-DARWINX8632" "ffi-darwinx8632")
      #+(and x8664-target linux-target)  
      (bin-load-provide "FFI-LINUXX8664" "ffi-linuxx8664")
      #+(and x8664-target darwin-target)  
      (bin-load-provide "FFI-DARWINX8664" "ffi-darwinx8664")
      #+(and x8664-target freebsd-target)  
      (bin-load-provide "FFI-FREEBSDX8664" "ffi-freebsdx8664")
      #+(and x8664-target solaris-target)
      (bin-load-provide "FFI-SOLARISX8664" "ffi-solarisx8664")
      #+win64-target
      (bin-load-provide "FFI-WIN64" "ffi-win64")
      #+linuxx8632-target
      (bin-load-provide "FFI-LINUXX8632" "ffi-linuxx8632")
      #+win32-target
      (bin-load-provide "FFI-WIN32" "ffi-win32")
      #+solarisx8632-target
      (bin-load-provide "FFI-SOLARISX8632" "ffi-solarisx8632")
      #+freebsdx8632-target
      (bin-load-provide "FFI-FREEBSDX8632" "ffi-freebsdx8632")
      #+(and arm-target linux-target (not android-target))
      (bin-load-provide "FFI-LINUXARM" "ffi-linuxarm")
      #+(and arm-target android-target)
      (bin-load-provide "FFI-ANDROIDARM" "ffi-androidarm")
      #+(and arm-target darwin-target)
      (bin-load-provide "FFI-DARWINARM" "ffi-darwinarm")


      ;; Knock wood: all standard reader macros and no non-standard
      ;; reader macros are defined at this point.
      (setq *readtable* (copy-readtable *readtable*))

      (bin-load-provide "DB-IO" "db-io")

      (canonicalize-foreign-type-ordinals *host-ftd*)

      (bin-load-provide "CASE-ERROR" "case-error")
      (bin-load-provide "ENCAPSULATE" "encapsulate")
      (bin-load-provide "METHOD-COMBINATION" "method-combination")
      (bin-load-provide "MISC" "misc")
      (bin-load-provide "PPRINT" "pprint")
      (bin-load-provide "DUMPLISP" "dumplisp")
      (bin-load-provide "PATHNAMES" "pathnames")
      (bin-load-provide "TIME" "time")
      (bin-load-provide "COMPILE-CCL" "compile-ccl")
      (bin-load-provide "ARGLIST" "arglist")
      (bin-load-provide "EDIT-CALLERS" "edit-callers")
      (bin-load-provide "DESCRIBE" "describe")
      (bin-load-provide "SWINK" "swink")
      (bin-load-provide "COVER" "cover")
      (bin-load-provide "LEAKS" "leaks")
      #-cross-compiling (bin-load-provide "CORE-FILES" "core-files")
      #-cross-compiling (bin-load-provide "DOMINANCE" "dominance")
      (bin-load-provide "SWANK-LOADER" "swank-loader")
      (bin-load-provide "REMOTE-LISP" "remote-lisp")
      (bin-load-provide "MCL-COMPAT" "mcl-compat")
      (require "LISPEQU") ; Shouldn't need this at load time ...
      (require "LOOP")
      (bin-load-provide "CCL-EXPORT-SYMS" "ccl-export-syms")
      (l1-load-provide "VERSION" "version")
      (require "JP-ENCODE")
      (require "CN-ENCODE")
      (require "SOCKETS")
      )
    (setq *%fasload-verbose* nil)
    )
)






