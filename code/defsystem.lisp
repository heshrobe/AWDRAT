;;; -*- Syntax: Ansi-common-lisp; Package: cl-USER; Base: 10; Mode: LISP -*-

(in-package :cl-user)

(defvar *awdrat-home-directory* :not-yet)
(defvar *awdrat-wild-directory* :not-yet)

(eval-when (:execute :load-toplevel)
  (let* ((loading-file *load-truename*)
	 (host (pathname-host loading-file))
	 (device (pathname-device loading-file))
	 (home-dir (pathname-directory loading-file))
	 (wild-dir (append home-dir (list :wild-inferiors))))
    (setq *awdrat-home-directory* (make-pathname :directory home-dir
						 :host host
						 :device device)
	  *awdrat-wild-directory* (make-pathname :directory wild-dir
						 :host host
						 :device device
						 :type :wild
						 :name :wild
						 :version :unspecific))
    (setf (logical-pathname-translations "awdrat")
      `(("home;*.*"	,*awdrat-home-directory*)
	("**;*.*"	,*awdrat-wild-directory*)
	)))
    (with-open-file (F #P"awdrat:home;my-logical-pathnames.lisp" :direction :output :if-exists :supersede :if-does-not-exist :create)
      (format f "~%;;; awdrat")
      (format f "~2%~s" "awdrat")
      (loop for (a b) in (logical-pathname-translations "awdrat")
          do (format f "~%'(~s ~s)" (namestring a) (namestring b)))
      (terpri f)
      )
    #+ALLEGRO
    (pushnew (namestring (truename #P"awdrat:home;my-logical-pathnames.lisp"))
             (logical-pathname-translations-database-pathnames)
             :test #'string-equal)
  )


#+allegro
(defsystem awdrat
    (:default-pathname "awdrat:home;"
	:default-module-class separate-destination-module)
  (:serial
   ("package-definition" (:module-class separate-destination-module))
   ("mediator-support" (:module-class separate-destination-joshua-module))
   ("simulator" (:module-class separate-destination-joshua-module))
   ("timing" (:module-class separate-destination-joshua-module))
   ("mediator-coupling" (:module-class separate-destination-joshua-module))
   ("editor" (:module-class separate-destination-joshua-module))
   ("node-mapper" (:module-class separate-destination-joshua-module))
   ("resources" (:module-class separate-destination-joshua-module))

   ))

#+swank
(pushnew (cons "AWDRAT" ji::*joshua-readtable*)
	 swank:*readtable-alist*
	 :key #'first
	 :test #'string=)


#-allegro
(asdf:defsystem awdrat
  :name "AWDRAT"
  :description "Model based diagnosis for cyber security"
  :maintainer "Howie Shrobe"
  :pathname "."
  :components ((:file "package-definition")
               (:joshua-file "mediator-support" :depends-on ("package-definition"))
               (:joshua-file "simulator" :depends-on ("mediator-support"))
               (:joshua-file "timing" :depends-on ("simulator"))
               (:joshua-file "mediator-coupling" :depends-on ("timing"))
               (:joshua-file "editor" :depends-on ("mediator-coupling"))
               (:joshua-file "node-mapper" :depends-on ("editor"))
               (:joshua-file "resources" :depends-on ("node-mapper"))
               ))
