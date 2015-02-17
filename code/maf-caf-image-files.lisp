;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat ; readtable: joshua -*-

(in-package :awdrat)

(define-service (image-load [image-loaded ?image ?path])
    (speed fast slow)
  (image-quality high low)
  (safety checked unchecked))

(define-method native-image-load
    :service image-load
    :features ((speed fast) 
	       (image-quality ?quality-of-image-type)
	       (safety unchecked))
    :other-parameters (?path)
    :resources (?image-file)
    :resource-constraints ([image-file-exists ?path ?image-type ?image-file]
			   [image-type-consistent-with-method ?image-type native-image-load]
			   [image-quality ?image-type ?quality-of-image-type])
    )

(define-method pure-java-image-load
    :service image-load
    :features ((speed slow) 
	       (image-quality ?quality-of-image-type)
	       (safety checked))
    :other-parameters (?path)
    :resources (?image-file)
    :resource-constraints ([image-file-exists ?path ?image-type ?image-file]
			   [image-type-consistent-with-method ?image-type pure-java-image-load]
			   [image-quality ?image-type ?quality-of-image-type])
    )

(defun decide-how-to-load-images (max-value path)
   (let ((utility-function
 	  (utility-function-for-service 
 	    'image-load
 	    '((speed fast (>> 1.1) speed slow)
	      (image-quality high (>> 1.5) image-quality low)
	      (safety checked (>> 2) safety unchecked)
	      ;; (speed fast (>> 1.1) safety checked)
 	      ;; (image-quality high (>> 1.2) safety checked)
 	      (speed fast (>> 1.5) image-quality high))
	      max-value
 	      )))
     (find-em 'image-load utility-function nil (list path))))


(defun compose-pathname (root type)
  (concatenate 'string (string root) "." (string-downcase (string type))))

;;; A hack to say that all 4 versions exist for any file
(defrule image-file-exist-1 (:backward)
  then [image-file-exists ?path ?image-type ?image-file]
  if (cond ((unbound-logic-variable-p ?image-type)
	    (loop for type in '(gif jpg bmp png)
		do (with-unification
		       (unify ?image-type type)
		     (unify ?image-file (compose-pathname ?path ?image-type))
		     (succeed)))
	    nil)
	   (t (when (member ?image-type  '(gif jpg bmp png))
		(with-unification
		    (unify ?image-file (compose-pathname ?path ?image-type))
		  (succeed)))
	      nil)))

;;; A hack to say that any code file exists
(defrule code-file-exists (:backward)
  Then [code-file-exists ?path]
  if t)

(defun assert-image-file-facts ()
  (tell [cost-of-failure pure-java-image-load 0.5 ])
  (tell [cost-of-failure native-image-load 10])

  (tell [image-quality gif high])
  (tell [image-quality jpg high])
  (tell [image-quality png low])
  (tell [image-quality bmp low])

  (tell [image-type-consistent-with-method gif native-image-load])
  (tell [image-type-consistent-with-method jpg native-image-load])
  (tell [image-type-consistent-with-method png native-image-load])
  (tell [image-type-consistent-with-method bmp native-image-load])

  (tell [image-type-consistent-with-method gif pure-java-image-load])
  (tell [image-type-consistent-with-method png pure-java-image-load])
  (tell [image-type-consistent-with-method jpg pure-java-image-load])
  (tell [not [image-type-consistent-with-method bmp pure-java-image-load]]))

(defun initialize-facts-about-image-loading (path &optional broken-type-alist)
  ;; remove previous probability assertions
  (loop for type in '(gif jpg bmp png)
      do (ask `[state-of ,(compose-pathname path type) working ?]
	      #'(lambda (bs)
		  (let ((pred (ask-database-predication bs)))
		    (when pred
		      (untell pred))))))

  ;; insert new probability assertions
  (loop for type in '(gif jpg bmp png)
      for probability = (or (cdr (assoc type broken-type-alist)) 1)
      do (tell `[state-of ,(compose-pathname path type) working ,probability]))
  )

(defun initialize-facts-about-image-directory (directory-path &optional broken-type-alist)
  (let ((all-files (common-lisp:directory directory-path)))
    (loop for file in all-files
	for file-type = (pathname-type file)
	for file-string = (namestring file)
	when (member file-type '("bmp" "gif" "png" "jpg") :test #'string-equal)
	do (ask `[state-of ,file-string working ?]
		#'(lambda (bs)
		    (let ((pred (ask-database-predication bs)))
		      (when pred
			(untell pred)))))
	   (let ((prob (or (cdr (assoc file-string broken-type-alist :test #'string-equal)) 1)))
	     (tell `[state-of ,file-string working ,prob])))))
	   
(defun bad-case ()
  (initialize-facts-about-image-loading "/foo/bar/baz" '((gif . 0.1) (jpg . 0.1)))
  (decide-how-to-load-images 10 "/foo/bar/baz"))

(defun good-case ()
  (initialize-facts-about-image-loading "/foo/bar/baz")
  (decide-how-to-load-images 10 "/foo/bar/baz"))

(defvar *trust-model* nil)
(defvar *killer-jpg* "C:\\jbi\\afrl\\v1.1\\clients\\MAF.EMC\\Source\\mil\\af\\rl\\jbi\\client\\ExtensibleMappingClient\\client\\resources\\saveimage.jpg")

(defun read-in-trust-model (&key (trust-model "./trust-model.lisp")
				 image-directories)
  (setq *trust-model*
    (with-open-file (f trust-model :if-does-not-exist nil :direction :input)
      (when f
	(loop for path = (read f nil 'eof)
	    for prob = (read f nil 'eof)
	    until (eql path 'eof)
	    collect (cons (namestring (merge-pathnames path)) prob)))))
  (loop for image-directory in image-directories
      for full-image-directory = (directory-of-pathname (pathname image-directory))
      do (initialize-facts-about-image-directory full-image-directory *trust-model*)))

(defun write-out-trust-model (&key (trust-model-pathname "./trust-model.lisp"))
  (with-open-file (f trust-model-pathname
		   :if-does-not-exist :create
		   :if-exists :supersede
		   :direction :output)
    (loop for (thing . prob) in *trust-model*
	do (write thing :stream f)
	   (write-string " " f)
	   (write prob :stream f)
	   (terpri f))))

(defun update-trust-model (set-of-updates)
  (loop for (thing . prob) in set-of-updates
      for entry = (assoc thing *trust-model* :test #'string-equal)
      if entry
      do (setf (cdr entry) prob) 
      else do (push (cons thing prob) *trust-model*)))

(defparameter *image-directory*
     "./Source/mil/af/rl/jbi/client/ExtensibleMappingClient/client/resources/")

(defun convert-resource-probabilities (probability-alist)
  (let* ((imagery (assoc 'imagery probability-alist))
	 ;; Hack alert - way too specific
	 (normal-entry (assoc 'normal (cdr imagery)))
	 (probability (second normal-entry)))
    (when probability
      (let* ((directory (truename (pathname *image-directory*)))
	     (suspect (merge-pathnames (pathname "saveimage.jpg") directory))
	     (cousins (loop for type in '("bmp" "gif" "png")
			  collect (merge-pathnames 
				   (make-pathname :type type)
				   suspect))))
	(let ((updates (loop for cousin in cousins
			   collect (cons (namestring cousin)
					 (* probability 2)))))
	  (push (cons (namestring suspect) probability) updates)
	  updates
  )))))

(defun kill-state-of-assertions ()
  (ask [state-of ? ? ?]
       #'(lambda (bs) (untell (ask-database-predication bs)))))

(defun directory-of-pathname (path)
  (let ((directory (pathname-directory path)))
    (make-pathname :directory directory
		   :name :wild
	 	   :type :wild
		   :defaults path)))

(defun trust-model-case (path)
  (let ((namestring (namestring (make-pathname :defaults path
					       :type nil))))
    (multiple-value-bind (best-method i1 best-resources i2)
	(decide-how-to-load-images 10 namestring)
      (declare (ignore i1 i2))
      (values best-method best-resources))))

; (tell [state-of direct-connection working])
; (tell [input-file-exists maf-caf file-1 recent])
; (tell [state-of file-1 working])
; (tell `[cost-of ,(follow-path '(core-oadb)) 2])
; (tell `[cost-of ,(follow-path '(maf-caf-oadb)) 2])

; (make-everything-working)

; (defun make-everything-working ()
;   (ask [or [object-type-of ?x computer]
;        [object-type-of ?x database]]
;        #'(lambda (stuff)
; 	   (declare (ignore stuff))
; 	   (set-object-state ?x 'working))))

(defun set-object-state (object-or-pathname &optional (value 'working))
  (let ((object (if (typep object-or-pathname 'list)
		    (follow-path object-or-pathname)
		  object-or-pathname)))
    (ask `[state-of ,object ?]
	 #'(lambda (stuff)
	     (let ((pred (ask-database-predication stuff)))
	       (when pred
		 (untell pred))))
	 :do-backward-rules nil
	 :do-questions nil)
    (tell `[state-of ,object ,value])))