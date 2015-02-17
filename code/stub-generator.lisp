;;; -*- Mode: common-lisp; Syntax: joshua; Package: awdrat; readtable: joshua -*-

(in-package :awdrat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Syntax Hackers
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun explode (string &optional (delimiter #\.))
  (loop for last = 0 then (1+ next)
      for next = (position delimiter string :test #'char-equal :start last)
      collect (subseq string last next)
      until (null next)))

(defun implode (list &optional (delimiter #\.))
  (intern
   (string-upcase  
    (with-output-to-string (f)
      (loop for first = t then nil
	  for term in list
	  unless first do (write-char delimiter f)
	  do (write-string (string term) f))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;  Registering Events
;;;
;;; A registered event is just an fwrapper that calls notice-event (optionally) on entry and exit of the wrapped function
;;; 1) The call to notice-event includes:
;;; 2) the event name
;;; 3) a key-word (:entry or :exit) 
;;; 4) the arguments provided to the function (as a list) for entry events
;;;    or the return values produced by the function (as a list) for exit events
;;; 5) the universal-time of the event 
;;; 6) the process in which the event was noticed.
;;;
;;; this also makes an entry in the event registry
;;; The entry is indexed under event-name 
;;; and contains a list of two things: t
;;; 1) A list of functions wrapped with this event noticer
;;; 2) The fwrapper name
;;; This allows us to have several functions produce the same event.  Notice that because we gobble all the args into a single &rest value
;;; the same fwrapper can be applied to multiple functions with different arglist (even non-congruent ones).
;;; similarly for return values.
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *event-registry* (make-hash-table :test #'equal))

(defun clear-registries () (clrhash *event-registry*))

(defmacro register-event (event-name function-name &key (entry t) (exit t))
  (let ((wrapper-name (implode (list "wrap" (string function-name)) #\-)))
    `(eval-when (:execute :load-toplevel)
      (let ((entry (gethash ',event-name *event-registry*)))
	(when (null entry)
	  (setq entry (list nil ',wrapper-name))
	  (setf (gethash ',event-name *event-registry*) entry) )
	(pushnew ',function-name (first entry)))
      (def-fwrapper ,wrapper-name (&rest args)
	,(when entry
	   `(notice-event ',event-name :entry (get-universal-time) mp:*current-process* args))
	(let ((return-values (multiple-value-list (call-next-fwrapper))))
	  ,(when exit
	     `(notice-event ',event-name :exit (get-universal-time) mp:*current-process* return-values)))))))

(defun install-event (event-name &optional function-name)
  (let ((entry (gethash event-name *event-registry*)))
    (destructuring-bind (functions wrapper-name) entry
      (cond
       ((null function-name)
	(loop for function-name in functions
	    do (fwrap function-name 'event wrapper-name)))
       ((member function-name functions)
	(fwrap function-name 'event wrapper-name))
       (t (error "Function ~a is not registered for event ~a"
		 function-name event-name))))))

(defun install-all-events ()
  (loop for (functions wrapper-name) being the hash-values of *event-registry*
      do (loop for function-name in functions
	     do (fwrap function-name 'event wrapper-name))))

(defun uninstall-event (function-name)
  (funwrap function-name 'event))

(defun uninstall-all-events ()
  (loop for (functions) being the hash-values of *event-registry*
      do (loop for function-name in functions
	     do (funwrap function-name 'event))))

(defun disable-event (event-name)
  (destructuring-bind (functions fwrapper-name) (gethash event-name *event-registry*)
    (declare (ignore fwrapper-name))
    (loop for function-name in functions
	do (funwrap function-name 'event))))
