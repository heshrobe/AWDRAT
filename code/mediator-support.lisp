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

;;; reporting the event to the simulator
;;; Things reported are:
;;; 1) the event name
;;; 2) the type of event (entry exit)
;;; 3) the universal time at which the event was noticed
;;; 4) the process it was noticed in
;;; 5) the args and/or the return-value

(defvar *event-registry* (make-hash-table :test #'equal))
(defparameter *monitored-threads* :all)

(defgeneric notice-event (event-name event-type universal-time process args))

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
	 (let ((process mp:*current-process*))
	   (cond
	    ;; if we're not monitoring this thread
	    ;; because it's not one of a selected set
	    ;; and we're not monitoring all threads
	    ;; then just invoke the function
	    ((not (or (eql *monitored-threads* :all)
		      (member process *monitored-threads*)))
	     (call-next-fwrapper))
	    (t ;;otherwise send the events if appropriate
	     ,(when entry
		`(notice-event ',event-name 'entry (get-universal-time) mp:*current-process* args))
	     ,(when exit
		`(let ((return-values (multiple-value-list (call-next-fwrapper))))
		   (notice-event ',event-name 'exit (get-universal-time) mp:*current-process* return-values)
		   (apply #'values return-values))))))))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Infrastructure Support for Tracers
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Macro for defining Event noticers that do something other than 
;;; reporting the event to the simulator
;;; this macro is used by the lisp stubs

;;; tracers are wrappers around the notice-event method
;;; It's done this way, rather than wrapping the function directly
;;; because in principle, the monitor and the program could be in two separate
;;; lisps (or other programs as with the original java-wrappers)
;;; on different machines (not that this is implemented right now), communicating
;;; via lisp-rpc or something like that.
;;; The tracer is conceptually part of the monitor, so it has to work by using the notice-event mechanism

(defmacro deftracer ((event-name event-type) arglist &body body)
  (let ((declaration nil))
    (when (eql (first (first body)) 'declare)
      (push (pop body) declaration))
    `(defmethod notice-event ,(ecase event-type (entry :before) (exit :after)) ((event-name (eql ',event-name)) (event-type (eql ',event-type))
										universal-time process args)
       (declare (ignorable universal-time process))
       (destructuring-bind (,@arglist) args
	 ,@declaration
	 (restart-case
	     ;;This forces debugger entry
	     (handler-bind ((error #'invoke-debugger)) ,@body)
	   ;; This offers the possibility of just returning
	   (return ()
		   :report "Return from tracer"))))))