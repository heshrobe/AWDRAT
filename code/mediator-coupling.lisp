;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat ; readtable: joshua -*-

;;; This is from ~/aire2/edu/mit/aire/awdrat/
;;; It was part of the final demo and has a lot of stuff
;;; specific to the java coupling and the maf-caf-demo
;;; Surgery will be performed here, the original remains
;;; But there is stuff in here that maybe should be in the simulator
;;; safefamily is presumably the windows mediator stuff that talked to
;;; AWDRAT via sockets

(in-package :awdrat)

(defrule bad-events-are-contradictory (:forward)
  if [and [no-bad-events ?component] :support ?f1
	  [bad-event-detected ?event ?time ?component ?args]:support ?f2
	  ]
  then (diagnose-from-bad-event ?component ?f1 ?f2))

(defrule completed-normal-means-no-bad-event (:forward)
  if [selected-model ?component normal]
  then [no-bad-events ?component])

(defun diagnose-from-bad-event (component no-bad-event-assert bad-event-assert)
  ;; The bad event assertion is only made as a premise by 
  ;; the event tracking part of the simulator
  ;; Unjustify it now to prevent a tms contradiction
  ;; before we're ready to handle it.
  ;; (unjustify bad-event-assert)
  ;; set up so that when we re-justify it there will be a contradition
  (tell [ltms:contradiction] 
	:justification `(bad-event-conflict 
			 (,bad-event-assert ,no-bad-event-assert)))
  (with-statement-destructured (event-name time the-component args) bad-event-assert
    (declare (ignore time args the-component))
    (error 'execution-aborted-due-to-bad-event
	   :component component
	   :event-name event-name))
  )

(defvar *search-control* nil)

(define-condition execution-aborted-due-to-bad-event (error) 
  ((component :reader component :initarg :component)
   (event-name :reader event-name :initarg :event-name))
  (:report (lambda (self stream)
	     (format stream "Execution was aborted in ~a due to the disallowed event ~a"
		     (component self) (event-name self)))))

(defparameter *my-ensemble* nil)
(defparameter *my-component* nil)

(defun harnessing (function ensemble-name
		   &key
		   (monitored-threads (list mp:*current-process*))
		   (attack-models *attack-models*)
		   (stream '*standard-output*))
  (clim-utils:letf-globally ((*monitored-threads* monitored-threads))
    (clear)
    (install-all-events)
    (unwind-protect
	(let* ((outside (build-interface ensemble-name 'my-example))
	       (inside (build-implementation ensemble-name  outside))
	       (*my-ensemble* inside)
	       (*my-component* outside)
	       (contradiction-detected nil))
	  (catch 'quick-exit
	    (handler-bind
		((ltms:ltms-contradiction 
		  #'(lambda (condition)
		      (setq contradiction-detected t)
		      (format stream "~%Contradiction detected:~% In ensemble ~a ~% Active attack models ~{~a~^ ,~}" ensemble-name attack-models)
		      (multiple-value-bind (ignore ignore true-support false-support ignore)
			  (destructure-justification (current-justification (tms-contradiction-contradictory-predication condition)))
			(declare (ignore ignore))
			(let ((*print-length* 4))
			  (format stream "~2%Contradictory Predications: ")
			  (clim:indenting-output (stream 4)
			    (flet ((do-a-list (preds)
				     (loop for pred in preds do (print pred stream))))
			      (do-a-list true-support)
			      (do-a-list false-support)))))
		      (terpri stream)
		      (setq *search-control*
			(set-up-search-control (object-name *my-ensemble*) *my-ensemble* attack-models))
		      (multiple-value-bind (nogood assumptions) (nogood-from-condition condition)
			(declare (ignore nogood))		
			(loop for clause in assumptions
			    do (multiple-value-bind (mnemonic assertion) (destructure-justification clause)
				 (declare (ignore mnemonic))
				 (with-statement-destructured (component model) assertion
				   (format stream "~%Retracting Model ~a for ~a" model component))))
			(invoke-restart :unjustify-subset assumptions))))
		 (execution-aborted-due-to-bad-event
		   #'(lambda (condition)
		       (declare (ignore condition))
		       (throw 'quick-exit (values)))))
	      (funcall function)))
	  (cond (contradiction-detected
		 (remove-all-selected-components *search-control*)
		 (solve *search-control* stream nil))
		(t (format stream "~%Clean execution"))))
      (uninstall-all-events)
      (values))))

(defmacro with-harness ((ensemble-name
			 &key (monitored-threads '(mp:*current-process*))
			      (attack-models '*attack-models*)
			      (stream '*standard-output*))
			&body body)
  `(flet ((monitored-process () ,@body))
     (harnessing #'monitored-process ',ensemble-name
		 :monitored-threads (list ,@monitored-threads)
		 :attack-models ,attack-models
		 :stream ,stream)))
		

(defvar *trust-model* nil)

(defmethod solve ((sc awdrat:search-control) stream &optional (report-while-going t))
  (let* ((awdrat:*report-out-loud* report-while-going)
         (awdrat:*editor-in-control* nil))
    (declare (special awdrat:*report-out-loud* awdrat:*editor-in-control*))
    (format stream "~2%Finding Diagnoses")
    (find-solutions sc nil)
    (unless report-while-going
      (format stream "~2%Diagnoses:")
      (clim:indenting-output (stream 4)
	(loop for diagnosis in (solution-states sc)
	    do (terpri stream)
	       (loop for pred in diagnosis
		   do (terpri stream)
		      (ji:print-database-predication-without-truth-value pred stream))))
      (format stream "~2%Nogoods found:")
      (clim:indenting-output (stream 4)
	(loop for entry in (nogoods sc)
	    do (terpri stream)
	       (loop for pred in (rest entry) 
		   do (terpri stream)
		      (ji:print-database-predication-without-truth-value pred stream)))))
    (format stream "~2%Calculating Probabilities of Resource States~%")
    (let* ((probs (all-resource-probabilities sc))
	   ;; (updates (awdrat:convert-resource-probabilities probs))
	   )
      (declare (ignore probs))
      (terpri stream)
      (table-resources sc nil stream)
      (terpri stream)
      ;; (loop for (thing value) in probs do (format stream "~%(~10t~a     ~a)" thing value))
      ;;(update-trust-model updates)
      )
    ;; (awdrat:write-out-trust-model)
    ))

(defun update-trust-model (set-of-updates)
  (loop for (thing . prob) in set-of-updates
      for entry = (assoc thing *trust-model* :test #'string-equal)
      if entry
      do (setf (cdr entry) prob) 
      else do (push (cons thing prob) *trust-model*)))

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


#||


(defun convert-resource-probabilities (probability-alist)
  (let* ((imagery (assoc 'awdrat::imagery probability-alist))
	 ;; hack alert - way too specific
	 (normal-entry (assoc 'normal (cdr imagery)))
	 (probability (or (second normal-entry) 0))
	 (updates nil))
    (when probability
      (loop for file-name in *loaded-image-files*
	  for suspect = (pathname file-name)
	  for cousins = (loop for type in '("bmp" "gif" "png")
			  collect (merge-pathnames 
				   (make-pathname :type type)
				   suspect))
	  do (loop for cousin in cousins
		 do (push (cons (namestring cousin) (* probability 2))
			  updates))))
    updates
    ))

||#


(defvar *mediator-tracing* nil)

(defun mediator-trace (stream format-string &rest args)
  (when *mediator-tracing*
    (apply #'format stream format-string args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;  Showing System Status
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *presentation-window* nil)
(defvar *presentation-process* nil)

(defun get-presentation-window ()
  (unless *presentation-window* 
    (setq *presentation-window* 
      (clim:open-window-stream 
       :label "Situation Display"
       :scroll-bars t
       :width 400 :height 300 :left 200 :top 100)))
  (clim:window-expose *presentation-window*))

(defun close-presentation-window ()
  (clim:destroy-frame (clim:pane-frame *presentation-window*))
  (setq *presentation-window* nil))

(defun show-situation-display ()
  (get-presentation-window)
  (clim:window-stack-on-top *presentation-window*)
  (labels 
      ((get-children (ensemble)
	 (let ((stuff nil))
	   (ask `[component ,ensemble ?name ?comp]
		#'(lambda (just)
		    (declare (ignore just))
		    (let ((comp-status (get-component-status ?comp)))
		      (when comp-status
			(push (list ?name 
				    comp-status
				    (get-component-children ?comp))
			      stuff)))))
	   stuff))
       (get-component-status (component)
	 (let ((stats nil))
	   (ask `[execution-status ,component normal ?s]
		#'(lambda (just)
		    (declare (ignore just))
		    (push ?s stats)))
	   (cond ((member 'completed stats) "Completed")
		 ((member 'started stats) "Started"))))
       (get-component-children (component)
	 (ask `[corresponding-ensemble ,component ?ensemble]
	      #'(lambda (just)
		  (declare (ignore just))
		  (return-from get-component-children
		    (get-children ?ensemble))))))
    (clim:window-clear  *presentation-window*)
    (let ((tree (get-children nil)))
      (clim:format-graph-from-roots
       tree
       #'(lambda (node stream)
	   (let ((name (first node))
		 (status (second node)))
	     (clim:surrounding-output-with-border (stream)
	       (format stream "~a~% ~a" name status))))
       #'(lambda (node)
	   (third node))
       :stream *presentation-window*))))