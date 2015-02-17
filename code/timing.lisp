;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat ; readtable: joshua -*-

(in-package :awdrat)

;;; This file has all the stuff having to do with timing models.  This is unused at the moment.

;;; dynamic assertions about timing
(define-predicate potentially (predicate) (ltms:ltms-predicate-model))
(define-predicate earliest-arrival-time (port component time) (ltms:ltms-predicate-model))
(define-predicate latest-arrival-time (port component time)(ltms:ltms-predicate-model))
(define-predicate earliest-production-time (port component time)(ltms:ltms-predicate-model))
(define-predicate latest-production-time (port component time)(ltms:ltms-predicate-model))

(defmacro deftiming-model ((component model-name) &body rules)
  `(progn
     ,@(loop for (inputs outputs min max) in rules
	     for clause-number from 0
	     for clause-name = (make-name component model-name)
	     append (build-forward-propagators inputs outputs component model-name clause-number min max clause-name)
	     append (build-backward-propagators inputs outputs component model-name clause-number min max clause-name))))

(defun build-forward-propagators (inputs outputs component-name model-name clause-number min max rule-name)
  (setq rule-name (make-name rule-name 'forward))
  (let ((min-rule-name (intern (format nil "~a-~a-F-min-~d" component-name model-name clause-number)))
	(max-rule-name (intern (format nil "~a-~a-F-max-~d" component-name model-name clause-number))))
    (list (let ((model-support `(logic-variable-maker ,(intern "?model-support")))
		(ensemble-variable `(logic-variable-maker ,(intern "?ENSEMBLE" )))
		(component-variable `(logic-variable-maker ,(intern "?COMPONENT"))))
	    (loop for input in inputs
                for counter from 0
                for logic-variable = `(logic-variable-maker ,(intern (format nil "?input-~d" counter)))
                for support-lv = `(logic-variable-maker ,(intern (format nil "?support-~d" counter)))
                collect logic-variable into lvs
                collect support-lv into support-lvs
                append `((predication-maker '(earliest-arrival-time ,input ,component-variable ,logic-variable)) 
			 :support ,support-lv)
		 into clauses
		finally 
		  (return `(defrule ,min-rule-name (:forward)
			     If (predication-maker
				 '(and
				   (predication-maker '(component ,ensemble-variable ,component-name ,component-variable))
				   (predication-maker '(selected-model ,component-variable ,model-name))
				   :support ,model-support
				   ,@clauses))
			     then (compute-forward-min-delay (list ,@lvs) ,min ',outputs ,component-variable
							     (list ,model-support ,@support-lvs)
							     ',rule-name)))))
	  (let ((model-support `(logic-variable-maker ,(intern "?model-support")))
		(ensemble-variable `(logic-variable-maker ,(intern "?ENSEMBLE")))
		(component-variable `(logic-variable-maker ,(intern "?COMPONENT"))))
	    (loop for input in inputs
                for counter from 0
                for logic-variable = `(logic-variable-maker ,(intern (format nil "?input-~d" counter)))
                for support-lv = `(logic-variable-maker ,(intern (format nil "?support-~d" counter)))
                collect logic-variable into lvs
                collect support-lv into support-lvs
                append `((predication-maker '(latest-arrival-time ,input ,component-variable ,logic-variable))
                         :support ,support-lv)
                into clauses
		finally  
		  (return `(defrule ,max-rule-name (:forward)
			     If (predication-maker
				 '(and 
				   (predication-maker '(component ,ensemble-variable ,component-name ,component-variable))
				   (predication-maker '(selected-model ,component-variable ,model-name))
				   :support ,model-support
				   ,@clauses))
			     then (compute-forward-max-delay (list ,@lvs) ,max ',outputs ',component-variable
							     (list ,model-support ,@support-lvs)
							     ',rule-name))))))))


(defun compute-forward-min-delay (input-times delay output-names component support rule-name)
  (let* ((max-of-input-times (loop for input-time in input-times maximize input-time))
         (output-time (+ max-of-input-times delay)))
    (loop for output-name in output-names doing
          (tell `[potentially [earliest-production-time ,output-name ,component ,output-time]]
                :justification `(,rule-name ,support)))))

(defun compute-forward-max-delay (input-times delay output-names component support rule-name)
  (let* ((max-of-input-times (loop for input-time in input-times maximize input-time))
         (output-time (+ max-of-input-times delay)))
    (loop for output-name in output-names doing
          (tell `[potentially [latest-production-time ,output-name ,component ,output-time]]
                :justification `(,rule-name ,support)))))

(defun build-backward-propagators (inputs outputs component-name model-name clause-number min max rule-name)
  (setq rule-name (make-name rule-name 'backwards))
  (loop for output in outputs
      for output-counter from 0
      append
	(loop for input in inputs
	    for input-counter from 0
	    for min-rule-name = (intern (format nil "~a-~a-B-min-~d-~d-~d"
						component-name model-name clause-number input-counter output-counter)
					)
	    for max-rule-name = (intern (format nil "~a-~a-B-max-~d-~d-~d"
						component-name model-name clause-number input-counter output-counter)
					)
	    collect
	      (let ((model-support `(logic-variable-maker ,(intern "?model-support")))
		    (output-lv `(logic-variable-maker ,(intern "?output-time")))
		    (output-support `(logic-variable-maker ,(intern "?output-support")))
		    (ensemble-variable `(logic-variable-maker ,(intern "?ENSEMBLE")))
		    (component-variable `(logic-variable-maker ,(intern "?COMPONENT"))))
		(loop for other-input in (remove input inputs)
		    for counter from 0
		    for logic-variable = `(logic-variable-maker ,(intern (format nil "?input-~d" counter)))
		    for support-lv = `(logic-variable-maker ,(intern (format nil "?support-~d" counter)))
		    collect logic-variable into lvs
		    collect support-lv into support-lvs
		    append `((predication-maker
			      '(earliest-arrival-time ,other-input ,component-variable ,logic-variable)) :support ,support-lv)
		    into clauses
		    finally  
		      (return
			`(defrule ,min-rule-name (:forward)
			   If (predication-maker
			       '(and
				 (predication-maker '(component ,ensemble-variable ,component-name ,component-variable))
				 (predication-maker '(selected-model ,component-variable ,model-name))
				 :support ,model-support
				 (predication-maker '(earliest-production-time ,output ,component-variable ,output-lv)) 
				 :support ,output-support
				 ,@clauses))
			   then (compute-backward-min-delay ,output-lv (list ,@lvs) ,max ',input ,component-variable
							    (list ,model-support ,output-support
								  ,@support-lvs)
							    ',rule-name
							    )))))
	    collect (let ((model-support `(logic-variable-maker ,(intern "?model-support")))
			  (support-lv `(logic-variable-maker ,(intern "?output-support")))
			  (output-lv `(logic-variable-maker ,(intern "?output")))
			  (ensemble-variable `(logic-variable-maker ,(intern "?ENSEMBLE")))
			  (component-variable `(logic-variable-maker ,(intern "?COMPONENT"))))
		      `(defrule ,max-rule-name (:forward)
			 If (predication-maker
			     '(and 
			       (predication-maker '(component ,ensemble-variable ,component-name ,component-variable))
			       (predication-maker '(selected-model ,component-variable ,model-name)) :support ,model-support
			       (predication-maker '(latest-production-time ,output ,component-variable ,output-lv))
			       :support ,support-lv))
			 then (compute-backward-max-delay ,output-lv ,min ',input ,component-variable
							  (list ,model-support ,support-lv)
							  ',rule-name))))))

(defun compute-backward-min-delay (output-time other-input-times delay input-name component support rule-name)
  (let* ((max-of-other-input-times (loop for input-time in other-input-times maximize input-time))
         (input-constraint (- output-time delay)))
    (when (> input-constraint max-of-other-input-times)
      (tell `[potentially [earliest-arrival-time ,input-name ,component ,input-constraint]]
            :justification `(,rule-name ,support)))))

(defun compute-backward-max-delay (output-time delay input-name component support rule-name)
  (let* ((constraint (- output-time delay)))
    (tell `[potentially [latest-arrival-time ,input-name ,component ,constraint]]
          :justification `(,rule-name ,support))))




;;; Basic rules for detecting conflicts
;;; and propagating dataflows

(defrule time-inconsistency-1 (:forward)
  If [and [earliest-arrival-time ?input ?component ?early]
          [latest-arrival-time ?input ?component ?late]
          (> ?early ?late)
          ]
  then [ltms:contradiction])

(defrule time-inconsistency-2 (:forward)
  If [and [earliest-production-time ?output ?component ?early]
          [latest-production-time ?output ?component ?late]
          (> ?early ?late)
          ]
  then [ltms:contradiction]) 

(defrule dataflow-timing-1 (:forward)
  If [and [dataflow ?producer-port ?producer ?consumer-port ?consumer]
          [earliest-arrival-time ?consumer-port ?consumer ?time]]
  then [potentially [earliest-production-time ?producer-port ?producer ?time]])

(defrule dataflow-timing-2 (:forward)
  If [and [dataflow ?producer-port ?producer ?consumer-port ?consumer]
          [latest-arrival-time ?consumer-port ?consumer ?time]]
  then [potentially [latest-production-time ?producer-port ?producer ?time]])

(defrule dataflow-timing-3 (:forward)
  If [and [dataflow ?producer-port ?producer ?consumer-port ?consumer]
          [earliest-production-time ?producer-port ?producer ?time]]
  then [potentially [earliest-arrival-time ?consumer-port ?consumer ?time]])

(defrule dataflow-timing-4 (:forward)
  If [and [dataflow ?producer-port ?producer ?consumer-port ?consumer]
          [latest-production-time ?producer-port ?producer ?time]]
  then [potentially [latest-arrival-time ?consumer-port ?consumer ?time]])


;;; everything having to do with the demo simulator
;;; needs fixing


;;;(defun run-case (ensemble-name input-timings output-timings &key 
;;;                               (do-all-solutions t) 
;;;                               (attack-model nil)
;;;                               (report-while-constructing nil)
;;;                               (report-while-running nil))
;;;  ;; first set up with each model being the normal one
;;;  (let ((*report-out-loud* report-while-constructing))
;;;    (let* ((search-control (set-up-search-control ensemble-name attack-model)))
;;;      (let ((*report-out-loud* report-while-running))
;;;        (with-atomic-action 
;;;          (apply-inputs input-timings)
;;;          (apply-observations output-timings))
;;;        (find-solutions search-control do-all-solutions)))))
;;;
;;;
;;;; (defun get-expected-results (ensemble-name input-timings output-variables)
;;;;   (clear)
;;;;   (let ((ensemble (funcall ensemble-name)))
;;;;     (apply-inputs input-timings)
;;;;     (ask `[component ,ensemble ?component-name ?component]
;;;; 	 #'(lambda (just)
;;;; 	     (declare (ignore just))
;;;; 	     (tell [selected-model ?component normal])))
;;;;     (let ((answers nil))
;;;;       (loop for (variable component) in output-variables
;;;;           do (ask `[and [latest-production-time ,variable ,component ?latest-time]
;;;;                         [earliest-production-time ,variable ,component ?early-time]]
;;;;                   #'(lambda (just)
;;;;                       (declare (ignore just))
;;;;                       (push (list variable component ?early-time ?latest-time) answers))))
;;;;       (nreverse answers))))
;;;; 

(defun parse-observation (predication ensemble)
  (labels ((hack-a-primitive-statement (predication)
	     (let ((statement (predication-statement predication)))
	       (let ((new-statement (loop for thing in statement
					if (listp thing)
					collect (observation-parser ensemble (first thing) (rest thing))
					else collect thing)))
		 (make-predication new-statement))))
	   (hack-a-statement (predication)
	     (let ((statement (predication-statement predication))
		   (predicate (predication-predicate predication)))
	       (cond
		((member predicate '(and or not))
		 (let* ((sub-statements (cdr statement))
			(processed-subs (loop for sub in sub-statements
					    collect  (hack-a-statement sub))))
		   (make-predication `(,predicate ,@processed-subs))))
		(t (hack-a-primitive-statement predication))))))
    (hack-a-statement predication)
    ))

(defmethod observation-parser ((e compound-component) (type (eql 'io)) stuff)
  (destructuring-bind (direction name component-name) stuff
    (io-named e name direction component-name)))

(defmethod observation-parser ((e compound-component) (type (eql 'situation)) stuff)
  (destructuring-bind (before-or-after component-name) stuff
    (situation-named e before-or-after component-name)))

(defmethod observation-parser ((e compound-component) (type (eql 'interval)) stuff)
  (destructuring-bind (before-or-after component-name) stuff
    (interval-named e before-or-after component-name)))

(defun apply-inputs (input-timings)
  (loop for (node component time) in input-timings
        doing (tell `[potentially [earliest-arrival-time ,node ,component ,time]]
                    :justification :premise)
        (tell `[potentially [latest-arrival-time ,node ,component ,time]]
              :justification :premise)))

(defun apply-observations (output-timings)
  (loop for (node component time) in output-timings
        doing (tell `[potentially [earliest-production-time ,node ,component ,time]]
                    :justification :premise)
        (tell `[potentially [latest-production-time ,node ,component ,time]]
              :justification :premise)))

(define-predicate-method (notice-truth-value-change potentially :before) (old-truth-value)
  (when (eql old-truth-value *true*)
    ;; If I'm going out remove me as a justification for the current
    ;; real predication that I support
    (let* ((predication (second (predication-statement self))))
      (let ((old-guy (tell predication :justification :none)))
	(when old-guy 
	  (loop for just in (all-justifications old-guy) 
		doing (multiple-value-bind (mnemonic) (destructure-justification just)
			(when (eql mnemonic 'best-time-finder)
			  (unjustify old-guy just)))))))))

(define-predicate-method (notice-truth-value-change potentially :after) (old-truth-value)
  (declare (ignore old-truth-value))
  (let* ((predication (second (predication-statement self)))
         (type (predication-predicate predication)))
    (with-statement-destructured (port component time) predication
      (declare (ignore time))
      (let ((best-time nil)
            (best-guy nil)
	    (old-best-time nil)
            (old-best-guy nil))
        (block find-current
          (ask `[,type ,port ,component ?his-time]
               #'(lambda (justification)
                   (setq old-best-time ?his-time 
			 old-best-guy (ask-database-predication justification))
		   (return-from find-current (values)))))
	(cond
	  ((and old-best-guy
		(eql :premise (destructure-justification (current-justification old-best-guy))))
	   ;; there was a best guy but he was a premise so leave him alone
	   )
	  (t
	   (setq best-time old-best-time)
	   (ask `[potentially [,type ,port ,component ?new-time]]
		#'(lambda (justification)
		    (when (or (null best-time)
			      (case type
				(earliest-arrival-time (> ?new-time best-time))
				(latest-arrival-time (< ?new-time best-time))
				(earliest-production-time (> ?new-time best-time))
				(latest-production-time (< ?new-time best-time))))
		      (setq best-time ?new-time best-guy (ask-database-predication justification)))))
	   (when best-time
	     (let ((new-guy (tell `[,type ,port ,component ,best-time] :justification :None)))
	       (unless (eql new-guy old-best-guy)
		 (when old-best-guy
		   (unjustify old-best-guy))
		 (tell new-guy :justification `(best-time-finder (,best-guy))))
	       new-guy))))))))