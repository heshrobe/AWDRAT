;;; -*- Mode: common-lisp; Syntax: joshua; Package: awdrat; readtable: joshua -*-

(in-package :awdrat)

;;; the predicate definitions are our vocabulary for describing the world

;;; First a hack to make a pool of assertions that can be cleared in one fell swoop without
;;; affecting other assertions.
;;; This just collects all such assertions and then untells them on demand.
;;; So this is independent of how the assertions are indexed, etc.
;;;
;;; It might have been cuter to do this with the MOP
;;; using a slot in each class.  Problem is that what you'd like to
;;; do is have a class allocated slot.  But you can only access that with an accessor
;;; on the instances, not the class itself.

(defvar *clearable-facts-hashtable* (make-hash-table))

(define-predicate-model separately-clearable-facts-mixin ()
  ())


(define-predicate-method (tell separately-clearable-facts-mixin :after) (truth-value justification)
  (declare (ignore truth-value justification))
  (push self (gethash  (class-of self) *clearable-facts-hashtable*)))

(define-predicate-method (untell separately-clearable-facts-mixin :after) ()
  ;; (declare (ignore pred))
  (setf (gethash (class-of self) *clearable-facts-hashtable*)
    (delete self (gethash (class-of self) *clearable-facts-hashtable*)))
  self)

(defmethod cleanup ((model-name symbol))
  (let ((class (find-class model-name nil))
	(classes-done nil))
    (when class
      (labels ((do-one (sub)
		 (unless (member sub classes-done)
		   (push sub classes-done)
		   (mapc #'untell (gethash sub *clearable-facts-hashtable*))
		   (mapc #'do-one #+allegro (aclmop:class-direct-subclasses sub)
                                  #+sbcl (sb-mop:class-direct-subclasses sub)
                                  ))))
	(when class
	  (do-one class))))))

;;; The idea is that by defining models that are subclasses of separately-clearable-facts-mixin
;;; you get a pool of facts that can be cleared without screwing up other things.
;;; Namely any predicate that is sub-type of that model, will be cleared if you call cleanup
;;; on the model name.
;;; In particular, any per session facts should use the model pams-volatile-facts and any
;;; background type information should not use it.  Then calling (cleanup 'pams-volatile-facts)
;;; will get rid of all the per session facts, so that you can do a new session.

(define-predicate-model volatile-facts ()
  (separately-clearable-facts-mixin default-predicate-model))

;;; Notice that these are background facts, always true and therefore not volatile-facts
(eval-when (:compile-toplevel :load-toplevel :execute)
  (define-predicate cost-of-failure (method cost))
  (define-predicate state-of (device state probability)))

(defvar *service-hash-table* (make-hash-table))

(defclass service-description ()
  ((name :accessor service-name :initarg :name)
   (goal :accessor goal :initarg :goal :initform nil)
   (features :accessor features :initarg :features :initform nil)
   (feature-defaults :accessor feature-defaults :initarg :feature-defaults :initform nil)
   (feature-map :accessor feature-map :Initform nil)))

(defmacro define-service ((name goal) &body features-and-values)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (Let ((description (make-instance 'service-description
			  :goal ,goal
			  :name ', name)))
	  (loop for (feature values default) in ',features-and-values
	      do (push feature (features description))
		 (push (list feature default) (feature-defaults description))
		 (push (cons feature values) (feature-map description)))
	  (setf (features description) (nreverse (features description)))
	  (setf (feature-map description) (nreverse (feature-map description)))
	  (setf (gethash ',name *service-hash-table*) description)
	  description)))

(defun get-service-features (service-name)
  (let ((entry (or (gethash service-name *service-hash-table*)
		   (error "No such service ~a" service-name))))
    (features entry)))

(defun get-service-goal (service-name)
  (let ((entry (or (gethash service-name *service-hash-table*)
		   (error "No such service ~a" service-name))))
    (goal entry)))

(defun get-service-feature-map (service-name)
  (let ((entry (or (gethash service-name *service-hash-table*)
		   (error "No such service ~a" service-name))))
    (feature-map entry)))

; ;; this is the thing which connects a service to a method
; (define-predicate method-for (service goal features method resources components other-parameters sub-services))

; ;; syntactic sugar for defining a method
; ;; turns it into a rule that matches the service statement to the method
; ;; and its resources
; (defmacro define-method (method-name &key service features goal
; 					  components
; 					  resources resource-constraints
; 					  context other-parameters
; 					  sub-services
; 					  plan prerequisite)
;   (declare (ignore plan))
;   (let* ((entry (or (gethash service *service-hash-table*)
; 		    (error "No such service ~a" service)))
; 	 (service-features (features entry))
; 	 (defaults (feature-defaults entry)))
;     (setq features (loop for feature in service-features
; 		       for required-feature = (second (assoc feature features))
; 		       for default-feature = (second (assoc feature defaults))
; 		       collect (list feature (or required-feature default-feature))))
;     `(progn
;        (defrule ,method-name (:backward)
; 	 then [method-for ,service ,goal ,features ,method-name ,resources ,components ,other-parameters ,sub-services]
; 	 if [and ,@context ,@prerequisite ,@resource-constraints
; 		 ;; might like somthing like
; 		 ;; (process-sub-goals ,sub-services)
; 		 ;; ,@ final-constraints
; 		 ])
;        )))


(define-predicate method-for (service
			      goal
			      feature-alist ;; used as in/out
			      current-resource-alist ;; the accumulated use of resources when I'm called.  An in parameter.
			      current-resource-cost ;; similar for resource cost
			      current-resource-probability ;; similar for resource probability
			      updated-resource-alist ;; the use of resources after satisyfing this goal.  An out parameter
			      updated-resource-cost ;; similar
			      updated-resource-probability ;; similar
			      cutoff-function ;; If non-nil, the guy to call to see if you should keep building this plan.
			      plan ;; A keyword list structure representing the plan
			      top-method ;; the top-level method
			      ))

(defmacro define-method (method-name
			 &key service
			      goal
			      features
			      context
			      prerequisite
			      resources
			      resource-constraints
			      resource-costs
			      components
			      sub-services
			      plan)
  (let* ((entry (or (gethash service *service-hash-table*)
		    (error "No such service ~a" service)))
	 (service-features (features entry))
	 (defaults (feature-defaults entry))
	 (resource-cost-alist (cons 'list (loop for plist in resource-costs
					      collect (cons 'list plist))))
	 (features-for-answer nil))
    (when (null goal) (setq goal `(logic-variable-maker \?goal)))
    (setq features (loop for feature in service-features
		       for required-feature = (second (assoc feature features))
		       for default-feature = (second (assoc feature defaults))
		       collect (list feature (or required-feature default-feature))))
    (setq features-for-answer
      (loop for (key value) in features
	  for quoted-value = (if (logic-variable-maker-p value) value `',value)
	  collect `(list ',key ,quoted-value)))
    `(progn
       (defrule ,method-name (:backward)
	 then [method-for ,service ,goal ,features
			  ?current-resource-alist ?current-resource-cost ?current-resource-probability
			  ?updated-resource-alist ?updated-resource-cost ?updated-resource-probability
			  ?cutoff-function ?plan ?top-method]
	 if [and ,@context ,@prerequisite ,@resource-constraints
		 (multiple-value-bind (resource-alist-so-far resource-cost resource-probability)
		     (update-resource-costs ,resource-cost-alist ',components
					    ?current-resource-alist ?current-resource-cost ?current-resource-probability)
		   (when (or (null ?cutoff-function)
			     (null (funcall ?cutoff-function ?top-method
					    resource-cost resource-probability resource-alist-so-far)))
		     (when (unbound-logic-variable-p ?top-method) (unify ?top-method ',method-name))
		     ,@(if sub-services
			   `((unify ?resource-alist-1 resource-alist-so-far)
			     (unify ?resource-cost-1 resource-cost)
			     (unify ?resource-probability-1 resource-probability))
			 `((unify ?updated-resource-alist resource-alist-so-far)
			   (unify ?updated-resource-cost resource-cost)
			   (unify ?updated-resource-probability resource-probability)))))
		 ,@(when sub-services
		     (loop for (sub-service goal alist plan . constraints) = (pop sub-services)
			 for previous from 1
			 for next from 2
			 for current-resource-alist = (lv-maker 'resource-alist previous)
			 for current-resource-cost = (lv-maker 'resource-cost previous)
			 for current-resource-probability = (lv-maker 'resource-probability previous)
			 for last? = (null sub-services)
			 for next-resource-alist = (if last? '(logic-variable-maker \?updated-resource-alist) (lv-maker 'resource-alist next))
			 for next-resource-cost = (if last? '(logic-variable-maker \?updated-resource-cost) (lv-maker 'resource-cost next))
			 for next-resource-probability = (if last? '(logic-variable-maker \?updated-resource-probability)
							   (lv-maker 'resource-probability next))
			 collect `(predication-maker
				   '(method-for ,sub-service ,goal ,(make-source-alist-for-service sub-service alist)
				     ,current-resource-alist ,current-resource-cost ,current-resource-probability
				     ,next-resource-alist ,next-resource-cost ,next-resource-probability
				     ?cutoff-function ,plan ?top-method))
			 when constraints
			 append constraints
			 until (null sub-services)))
		 (unify ?plan
			(list ',method-name
			      :cost (- ?updated-resource-cost ?current-resource-cost)
			      :resources (list ,@resources)
			      :components ',components
			      :features (list ,@features-for-answer)
			      :sub-plan ,plan))
		 ]))))



(defmacro define-configuration (&rest stuff)
  `(define-method ,@stuff))

(defmacro define-component (component-name &key resource-consumption reliability)
  (let ((resource-stmts (loop for (resource-name resource-amount) in resource-consumption
			    collect `(tell `[consumes-resource ,',component-name ,',resource-name ,',resource-amount])))
	(reliability-statements (loop for (property value probability) in reliability
				    collect `(tell `[reliability-under-condition ,',component-name ,',property ,',value ,',probability]))))
    `(eval-when (:load-toplevel :execute)
       ,@resource-stmts
       ,@reliability-statements
       )))


(define-predicate cost-of (resource-type thing key value cost))
(define-predicate cost-per-unit (category cost))
(define-predicate consumes-resource (component category amount))
(define-predicate environment-condition (property value))
(define-predicate reliability-under-condition (component property value probability))
(define-predicate resource-available (resource amount))
(define-predicate resource-type (resource category))

(defmacro resource-available (resource amount)
  `(tell `[resource-available ,',resource ,',amount]))

(defun resources-available ()
  (let ((alist nil))
    (ask [resource-available ?resource ?amount]
	 #'(lambda (ignore)
	     (declare (ignore ignore))
	     (push (list ?resource ?amount) alist)))
    alist))

(defmacro resource-cost-per-unit (category cost)
  `(tell `[cost-per-unit ,',category ,',cost]))

(defmacro environment (&rest pairs)
  `(eval-when (:load-toplevel :execute)
     ,@(loop for (property value) in pairs
	  collect `(tell `[environment-condition ,',property ,',value]))))

(defun aggregate-cost (category amount)
  (ask `[cost-per-unit ,category ?cost-per-unit]
       #'(lambda (just)
	   (declare (ignore just))
	   (return-from aggregate-cost
	     (* ?cost-per-unit amount))))
  0)

(defmacro uses-resource (component resource-type amount)
  `(tell `[consumes-resource ,',component ,',resource-type ,',amount]))

(defun component-consumption (component)
  (let ((alist nil))
    (ask `[consumes-resource ,component ?category ?amount]
	 #'(lambda (ignore)
	     (declare (ignore ignore))
	     (push (list ?category ?amount) alist)))
    alist))

(defvar *infinity* 1e6)

(defun cost-of-resource (resource plist)
  (ask `[resource-type ,resource ?resource-type]
       #'(lambda (ignore)
	   (declare (ignore ignore))
	   (let ((total-cost 0))
	     (loop for (key value) on plist by #'cddr
		 do (ask `[cost-of ?resource-type ,resource ,key ,value ?cost]
			 #'(lambda (ignore)
			     (declare (ignore ignore))
			     (incf total-cost ?cost))))
	     (return-from cost-of-resource total-cost))))
  0)

;; a test-case function which finds a method for the present-information service
(defvar *trace-utility-calc* nil)

(defmacro trace-utility-calc (format-string &rest args)
  `(when *trace-utility-calc*
     (format *trace-utility-calc*
	     ,format-string ,@args)))

(defun utility-trace (&optional (on-or-off 'on))
  (if (eql on-or-off 'on)
      (setq *trace-utility-calc* t)
    (setq *trace-utility-calc* nil)))

(defun utility-function-for-service (service-name preferences max-value)
  (make-utility-bounds-function
   (get-service-feature-map service-name)
   preferences
   max-value))

(defun is-working (resource)
  (ask `[state-of ,resource working ?probability]
       #'(lambda (just)
	   (declare (ignore just))
	   (return-from is-working (list t ?probability))))
  (list t 1))

(defrule working-in-condition (:backward)
  then [state-of ?resource working ?probability]
  if [and [reliability-under-condition ?resource ?property ?value ?probability]
	  [environment-condition ?property ?value]
	  ]
  )

(defun cost-of-failure (method)
  (ask `[cost-of-failure ,method ?cost]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (return-from cost-of-failure ?cost)))
  0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Find Best Method for Service
;;;
;;; This finds the best method taking into account:
;;;  The benefit delivered
;;;  The cost of the resources
;;;  Limits on the amounts of specific resources that can be used
;;;  The possiblity that some resource isn't working and could cause the method to fail
;;;
;;; The utility-function is supposed to be the type that returns max min bounds
;;; this is always applied to the the top-level parameter alist
;;;  since this is the value of the whole solution
;;;
;;; This builds a cutoff continuation that is used to cut-off a sub-tree exploration
;;;  If it already consumes too much of some resource or
;;;  If it's clearly worse than the best solution so far
;;;  this is equivalent to its max utility - resource cost incurred so far is worse than the best
;;;   conditioned by the probability of failure and failure cost for the top-level method
;;;
;;; It also builds a continuation for when a total solution is reached
;;;  this captures the best solution so far
;;;
;;; The main recursion is a couple of functions below
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-best-method-for-service (service-name utility-function
				     &key feature-requirements resource-budget-alist goal do-cutoffs?)
  (let ((best-value nil) (best-method nil) (best-raw-utility nil) (best-expected-utility nil)
	(alist (make-alist-for-service service-name feature-requirements))
	(all-methods nil)
	(no-goods nil)
	(number-of-cutoff-checks 0)
	(number-considered 0) (number-of-resource-cutoffs 0) (number-of-utility-cutoffs 0))
    (unless goal
      (setq  goal (ji:make-unbound-logic-variable 'goal)))
    (labels ((cut-off? (top-method total-resource-cost joint-probability resource-consumption-alist)
	       ;; This returns nil if you should cutoff t if there's a chance this could be better
	       ;; also checks that you haven't exceeded resource budgets
	       (incf number-of-cutoff-checks)
	       (cond
		((exceeds-resource-limit resource-consumption-alist)
		 (incf number-of-resource-cutoffs)
		 (trace-utility-calc "~%Cutting off for excessive resources: ~\
                                        ~10t~{~a~^,~}~\
                                        ~10t~{~a~^,~}"
				     resource-consumption-alist
				     resource-budget-alist)
		 t)
		((null best-value) nil)
		(t (multiple-value-bind (his-best-possible no-good)
		       (expected-net-benefit top-method total-resource-cost joint-probability
					     alist utility-function
					     (when do-cutoffs? best-value)
					     no-goods)
		     (cond
		      (his-best-possible
		       ;; he didn't get cutoff, return nil for no cutoff
		       nil)
		      (t ;; he got cutoff
		       (incf number-of-utility-cutoffs)
		       (when no-good
			 (push no-good no-goods))
		       (trace-utility-calc "~%Cutting off because his value is~\
                                               ~%  worse than best ~a~\
                                               ~%  provided by ~{~a~^~%  ~}"
					   best-value best-method)
		       t))))))
	     (exceeds-resource-limit (resource-consumption-alist)
	       (loop for (resource amount-used) in resource-consumption-alist
		   for entry = (assoc resource resource-budget-alist)
		   when entry
		   do (let ((amount-allowed (second entry)))
			(when (> amount-used amount-allowed)
			  (return t)))
		   finally (return nil))))
      (ask `[method-for ,service-name ,goal ,alist
			nil 0 1		;resource alist, resource cost, resource-probability
			?final-resource-alist ?final-resource-cost ?final-resource-probability
			,(when do-cutoffs? #'cut-off?) ?plan ?top-method]
	   #'(lambda (backward-support)
	       (declare (ignore backward-support))
	       (incf number-considered)
	       (multiple-value-bind (tradeoff no-good raw-utility expected-utility)
		   (expected-net-benefit ?top-method
					 ?final-resource-cost ?final-resource-probability alist
					 utility-function
					 (when do-cutoffs? best-value) no-goods)
		 (let ((final-plan (copy-object-if-necessary ?plan)))
		   (when tradeoff (push (list tradeoff final-plan raw-utility expected-utility) all-methods))
		   (cond
		    ((null tradeoff)
		     ;; he cutoff, no answer here
		     (when no-good (push no-good no-goods)))
		    ((or (null best-value) (> tradeoff best-value))
		     (setq best-value tradeoff
			   best-raw-utility raw-utility
			   best-expected-utility expected-utility
			   ;; list because there may be several equally good plans
			   best-method (list final-plan)))
		    ((and best-value (= tradeoff best-value))
		     (push final-plan best-method)))))
	       ))
      (values best-method
	      best-value
	      best-raw-utility
	      best-expected-utility
	      (collapsed-score-list all-methods)
	      number-considered
	      number-of-cutoff-checks
	      number-of-utility-cutoffs
	      number-of-resource-cutoffs
	      no-goods
	      ))))

(defun collapsed-score-list (list-of-pairs)
  (let ((alist nil))
    (loop for (score . stuff) in list-of-pairs
	for entry = (assoc score alist :test #'=)
	unless entry
	do (setq entry (list score 0 nil)) ;0 is count
	   (push entry alist)
	unless (member stuff (third entry) :test #'equal)
	do (push stuff (third entry)) (incf (second entry)))
    (sort alist #'> :key #'first)))

(defun make-alist-for-service (service-name feature-requirements)
  (if (unbound-logic-variable-p feature-requirements)
      feature-requirements
    (let* ((features (get-service-features service-name)))
      (loop for feature in features
	  for requirement = (assoc feature feature-requirements)
	  if requirement
	  collect requirement
	  else collect (list feature (ji:make-unbound-logic-variable feature))))))

;;; The assumption is that the utility function returns max-value
;;; the expected-cost-of-failure is the method's cost of failure weighted by probability of failure
;;;  which is 1 - probability that all the resources work
;;; expected-utility is the utility weighted by the probability that all the resources work
;;; your pay for the resources in all cases so it's not weighted by probability

(defun expected-net-benefit (method resource-cost joint-resource-probability alist utility-function
			     &optional current-best-value
				       nogoods)
  (let ((expected-failure-cost (* (- 1 joint-resource-probability) (cost-of-failure method))))
    (multiple-value-bind (raw-utility no-good)
	(funcall utility-function (copy-object-if-necessary alist) current-best-value nogoods)
      ;; the utility function can cutoff, returning nil
      (let ((expected-utility (when raw-utility (* joint-resource-probability raw-utility ))))
	(trace-utility-calc "~%Utility calc: raw: ~a, resource-cost ~a, fail cost: ~a, expected utility ~a"
			    raw-utility resource-cost expected-failure-cost expected-utility)
	(if expected-utility
	    (values (- (float expected-utility) (float resource-cost) expected-failure-cost)
		    nil			;return value for nogood
		    raw-utility expected-utility)
	  (values nil no-good)
	  )))))

;;; This is the user entry point
(defun choose-a-configuration (service-name request-name
			       &key (hard-constraints nil)
				    (preferences nil)
				    (resource-limits nil)
				    (max-utility nil)
				    (goal nil)
				    (do-cutoffs? nil))
  (declare (ignore request-name))
  (let ((utility-function
	 (utility-function-for-service
	  service-name
	  preferences
	  (or max-utility
	      (loop for (resource-name resource-limit) in resource-limits
		  sum (aggregate-cost resource-name resource-limit))))))
    (find-best-method-for-service
     service-name
     utility-function
     :goal goal
     :feature-requirements hard-constraints
     :resource-budget-alist resource-limits
     :do-cutoffs? do-cutoffs?
     )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Find Methods for service does the hierarchical search
;;; It iterates for each top level method for the service (this is the or node)
;;;   fetchings the resources
;;;   binding the top-level parameters in alis
;;;   and fetching the service requirements (sub-goals)
;;; It then checks whether this solution can be ignored
;;;   the idea is that the utility function is a bounds function which will return a max utility
;;;   over all unbound service-parameters
;;;   and we can then calculate an expected-net-benefit on that
;;;    as we pursue sub-services, the number of resources can only go up (increasing cost)
;;;    and the number of bound-parameters can only go up, tightening bounding (decreasing max utility)
;;;   Thus is expected-net-benefit is less than the best found so far, it isn't worth pursuing this line
;;;    since we're already worse and we can only get worse.
;;;  It then iterates over the sub-services requirements (this is the and node)
;;;   recursively calling itself for each
;;;    this iteration is done by recursion because each call is a generator that calls the continuation
;;;    for each possible solution
;;;  For each complete solution (resources and sub-methods) it calls the continuation
;;;
;;; The cutoff function is called with the method name, resource-cost, joint-probability
;;;  it has access to the utility function and the alist as captured closure variables
;;;  so it does little more than compute expected-net-benefit and threshold on that
;;;
;;; The continuation is called once for each solution with:
;;;   the cost-of-all-resources used by that method
;;;   the joint probability that the resources all work
;;;   the method name
;;;   the resources used directly by that method
;;;   the sub-services alist for this method
;;;    which is a set of quartets one for each sub-service requirement
;;;    including the method name, goal pattern, resources and sub-services
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (defun find-methods-for-service (service-name goal alist other-parameters
; 				 continuation
; 				 cutoff-function
; 				 resource-cost-so-far
; 				 resource-probability-so-far
; 				 resource-alist-so-far
; 				 ;; Top-method is null on the top-level call but not at any other time
; 				 &optional top-method )
;   (let ((valid-methods 0) (methods-with-working-resources 0))
;     (unless other-parameters
;       (setq  other-parameters (ji:make-unbound-logic-variable 'parameters)))
;     (unless goal
;       (setq  goal (ji:make-unbound-logic-variable 'goal)))
;     (ask `[method-for ,service-name ,goal ,alist ?my-method ?my-resources ?my-components ,other-parameters ?sub-services]
; 	 #'(lambda (bs)
; 	     (declare (ignore bs))
; 	     (trace-utility-calc "~2%Trying method ~a for ~a" ?my-method service-name)
; 	     (incf valid-methods)
; 	     (let ((cummumlative-resource-cost resource-cost-so-far)
; 		   (cummulative-resource-probability resource-probability-so-far)
; 		   (resource-alist-so-far (copy-tree resource-alist-so-far)))
; 		 (loop for r in ?my-resources
; 		     for (value probability) = (is-working r)
; 		     if (null value)
; 		     do (return-from find-methods-for-service (values))
; 		     else do (incf cummumlative-resource-cost (cost-of-resource r))
; 			  (setq cummulative-resource-probability (* cummulative-resource-probability probability)))
; 		 (incf methods-with-working-resources)
; 		 (loop for component in ?my-components
; 		     do (loop for (category amount) in (component-consumption component)
; 			    for entry = (assoc category resource-alist-so-far)
; 			    for cost = (aggregate-cost category amount)
; 			    do (incf cummumlative-resource-cost cost)
; 			    if entry
; 			    do (incf (second entry) amount)
; 			    else do (push (list category amount) resource-alist-so-far)))
; 		 (loop for component in ?my-components
; 		     for (value probability) = (is-working component)
; 		     if (null value)
; 		     do (return-from find-methods-for-service (values))
; 		     else do (setq cummulative-resource-probability (* cummulative-resource-probability probability)))
; 		 (trace-utility-calc "~%Resources ~a~% Resource consumption ~{~a~^,~}~% Resource cost ~a ~% Resource Reliability ~a"
; 				     ?my-resources resource-alist-so-far cummumlative-resource-cost
; 				     cummulative-resource-probability)
; 		 (cond
; 		  ;; if we should cutoff there's nothing to do
; 		  ((funcall cutoff-function (or top-method ?my-method)
; 			    cummumlative-resource-cost cummulative-resource-probability
; 			    resource-alist-so-far
; 			    (copy-object-if-necessary ?my-resources)
; 			    (copy-object-if-necessary ?sub-services)))
; 		  ((null ?sub-services)
; 		   ;; if there are no sub-services, we're done, call our continuation
; 		   (funcall continuation
; 			    cummumlative-resource-cost cummulative-resource-probability resource-alist-so-far
; 			    (copy-object-if-necessary ?my-method)
; 			    (copy-object-if-necessary ?my-resources)
; 			    nil))
; 		  ;; there are sub-services, start the iteration to find solutions for those
; 		  ;; as long as we aren't already cutoff
; 		  (t
; 		   (labels
; 		       ((do-next-subservice (cost-so-far probability-so-far resource-alist-so-far
; 					     sub-services-left sub-services-done top-method)
; 			  (destructuring-bind  (sub-service-name sub-service-goal his-alist other-params &rest constraints)
; 			      (first sub-services-left)
; 			    (setq his-alist (make-alist-for-service sub-service-name his-alist))
; 			    (find-methods-for-service
; 			     sub-service-name sub-service-goal his-alist other-params
; 			     #'(lambda (his-resource-cost his-probability his-resource-alist
; 					his-method-name his-resources his-sub-methods)
; 				 (setq sub-services-done (cons (list his-method-name his-resources his-sub-methods)
; 							       sub-services-done)
; 				       sub-services-left (cdr sub-services-left))
; 				 (mapc #'eval constraints)
; 				 (if (null sub-services-left)
; 				     ;; no more sub-goals, pass back the answer
; 				     (funcall continuation
; 					      his-resource-cost his-probability his-resource-alist
; 					      his-method-name his-resources sub-services-done)
; 				   ;; more sub-goals to satisfy
; 				   (do-next-subservice his-resource-cost his-probability his-resource-alist
; 						       sub-services-left sub-services-done top-method)))
; 			     cutoff-function
; 			     cost-so-far
; 			     probability-so-far
; 			     resource-alist-so-far
; 			     top-method))))
; 		     (do-next-subservice resource-cost-so-far cummulative-resource-probability resource-alist-so-far
; 					 ?sub-services nil (or top-method ?my-method))))))))
;     (trace-utility-calc "~%~d methods considered, ~d methods with working resources "
; 			valid-methods methods-with-working-resources)
;     )
;   )




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; New approach
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is going to be a very large relationship because it's going to be used to pass along the cummulative
;;; resource consumption going down and then to pass it back up.  To be specific as we do down a sub-goal we pass it
;;; the resource consumption so far.  It solves the subgoal and returns the resource consumption for it and all its subgoals.
;;; We then pass this cummulative value to our next subgoal, etc.  So there's and in and out value for each of these.

;;; Possible modifications: Instead of returning resources, other parameters, components, sub-services
;;; return a single plan structure embodying all of those.

;;; In  a top level call:
;;;   the cummulative resource alist is nil
;;;   the cummulative resource cost is 0
;;;   the cummulative resource probability is 1

(defun update-resource-costs (my-resources my-components resource-alist-so-far cummulative-resource-cost cummulative-resource-probability)
  ;; we're going to side effect this alist and it's shared with other possible branches
  ;; so copy it first.
  (setq resource-alist-so-far (copy-tree resource-alist-so-far))
  (loop for (r . plist) in my-resources
      for (value probability) = (is-working r)
      if (null value)
      do (return-from update-resource-costs (values))
      else do (incf cummulative-resource-cost (cost-of-resource r plist))
	   (setq cummulative-resource-probability (* cummulative-resource-probability probability)))
  ;; (incf methods-with-working-resources)
  (loop for component in my-components
      do (loop for (category amount) in (component-consumption component)
	     for entry = (assoc category resource-alist-so-far)
	     for cost = (aggregate-cost category amount)
	     do (incf cummulative-resource-cost cost)
	     if entry
	     do (incf (second entry) amount)
	     else do (push (list category amount) resource-alist-so-far)))
  (loop for component in my-components
      for (value probability) = (is-working component)
      if (null value)
      do (return-from update-resource-costs (values))
      else do (setq cummulative-resource-probability (* cummulative-resource-probability probability)))
  (trace-utility-calc "~%Resources ~a~% Resource consumption ~{~a~^,~}~% Resource cost ~a ~% Resource Reliability ~a"
		      my-resources resource-alist-so-far
		      cummulative-resource-cost
		      cummulative-resource-probability)
  (values resource-alist-so-far
	  cummulative-resource-cost
	  cummulative-resource-probability))

(defun lv-maker (name index)
  (let ((name (intern (format nil "?~a-~d" (string-upcase (string name)) index))))
    `(logic-variable-maker ,name)))


(defparameter *anonymous-counter* 1)

(defun make-source-alist-for-service (service-name partial-alist)
  (if (logic-variable-maker-p partial-alist)
      partial-alist
    (let* ((features (get-service-features service-name)))
      (loop for feature in features
	  for index from 1
	  for requirement = (assoc feature partial-alist)
	  if requirement
	  collect requirement
	  else collect (list feature (lv-maker "ANONYMOUS" *anonymous-counter*))))))

(defun print-plan (plan &optional (stream *standard-output*) (indent-level 0))
  (let* ((name (first plan))
	 (plist (rest plan))
	 (cost (getf plist :cost))
	 (resources (getf plist :resources))
	 (components (getf plist :components))
	 (features (getf plist :features))
	 (sub-plan (getf plist :sub-plan))
	 (combination (first sub-plan))
	 (sub-plans (rest sub-plan))
	 )
    (unless (eql combination :atomic)
      (format stream
	      "~%~vtName: ~a~%~vtResources: ~a~%~vtComponents: ~a~%~vtCost: ~d"
	      indent-level name
	      indent-level resources
	      indent-level components
	      indent-level cost)
      (format stream "~%~vtFeatures:" indent-level)
      (loop with indent-level = (+ indent-level 5)
	  for (key value) in features
	  do (format stream "~%~vt~a ~a" indent-level key value)))
    (case combination
     (:atomic
      (format stream "~%~vtName: ~a ~%~vtParameters:" indent-level name indent-level)
      (loop with indent-level = (+ indent-level 5)
	  for (key value) on sub-plans by #'cddr
	  do (format stream "~%~vt~a ~a"
		     indent-level key value)))
     ((:parallel :sequential)
      (format stream "~%~vtSubplan: ~a" indent-level combination)
      (loop for plan in sub-plans
	  do (terpri stream)
	     (print-plan plan stream (+ indent-level 2))))
     (otherwise (format stream "~%~vtSubplan: Combination: ~a" indent-level combination)
	(loop for plan in sub-plans
	    do (terpri stream)
	       (print-plan plan stream (+ indent-level 2)))))))

(defun extract-primitive-actions (plan)
  (let ((actions nil))
    (labels ((do-sub-plan (plan)
	     (let* ((plist (rest plan))
		    (sub-plan (getf plist :sub-plan))
		    (combination (first sub-plan))
		    (sub-plans (rest sub-plan)))
	       (cond
		((eql combination :atomic) (push sub-plans actions))
		(t (loop for plan in sub-plans
		       do (do-sub-plan plan)))))))
      (do-sub-plan plan))
    (nreverse actions)))





#|

(defrule method-name (:backward)
  Then [new-method-for service [goal] canonical-feature-alist
		       ?current-resource-alist ?current-resource-cost ?current-resource-probability
		       ?updated-resource-alist ?updated-resource-probability ?updated-resource-cost
		       ?plan ?cutoff-function ?top-method]
  If [and
      ;; this gets our resource variables bound
      <prerequisites>
      <resource-constraints>
      (when (unbound-logic-variable-p ?top-method)
	(unify ?top-method method-name))
      (multiple-value-bind (alist-so-far resource-cost resource-probability)
	  (update-resource-costs (list resources) (list components)
				 ?current-resource-alist ?current-resource-cost ?current-resource-probability)
	(when (or (null ?cutoff-function)
		  (null (funcall ?cutoff-function ?top-method
				 resource-cost resource-probability alist-so-far)))
	  (unify ?resource-alist-1 alist-so-far)
	  (unify ?current-resource-1 resource-cost)
	  (unify ?resource-probability-1 resource-probability)
	  (succeed)))
      [new-method-for sub-service-1 [sub-goal-1] ?alist-1
		      ?resource-alist-1 ?resource-cost-1 ?resource-probability-1
		      ?resource-alist-2 ?resource-cost-2 ?resource-probability-2
		      ?plan-1 ?cutoff-function]
      <constraints-for-sub-service-1>
      [new-method-for sub-service-2 [sub-goal-2] ?alist-2
		      ?resource-alist-2 ?resource-cost-2 ?resource-probability-2
		      ?resource-alist-3 ?resource-cost-3 ?resource-probability-3
		      ?plan-2 ?cutoff-function]
      <constraints-for-sub-service-2>
      ...
      <constraints-for-sub-service-n-1>
      [new-method-for sub-service-n-1 [sub-goal-n] ?alist-n
		      ?resource-alist-n ?resource-cost-n ?resource-probability-n
		      ?update-resource-alist ?updated-resource-cost ?update-resource-probability
		      ?plan-n ?cutoff-function]
      <constraints-for-sub-service-n>
      <code to build ?plan>
      ]
  )

|#
