;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat ; readtable: joshua -*-

(in-package :awdrat)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (export (intern (string-upcase "Label-name") :ideal) :ideal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The basic data model
;;;
;;; Components:
;;;  Have two parts: The interface and the implementation
;;;   Interface: input and output ports as well pre-, post- and invariant conditions
;;;   Implementation: Component parts with their ports
;;;                   Splits and Joins with their branches and ports
;;;                    control-flows data-flows connecting all of the above.
;;;  A Behavior model can be provided for the component type
;;;                     allowing simulation without decompositoin
;;;                   (Actually there can be several of these allowing a run-time implementation choice)
;;;
;;;   When the implementation is instantiated to represent the innards of a component there are
;;;     assertions made to represent dataflow and control flow
;;;
;;; Dataflows link ports of components within an ensemble.
;;;      And across the implementation boundary as well (input-input output-output links)
;;;
;;; Control flows link an output branch of a component to another component
;;;                    or a component to an input branch of a join
;;;    for notational simplicity a component that is neither a branch or join is thought of
;;;                   having a  branches called "before" and "after", allowing after-before, after-after
;;;                    and before-before control flow constraints.  Initially we'll only worry about
;;;                        after-before links
;;;
;;; Splits and Joins own a set of named branches
;;;  control flows go between branches of a split to a component and these may only be after-before
;;;  control flows go between normal components to a branch of a split and these are only after-before
;;;  data and control flows to into branches of a join
;;;    the control flow are always after-before
;;;    the data flows are ?-before
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; structural model
(define-predicate situation (component before-or-after situation) (ltms:ltms-predicate-model))
(define-predicate interval (component span interval) (ltms:ltms-predicate-model))

(define-predicate component (parent-ensemble component-name component) (ltms:ltms-predicate-model))
(define-predicate port (direction component port-name ) (ltms:ltms-predicate-model))
(define-predicate state-variable (component variable-name) (ltms:ltms-predicate-model))
(define-predicate control-port (direction component port-name) (ltms:ltms-predicate-model))

;;; This can be split, join, primitive of the name of an ensemble
(define-predicate component-type (component type) (ltms:ltms-predicate-model))

;;; This is the name of the associated plan or procedure
(define-predicate behavior (component type) (ltms:ltms-predicate-model))

(define-predicate dataflow (producer-port producer consumer-port consumer) (ltms:ltms-predicate-model))
(define-predicate controlflow (producer-brancy producer consumer-branch consumer)
  (ltms:ltms-predicate-model))


;;; This relates a branch to its split of join
(define-predicate branch-of (name split-or-join branch) (ltms:ltms-predicate-model))

;;; underlying infrastructure model
(define-predicate resource (ensemble resource-name resource) (ltms:ltms-predicate-model))
(define-predicate resource-type-of (resource resource-type) (ltms:ltms-predicate-model))

;;; dynamic assertions about values at the components' ports
(define-predicate input (port component value) (ltms:ltms-predicate-model))
(define-predicate output (port component value) (ltms:ltms-predicate-model))
(define-predicate data-type-of (object type) (ltms:ltms-predicate-model))
(define-predicate state-variable-value (object variable value) (ltms:ltms-predicate-model))

(define-predicate-method (expand-forward-rule-trigger data-type-of) (support-variable-name truth-value context bound-variables)
  (declare (ignore context bound-variables))
  (unless (eql truth-value +true+)
    (error "The rule pattern ~s does not have a truth-value of true" self))
  (with-predication-maker-destructured (object type) self
    `(:procedure
      (typep ,object ',type)
      ,support-variable-name
      ,(list object type))))

(define-predicate-method (ask-data data-type-of :around) (truth-value continuation)
  (with-statement-destructured (object type) self
    (cond
     ;; if either variable is unbound just do the normal thing
     ((or (unbound-logic-variable-p object) (unbound-logic-variable-p type))
      (call-next-method))
     ;; but if both are bound we can just use typep to check
     ;; we assert the fact in the database and return a normal
     ;; justification for something in the database
     ((and (eql truth-value +true+)
	   (typep object type))
      (let ((assertion (tell `[data-type-of ,object ,type] :justification :premise)))
	(stack-let ((backward-support (list self +true+ assertion)))
		   (funcall continuation backward-support))))
     ((and (eql truth-value +false+)
	   (not (typep object type)))
      (let ((assertion (tell `[not [data-type-of ,object ,type]] :justification :premise)))
	(stack-let ((backward-support (list self +false+ assertion)))
		   (funcall continuation backward-support))))
     )))

;;; dynamic assertions about controlflow status
(define-predicate controlflow-satisfied (controlflow) (ltms:ltms-predicate-model))
(define-predicate selected-branch (split-or-join branch) (ltms:ltms-predicate-model))

;;; dynamic assertions about execution interpretation
;;; status can be ready started completed (all can be true, once it's ready it stays ready).
(define-predicate execution-status (component status) (ltms:ltms-predicate-model))
(define-predicate event-for (event-name entry-exit component effect-on-component)
  (ltms:ltms-predicate-model))
;;; This asserts the event names in second argument (a set)
;;; are all allowable and that they are the only allowable events
;;; other than the entry and exit events
(define-predicate allowable-events-for (component set-of-events) (ltms:ltms-predicate-model))

(define-predicate autostart (component) (ltms:ltms-predicate-model))
(define-predicate event-map (event-name entry-or-exit component input-or-output argument-names) (ltms:ltms-predicate-model))
(define-predicate no-bad-events (component) (ltms:ltms-predicate-model))
(define-predicate bad-event-detected (event time component event-args) (ltms:ltms-predicate-model))
(define-predicate all-inputs-present (component) (ltms:ltms-predicate-model))
(define-predicate all-outputs-present (component) (ltms:ltms-predicate-model))
(define-predicate all-controlflows-satisfied (component) (ltms:ltms-predicate-model))
(define-predicate all-terminal-controlflows-satisfied (component) (ltms:ltms-predicate-model))
(define-predicate prerequisites-satisfied (component) (ltms:ltms-predicate-model))

;;; static and dynamic assertions about "mode's"
(define-predicate possible-model (component model) (ltms:ltms-predicate-model))




;;; assertions about attack exploits and vulnerabilities
(define-predicate attack (component attack-name attack-type) (ltms:ltms-predicate-model))
(define-predicate has-vulnerability (resource vulnerability) (ltms:ltms-predicate-model))
(define-predicate vulnerability-enables-attack (vulnerability attack) (ltms:ltms-predicate-model))
(define-predicate resource-might-have-been-attacked (resource attack) (ltms:ltms-predicate-model))
(define-predicate attack-implies-compromised-mode (attack resource mode likelihood) (ltms:ltms-predicate-model))

;;; mixin for time-tagged assertions

(define-predicate-model situation-tagged-mixin
    ()
  ()
  )

(define-predicate-model modeling-mixin
    ()
  (situation-tagged-mixin ltms:ltms-predicate-model))

;;; A useful predicate for writing models

(define-predicate is-equal (thing1 thing2 situation) (modeling-mixin))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;  Sets and Maps
;;; Assertions and classes
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An immutable set with fixed membership specified at make-instance time
;;; useful for the set of allowable events
;;; As assertions this says that the members are exactly those specified in
;;; the list contained in the "members" instance variable
(defclass fixed-membership-set ()
  ((members :initform nil :initarg :members :reader members))
  )

(defmethod print-object ((set fixed-membership-set) stream)
  (format stream "#<Set-of ~{~a~^, ~}" (members set)))

;;; Assertions for core data modeling
(define-predicate add-to-set (set new-value pre-situation post-situation) (ltms:ltms-predicate-model))
(define-predicate add-to-map (map key value pre-situation post-situation) (ltms:ltms-predicate-model))

(defgeneric add-to-set (set value))
(defgeneric add-to-map (map key value))
;;; A default implementation of maps
(defmethod add-to-map ((thing hash-table) key value)
  (setf (gethash key thing) value))

;;; NOTE: These seem to be done in a particularly obscure way
;;; Better to do this in the tradition of co-algebraic specs in which
;;; we have different names for the input and ouput even when it's the same thing
;;; and have an [Identical a b] predicate saying that it happened by side effect
;;; and perhaps an add-to-set-function
;;; and perhaps an [equal a b] predicate so we would instead say [Equal output-set (add-to-set input-set new-value)]

;;; these methods build a data-structure representation of the set (or map) in the simulator that mirrors what the
;;; data-structures in the concrete implementation should be.
(define-predicate-method (act-on-truth-value-change add-to-set :after) (old-truth-value &optional old-state)
  (declare (ignore old-truth-value old-state))
  (let* ((been-in-before (joshua:been-in-before-p self)))
    (when (and been-in-before (eql (predication-truth-value self) +true+))
      (with-statement-destructured (set new-value pre-sit post-sit) self
	(declare (ignore pre-sit post-sit))
	(when (listp set)
	  (setq set (funcall (first set) (second set))))
	(add-to-set set new-value)))))

(define-predicate-method (act-on-truth-value-change add-to-map :after) (old-truth-value &optional old-state)
  (declare (ignore old-truth-value old-state))
  (let* ((been-in-before (been-in-before-p self)))
    (when (and been-in-before (eql (predication-truth-value self) +true+))
      (with-statement-destructured (map key new-value pre-sit post-sit) self
	(declare (ignore pre-sit post-sit))
	(when (listp map)
	  (setq map (funcall (first map) (second map))))
	(add-to-map map key new-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Situations and Intervals and things that have them
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass situation-object (has-name-mixin)
  ((component :accessor component :initarg :component)
   (assertions :accessor assertions :initarg :assertions :initform nil)
   (before-or-after :accessor before-or-after :initarg :before-or-after)))

(defmethod print-object ((thing situation-object) stream)
  (format stream "<Situation ~a ~a>" (before-or-after thing) (component thing)))

(defclass interval-object (has-name-mixin)
  ((component :accessor component :initarg :component)
   (assertions :accessor assertions :initarg :assertions :initform nil)))

(defmethod before-or-after ((i interval-object)) 'during)

(defmethod print-object ((thing interval-object) stream)
  (format stream "<Interval spanning ~c>" (component thing)))

;;; A mixin for components that have incoming situtations

(defclass has-presituation-mixin ()
  ((presituation :accessor presituation :initarg :presituation)))

(defmethod initialize-instance :after ((c has-presituation-mixin) &rest initargs)
  (declare (ignore initargs))
  (let* ((name (object-name c))
	 (before-situation-name (make-name 'before name))
	 (before-situation (make-instance 'situation-object
			     :name before-situation-name
			     :component c
			     :before-or-after :before)))
    (tell `[situation ,c before ,before-situation])
    (setf (presituation c) before-situation)))

;;; A mixin for components that have outgoing situtations

(defclass has-postsituation-mixin ()
  ((postsituation :accessor postsituation :initarg :postsituation)))

(defmethod initialize-instance :after ((c has-postsituation-mixin) &rest initargs)
  (declare (ignore initargs))
  (let* ((name (object-name c))
	 (after-situation-name (make-name 'after name))
	 (after-situation
	  (make-instance 'situation-object
	    :name after-situation-name
	    :component c
	    :before-or-after :after)))
    (tell `[situation ,c after ,after-situation])
    (setf (postsituation c) after-situation)))

;;; A mixin for components that have spanning intervals

(defclass has-interval-mixin ()
  ((interval :accessor spanning-interval :initarg :interval)))

(defmethod initialize-instance :after ((c has-interval-mixin) &rest initargs)
  (declare (ignore initargs))
  (let* ((name (object-name c))
	 (interval-name (make-name 'interval name))
	 (interval (make-instance 'interval-object
		     :name interval-name
		     :component c)))
    (tell `[interval ,c during ,interval])
    (setf (spanning-interval c) interval)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Strucutural model classes
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; has parent mixin should be part of anything that is a direct
;;; part of the component hierarchy
;;;  e.g. splits, joins, components
;;;  buy not the branches of splits and joins
;;;  or dataflows, controlflow, ports, etc.

(defclass has-name-mixin ()
  ((object-name :accessor object-name :initarg :name :initform 'thing))
  )

(defclass has-qualified-name-mixin ()
  ((qualified-name :accessor qualified-name :initarg :qualified-name :initform nil))
  )


(defclass has-parent-mixin (has-name-mixin has-qualified-name-mixin)
  ((parent :accessor parent :initarg :parent)
   (object-type :accessor object-type :initarg :type :initform 'thing)
   ;; The qualified name is a dotted pathname from the top to here
   ;; where each field the object-name on the path
   ))

(defmethod print-object ((thing has-parent-mixin) stream)
  (format stream "<~s ~a>" (type-of thing) (object-name thing)))

(defmethod initialize-instance :after ((c has-parent-mixin) &rest initargs)
  (declare (ignore initargs))
  (let* ((name (object-name c))
	 (parent (parent c)))
    (tell `[component ,parent ,name ,c])
    (when parent
      (push c (components parent)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Splits, Joins and their branches
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defclass has-branches-mixin ()
  ((branches :accessor branches :initarg :branches :initform nil)))

(defclass primitive-branch-mixin (has-parent-mixin)
  ((branch-owner :accessor branch-owner :initarg :branch-owner :initform nil)
   (branch-name :accessor branch-name :initarg :branch-name :initform nil)))

(defmethod initialize-instance :after ((b primitive-branch-mixin)
				       &key branch-owner branch-name)
  (tell `[component-type ,b ,(type-of b)])
  (when (and branch-name branch-owner)
    (tell `[branch-of ,branch-name ,branch-owner ,b])))

;;; branchs of a split
(defclass split-branch (primitive-branch-mixin has-postsituation-mixin)
  ((condition :accessor branch-condition :initarg :condition :initform nil)))

;;; branches of a join
(defclass join-branch (primitive-branch-mixin has-presituation-mixin)
  ())

;;; These are assume to consume no time, thus no interval during their execution
;;; Split's have a pre-situation, the post-situation belongs to the branch
;;; Joins have a post-situation, the pre-situation belongs to the branch
(defclass split-object (has-parent-mixin
			has-presituation-mixin
			has-branches-mixin)
  ())

(defmethod initialize-instance :after ((s split-object) &key)
  (tell `[component-type ,s split]))

(defclass join-object (has-parent-mixin
		       has-branches-mixin
		       has-postsituation-mixin)
  ())

(defmethod initialize-instance :after ((s join-object) &key)
  (tell `[component-type ,s join]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Components
;;;  both primitive and ones with implementations
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass component-mixin (has-parent-mixin
			   has-presituation-mixin
			   has-postsituation-mixin
			   has-interval-mixin
			   )
  ((inside :initform nil :initarg :inside :accessor inside)
   (resources :initform nil :initarg :resources :accessor resources)
   ))

(defmethod qualified-name :around ((c component-mixin))
  (let ((answer (call-next-method)))
    (unless answer
      (let ((parent (parent c)))
	(cond ((not (null parent))
	       (setq answer (make-name (qualified-name parent) (object-name c) ".")))
	      (t (setq answer (object-name c)))))
      (setf (qualified-name c) answer))
    answer))

;;; components are things that can have an implementation
;;; it's initially not expanded, but by calling build implementattion
;;; on it you can build it.

(defclass compound-component (component-mixin)
  ((components :accessor components :initform nil :initarg :components)
   (implementation-expanded :accessor expanded? :initform nil))
  )

(defmethod component-named ((parent compound-component) role-name)
  (find role-name (components parent) :key #'object-name)
  )

;;; primtive components don't have an implementation
;;; calling build-implementation on them does nothing
;;; and they always respond to expanded? by saying yes
(defclass primitive-component (component-mixin)
  ()
  )

(defmethod initialize-instance :after ((c component-mixin) &key )
  (tell `[component-type ,c component]))

;;; There are two generic functions involved in constructing components:
;;;  Build interface
;;;  Build-implementation


(defgeneric build-interface (component-type role-name &optional parent))
(defgeneric build-implementation (component-type parent))

(defmethod build-implementation :after (component-type (c compound-component))
  (declare (ignore component-type))
  (setf (expanded? c) t))

(defmethod build-implementation (component-type (c primitive-component))
  (declare (ignore component-type))
  (values c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Resources
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; A resource has an owner (the highest placd in the hierarchy that it's know about)
;;;  and a set of users (any component below that the employs the resource)
;;;
(defclass resource-object (has-name-mixin has-qualified-name-mixin)
  ((type :accessor resource-type :initarg :type)
   ;; we have a model in which a single component owns the resource
   ;; but may share it with several other things.
   ;; Who actually "owns" this resource
   (owner :accessor owner :initarg :owner)
   ;; all components that use the resource
   (users :accessor users :initarg :users :initform nil)
   ))

(defmethod qualified-name :around ((r resource-object))
  (let ((answer (call-next-method)))
    (unless answer
      (let ((owner (owner r)))
	(cond ((not (null owner))
	       (setq answer (make-name (qualified-name owner) (object-name r) ".")))
	      (t (setq answer (object-name r)))))
      (setf (qualified-name r) answer))
    answer))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; finding components with no incoming dataflows or controlflows

(defun has-no-incoming-dataflows (component)
  (ask `[dataflow ?source-port ?source ?port-name ,component]
       #'(lambda (just)
	   (declare (ignore just))
	   (return-from has-no-incoming-dataflows nil)))
  t)

(defun has-no-incoming-controlflows (component)
  (ask `[controlflow ?source-port ?source ?port-name ,component]
       #'(lambda (just)
	   (declare (ignore just))
	   (return-from has-no-incoming-controlflows nil)))
  t)

(defmethod handle-null-cases ((component primitive-component))
  (values))

(defmethod handle-null-cases ((parent-component compound-component))
  (loop for component in (components parent-component)
      do (when (has-no-incoming-controlflows component)
	   (unless (or (typep component 'join-object)
		       (typep component 'split-branch))
	     (tell `[all-controlflows-satisfied ,component])))
	   (when (has-no-incoming-dataflows component)
	     (unless (or (typep component 'join-object)
			 (typep component 'split-branch))
	     (tell `[all-inputs-present ,component])))))


;;; This pushes along post-condition assertions to all those downstream situations
;;; that mention any object in the assertion
(define-predicate-method (act-on-truth-value-change situation-tagged-mixin :after) (old-truth-value &optional old-state)
  (declare (ignore old-truth-value old-state))
  (let* ((statement (predication-statement self))
	 (situation (first (last statement)))
	 (component (component situation)))
    (cond
     ((eql (predication-truth-value self) +true+)
      (push self (assertions situation))
      (cond
       ((eql (before-or-after situation) :after)
	;; want to propagate along data-flows
	(ask `[dataflow ?output ,component ?input ?other-component]
	     #'(lambda (just1)
		 (when
		     ;; does this assertion mention the associated output
		     (block foo
		       (ask `[output ?output ,component ?value]
			    #'(lambda (ignore)
				(declare (ignore ignore))
				(when (member ?value (predication-statement self))
				  (return-from foo t))))
		       nil)
		   (ask [situation ?other-component ?time ?other-situation]
			#'(lambda (just2)
			    (when (or (eql ?time 'before)
				      (and (eql ?time 'after)
					   (eql component ?other-component)))
			      (let* ((statement (predication-statement self))
				     (butlast (butlast statement))
				     (new-statement (append butlast (list ?other-situation))))
				(tell (make-predication new-statement)
				      :justification `(statement-flow (,(ask-database-predication just1)
								       ,(ask-database-predication just2)
								       ,self)))))))))))
       ((and (eql (before-or-after situation) :before)
	     (typep component 'component-object))
	(push-outside-assertion-inside self component))
       ;; Propogate across a Join branch
       ((and (eql (before-or-after situation) :before)
	     (typep component 'join-branch))
	;; want to move to after situation of the corresponding join
	;; but only if its the selected branch of the join
	(ask `[branch-of ?name ?join ,component]
	     #'(lambda (just1)
		 (ask `[selected-branch ?join ,component]
		      #'(lambda (just2)
			  (ask [situation ?join after ?other-situation]
			       #'(lambda (just3)
				   (let* ((statement (predication-statement self))
					  (butlast (butlast statement))
					  (new-statement (append butlast (list ?other-situation))))
				     (tell (make-predication new-statement)
					   :justification `(statement-flow (,(ask-database-predication just1)
									    ,(ask-database-predication just2)
									    ,(ask-database-predication just3)
									    ,self)))))))))))
       ))
     (t (setf (assertions situation) (remove self (assertions situation)))))))


;;; this does the pushing of assertions along dataflows
;;; from the outside of a plan to an inside component
;;; it's called just after the inside is constructed
(defmethod build-implementation :after (type component)
  (declare (ignore type))
  (push-implementation-initial-assertions component))

(defun push-implementation-initial-assertions (component)
  (let* ((before-situation (block block
			     (ask `[situation ,component before ?before-situation]
				  #'(lambda (just1)
				      (declare (ignore just1))
				      (return-from block ?before-situation)))))
	 (assertions (assertions before-situation)))
    ;; for each input of the box
    (loop for assertion in assertions
	do (push-outside-assertion-inside assertion component))))

(defun push-outside-assertion-inside (assertion component)
  (flet ((push-assertion (assertion new-situation support)
	   (let* ((statement (predication-statement assertion))
		  (butlast (butlast statement))
		  (new-statement (append butlast (list new-situation))))
	     (tell (make-predication new-statement)
		   :justification `(statement-flow ,support)))))
    ;; first token is the pred last is the situation
    (loop for value in (cdr (butlast (predication-statement assertion)))
	do (ask `[input ?input ,component ,value]
	       #'(lambda (just2)
		   (declare (ignore just2))
		   ;; and data flow from that input
		   (ask `[dataflow ?input ,component ?other-input ?inside-component]
			#'(lambda (just3)
			    ;; to a component of the outer box
			    (ask [situation ?inside-component before ?other-sit]
				 #'(lambda(just5)
				     (declare (ignore just5))
				     (push-assertion assertion ?other-sit
				      (list assertion
					    (ask-database-predication just3)))
				     )))))))))

;;; mixin for having a specific bit in a bit vector
(define-predicate-model has-bit-position-mixin
	((bit-pattern #-genera :initform 0 . #-genera (:accessor bit-pattern)))
	()
	)

(define-predicate selected-model (component model)
		  (has-bit-position-mixin ltms:ltms-predicate-model))

(define-predicate uses-resource (component resource) (ltms:ltms-predicate-model))

;;; Probabilities (apriori and conditional)
(define-predicate a-priori-probability-of (resource model probability) (ltms:ltms-predicate-model))
(define-predicate conditional-probability (component model resource-model-set conditional-probability)
		  (ltms:ltms-predicate-model))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Cleaning out things relating to an ensemble
;;;  Use this to remove every assertion describing an ensemble
;;;  not (clear), since that might kill things that want to be around statically
;;;
;;; Fix Me: Check that the list of predicates below is accurate
;;;         Does anybody actually use this anymore?
;;;         Maybe a better approach is something like separately clearable-mixin?
;;;
;;;(defun clear-top-level-ensemble (ensemble-name)
;;;  (let ((victims nil))
;;;    (labels
;;;	((kill-it (just)
;;;	   (push (ask-database-predication just) victims))
;;;	 ;; This is called with an outside-box. It first wipes out everything about the outside
;;;	 ;; then finds the inside-plan, finds all components in it (which are outside-boxes)
;;;	 ;; and then recursively wipes them out.
;;;	 (clear-ensemble-assertions (ensemble)
;;;	   ;; static structure
;;;	   (ask `[autostart ,ensemble] #'kill-it)
;;;	   (ask `[event-for ?event ?time ,ensemble ?effect] #'kill-it)
;;;	   (ask `[event-map ?event ?time ,ensemble ?argument-type ?map] #'kill-it)
;;;	   (ask `[behavior ,ensemble ?type] #'kill-it)
;;;	   (ask `[component-type ,ensemble ?type] #'kill-it)
;;;	   (ask `[branch-of ?branch-name ,ensemble ?the-branch] #'kill-it)
;;;	   (ask `[port ?direction ,ensemble ?port-name] #'kill-it)
;;;	   (ask `[uses-resource ,ensemble ?resource] #'kill-it)
;;;	   (ask `[interval ,ensemble ?span ?interval] #'kill-it)
;;;	   (ask `[situation ,ensemble ?position ?situation] #'kill-it)
;;;	   (ask `[dataflow ?port-name ,ensemble ?other-port ?other-component] #'kill-it)
;;;	   (ask `[dataflow ?port-name  ?other-component ?other-port ,ensemble] #'kill-it)
;;;	   (ask `[controlflow ?port-name ,ensemble ?other-port ?other-component]
;;;		#'(lambda (just)
;;;		    (let ((the-assertion (ask-database-predication just)))
;;;		      (ask `[controlflow-satisfied ,the-assertion] #'kill-it)
;;;		      (kill-it just))))
;;;	   (ask `[controlflow ?other-port ?other-component ?port-name ,ensemble]
;;;		#'(lambda (just)
;;;		    (let ((the-assertion (ask-database-predication just)))
;;;		      (ask `[controlflow-satisfied ,the-assertion] #'kill-it)
;;;		      (kill-it just))))
;;;	   (ask `[conditional-probability ,ensemble ?mode ?dependency-list ?prob] #'kill-it)
;;;	   (ask `[attack ,ensemble ?attack-name ?attack-type] #'kill-it)
;;;	   ;; dynamic behavior
;;;	   (ask `[bad-event-detected ?event ?time ,ensemble ?args] #'kill-it)
;;;	   (ask `[selected-branch ,ensemble ?branch] #'kill-it)
;;;	   (ask `[selected-model ,ensemble ?model] #'kill-it)
;;;	   (ask `[execution-status ,ensemble ?status] #'kill-it)
;;;	   (ask `[input ?port ,ensemble ?input] #'kill-it)
;;;	   (ask `[output ?port ,ensemble ?output] #'kill-it)
;;;	   (ask `[all-controlflows-satisfied ,ensemble] #'kill-it)
;;;	   (ask `[all-terminal-controlflows-satisfied ,ensemble] #'kill-it)
;;;	   (ask `[all-inputs-present ,ensemble] #'kill-it)
;;;	   (ask `[prerequisites-satisfied ,ensemble] #'kill-it)
;;;	   (ask `[potentially [earliest-arrival-time ? ,ensemble ?]] #'kill-it)
;;;	   (ask `[potentially [latest-arrival-time ? ,ensemble ?]] #'kill-it)
;;;	   (ask `[potentially [earliest-production-time ? ,ensemble ?]] #'kill-it)
;;;	   (ask `[potentially [latest-production-time ? ,ensemble ?]] #'kill-it)
;;;	   (ask `[earliest-arrival-time ? ,ensemble ?] #'kill-it)
;;;	   (ask `[latest-arrival-time ? ,ensemble ?] #'kill-it)
;;;	   (ask `[earliest-production-time ? ,ensemble ?] #'kill-it)
;;;	   (ask `[latest-production-time ? ,ensemble ?] #'kill-it)
;;;	   (ask `[possible-model ,ensemble ?model-name] #'kill-it)
;;;	   ;; find the body and clean it out as well
;;;	   ;; the body has components and resources
;;;	   (ask `[corresponding-ensemble ,ensemble ?sub-ensemble]
;;;		#'(lambda (stuff)
;;;		    (ask [resource ?sub-ensemble ?name ?resource]
;;;			 #'(lambda (stuff)
;;;			     (kill-it stuff)
;;;			     (ask [resource-might-have-been-attacked ?resource ?attack]
;;;				  #'(lambda (stuff)
;;;				      (ask [attack-implies-compromised-mode ?attack ?resource ?mode ?likelihood] #'kill-it)
;;;				      (kill-it stuff)))
;;;			     (ask [possible-model ?resource ?model-name] #'kill-it)
;;;			     (ask [resource-type-of ?resource ?type] #'kill-it)
;;;			     (ask [has-vulnerability ?resource ?vulnerability-name] #'kill-it)
;;;			     (ask [a-priori-probability-of ?resource ?model-name ?prob] #'kill-it)
;;;			     ))
;;;		    (ask [component ?sub-ensemble ?name ?component]
;;;			 #'(lambda (stuff)
;;;			     (clear-ensemble-assertions ?component)
;;;			     (kill-it stuff)))
;;;		    (kill-it stuff)))))
;;;      (ask `[component nil ,ensemble-name ?outer-ensemble]
;;;	   #'(lambda (just)
;;;	       (clear-ensemble-assertions ?outer-ensemble)
;;;	       (kill-it just))))
;;;    (mapc #'untell victims))
;;;  (values))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; component can be either a normal component or a branch of a split or join

(define-predicate-method (act-on-truth-value-change controlflow-satisfied :after) (old-truth-value &optional old-state)
  (declare (ignore old-truth-value old-state))
  (when (eql (predication-truth-value self) +true+)
    (with-statement-destructured (the-cf-assertion) self
      (with-statement-destructured (source-time source destination-time destination) the-cf-assertion
	(declare (ignore  source))
	(cond ((and (eql source-time 'after) (eql destination-time 'after))
	       (let ((support (all-terminal-controlflows-are-there destination)))
		 (when support
		   (tell `[all-terminal-controlflows-satisfied ,destination]
			 :justification `(cf-tracker ,support)))))
	      (t
	       (multiple-value-bind (all-there? support)
		   (all-controlflows-are-there destination)
		 (when (and all-there? support)
		   (tell `[all-controlflows-satisfied ,destination]
			 :justification `(cf-tracker ,support))))))))))

(defun all-controlflows-are-there  (component)
  (let ((supports nil))
    (ask `[controlflow ?time ?predecessor before ,component]
	 #'(lambda (just)
	     (let ((cf-assertion (ask-database-predication just)))
	       (block inner
		 (ask `[controlflow-satisfied ,cf-assertion]
		      #'(lambda (support)
			  (push (ask-database-predication support) supports)
			  (return-from inner t)))
		 (return-from all-controlflows-are-there nil)))))
    (values t supports)))


(defun all-terminal-controlflows-are-there  (component)
  (let ((supports nil))
    (ask `[controlflow after ?predecessor after ,component]
	 #'(lambda (just)
	     (let ((cf-assertion (ask-database-predication just)))
	       (block inner
		 (ask `[controlflow-satisfied ,cf-assertion]
		      #'(lambda (support)
			  (push (ask-database-predication support) supports)
			  (return-from inner t)))
		 (return-from all-terminal-controlflows-are-there nil)))))
    supports))


;;; Replaced this with a generated rules for each behavior model
;;; Whenever an input assertion becomes true check that all inputs are there
;;; This means that we need to somewhere check for modules with no inputs and
;;; assert that they have all inputs present.

;;;(define-predicate-method (act-on-truth-value-change input :after) (old-truth-value &optional old-state)
;;;  (declare (ignore old-truth-value old-state))
;;;  (when (eql (predication-truth-value self) +true+)
;;;    (with-statement-destructured (port component value) self
;;;	(declare (ignore value port))
;;;	(let ((all-input-names nil))
;;;	  (ask `[port input ,component ?port-name]
;;;	       #'(lambda (stuff)
;;;		   (declare (ignore stuff))
;;;		   (push ?port-name all-input-names)))
;;;	  (let ((supports (all-inputs-are-there component all-input-names)))
;;;	    (loop for support in supports
;;;		do (tell `[all-inputs-present ,component]
;;;			 :justification `(input-tracker ,support))))))))

;;;(defun all-inputs-are-there (component all-input-names)
;;;  (let ((support nil))
;;;    (labels ((do-next (preds-so-far remaining-names)
;;;	       (cond
;;;		((and (null remaining-names) preds-so-far)
;;;		 (push preds-so-far support))
;;;		((null remaining-names))
;;;		(t (destructuring-bind (input-name . rest-of-names) remaining-names
;;;		     (ask `[input ,input-name ,component ? ]
;;;			  #'(lambda (stuff)
;;;			      (do-next (cons (ask-database-predication stuff) preds-so-far)
;;;				rest-of-names))))))))
;;;      (do-next nil all-input-names))
;;;    support))

(define-predicate-method (act-on-truth-value-change output :after) (old-truth-value &optional old-state)
  (declare (ignore old-truth-value old-state))
  (when (eql (predication-truth-value self) +true+)
    (with-statement-destructured (port component value) self
	(declare (ignore value port))
	(let ((all-output-names nil))
	  (ask `[port output ,component ?port-name]
	       #'(lambda (stuff)
		   (declare (ignore stuff))
		   (push ?port-name all-output-names)))
	  (let ((support (all-outputs-are-there component all-output-names)))
	    (when support
	      (tell `[all-outputs-present ,component]
		    :justification `(output-tracker ,support))))))))

(defun all-outputs-are-there (component all-output-names)
  (let ((support nil))
    (loop for output-name in all-output-names
	always (block found-it
		 (ask `[output ,output-name ,component ? ]
		      #'(lambda (stuff)
			  (push (ask-database-predication stuff) support)
			  (return-from found-it t)))
		 (return-from all-outputs-are-there nil)))
    support))


;;; we need to do something similar for control flow assertions
;;; they would be triggered by execution status assertions

;;;(defun propagate-inputs (component all-input-names)
;;;  (ask `[port output ,component ?port-name]
;;;       #'(lambda (stuff)
;;;	   (declare (ignore stuff))
;;;	   (if (member ?port-name all-input-names)
;;;	       (ask `[input ?port-name ,component ?value]
;;;		    #'(lambda (stuff)
;;;			(let ((input-assertion (ask-database-predication stuff)))
;;;			  (tell `[output ?port-name ,component ?value]
;;;				:justification `(io-identical (,input-assertion))))))
;;;	     (let ((value (gentemp ?port-name)))
;;;	       (tell `[output ?port-name ,component ,value]
;;;		     :justification 'new-output))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The Macros for Defining Compnent Structure and Behavior
;;;
;;; These build methods for the two generic functions:
;;;   build-interface
;;;   build-implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defvar *top-level-components* nil)

(defmethod build-interface :around (module-type role-name &optional the-parent)
  (declare (ignore module-type role-name))
  (let ((the-component (call-next-method)))
    (setf (parent the-component) the-parent)
    (when (null the-parent)
      ;; it's a top level module so all its prerequisites are satisfied
      ;; by definition (or maybe they should be part of the define-ensemble
      ;; and then asserted)
      (tell `[prerequisites-satisfied ,the-component])
      ;; And all its incoming control-flows are satisfied too
      (tell `[all-controlflows-satisfied ,the-component])
      ;; so now whenever all its inputs are there it will be marked ready
      )
    ;; I'm sure I don't remember why this is here
    (when (and (null the-parent)
	       (all-inputs-are-present the-component)
	       (all-controlflows-are-there the-component))
      (tell `[execution-status ,the-component ready]))
    the-component))

;;; A rule that says that a resource belongs to an ensemble if it
;;; belongs to any component of the ensemble.  Resources are named, so
;;; there could be a name conflict from two components having two
;;; different resources with the same name.  Fix is to use the qualified-name

;;; The produces a dotted-tail list if it recurses?
(defrule resource-hierarchical (:backward)
  then [resource ?component ?resource-name ?resource]
  if [and [component ?component ? ?child]
	  [resource ?child ? ?resource]
	  (unify ?resource-name (qualified-name ?resource))
	  ]
  )

;;; Fix Me:
;;; This doesn't deal with the idea that there can be a shared dependency on a
;;; common resource.  In which case it's specified at the lub of the things that
;;; share it and is passed down as an argument as the inside is built.

(defmacro define-component-type (type
				 &key (top-level nil)
				      (primitive nil)
				      ;; structural parts
				      inputs outputs state-variables
				      components splits joins
				      dataflows controlflows
				      ;; events that are related to initiation, completion and internal progress
				      entry-events allowable-events exit-events
				      ;; resources and their types
				      resources
				      ;; behavior modes and their dependencies on the modes of the resources
				      behavior-modes behavior-dependencies
				      )
  `(eval-when (:compile-toplevel :execute :load-toplevel)
     (when ,top-level (pushnew ',type *top-level-components*))
     ;;: Fix Me? Loops of things here include a loop with a TELL in the expansion
     ;;; when it could flatten that out to just a bunch of TELL's
     (defmethod build-interface ((type (eql ',type)) name &optional parent)
       (let ((component (make-instance ',(if primitive 'primitive-component 'compound-component)
			  ;; NOTE: Need to clarify what's meant by parent vs ensemble
			  ;; at the moment for component-objects they seem to mean the
			  ;; same thing
			  :parent parent
			  :type type
			  :name name)))
	 ;; Processing of events
	 ,@(if (and (symbolp entry-events)
		    (eql entry-events :auto))
	       `((tell `[autostart ,component]))
	     (progn
	       (loop for event-name in entry-events
		   for real-event-name = (if (listp event-name) (first event-name) event-name)
		   for time = (if (listp event-name) (second event-name) 'entry)
		   collect `(tell `[event-for ,',real-event-name ,',time ,component start]))))
	 (tell `[allowable-events-for ,component ,(make-instance 'fixed-membership-set :members ',allowable-events)])
	 ,@(loop for event-name in allowable-events
	       for real-event-name = (if (listp event-name) (first event-name) event-name)
	       for time = (if (listp event-name) (second event-name) 'allowable)
	       when (eql time 'allowable)
	       collect `(tell `[event-for ,',real-event-name entry ,component allowable])
	       and collect `(tell `[event-for ,',real-event-name exit ,component allowable])
	       else collect `(tell `[event-for ,',real-event-name ',time ,component allowable]))
	 ,@(loop for entry in allowable-events
	       for (event-name time map) = (when (listp entry) entry)
	       when map
	       collect `(tell `[event-map ,',event-name ,',time ,component output ,',map]))
	 ,@(loop for event-name in exit-events
	       for real-event-name = (if (listp event-name) (first event-name) event-name)
	       for time = (if (listp event-name) (second event-name) 'exit)
	       collect `(tell `[event-for ,',real-event-name ,',time ,component completion]))
	 ,@(when (not (symbolp entry-events))
	     (loop for entry in entry-events
		 for explicit? = (listp entry)
		 collect (let ((event-name (if explicit? (first entry) entry))
			       (time (if explicit? (second entry) 'entry))
			       (map (if explicit? (copy-seq (third entry)) inputs)))
			   `(tell `[event-map ,',event-name ,',time ,component inputs ,',map]))))
	 ,@(loop for entry in exit-events
	       for explicit? = (listp entry)
	       collect (let ((event-name (if explicit? (first entry) entry))
			     (time (if explicit? (second entry) 'exit))
			     (map (if explicit? (copy-seq (third entry)) outputs)))
			 `(tell `[event-map ,',event-name ,',time ,component outputs ,',map])))
	 ;;; Now for inputs and outputs
	 (tell `[behavior ,component ,type])
	 ,@(loop for input in inputs collect  `(tell `[port input ,component ,',input]))
	 ,@(loop for output in outputs collect `(tell `[port output ,component ,',output]))
	 ,@(loop for state-variable in state-variables collect `(tell `[state-variable ,component ,',state-variable]))
	 ;; Behavior modes and their probabilities
	 ,@(loop for behavior-mode in behavior-modes
	       collect `(tell `[possible-model ,component ,',behavior-mode]))
	 ;;; Now for resources modes dependencies etc
	 ;;; First the resources and their types
	 ,(when resources
	    `(let ((resource-alist nil))
	       ;; process name and types
	       ,@(loop for (resource-name type) in resources
		     collect `(let ((resource (instantiate-resource ',type ',resource-name component)))
				(push resource (resources component))
				(push (cons ',resource-name resource) resource-alist)))
	       ;; Conditional Probabilities.
	       ;; These entries have the syntax:
	       ;; Behavor-mode <a list of (resource-name resource-mode) pairs> Probability
	       ,@(loop for (behavior-model dependency-list probability) in behavior-dependencies
		     collect `(let ((resource-dependency-list nil))
				,@(loop for (resource-name resource-mode) in dependency-list
				      collect `(let ((resource (cdr (assoc ',resource-name resource-alist))))
						 (push (cons resource ',resource-mode) resource-dependency-list)))
				(tell `[conditional-probability ,component ,',behavior-model ,resource-dependency-list ,',probability])))))
	 component))
     (defmethod build-implementation ((type (eql ',type)) parent)
       ,@(loop for (role-name behavior inputs branches) in splits
	     for branch-names in (loop for (role-name nil nil branches) in splits
				     collect (loop for branch in branches collect (smash role-name branch)))
	     collect `(let ((the-split (make-instance 'split-object
					 :name ',role-name
					 :type 'split
					 :parent parent)))
			(tell `[behavior ,the-split ,',behavior])
			,@(loop for input in inputs collect
				`(tell `[port input ,the-split ,',input]))
			,@(loop for name in branches
			      for branch-name in branch-names
			      collect `(make-instance 'split-branch
					 :name ',branch-name
					 :branch-name ',name
					 :branch-owner the-split
					 :parent parent))))
       ,@(loop for (role-name inputs branches) in joins
	     for branch-name in (loop for (role-name nil branches) in joins
				    collect (loop for branch in branches
						collect (smash role-name branch)))
	     collect `(let ((the-join (make-instance 'join-object
					:name ',role-name
					:type 'join
					:component parent)))
			,@(loop for input in inputs
			      collect `(tell `[port output ,the-join ,',input]))
			,@(loop for name in branches
			      for branch-name in (loop for (role-name nil branches) in joins
						     collect (loop for branch in branches
								 collect (smash role-name branch)))
			      collect `(let ((the-branch (make-instance 'join-branch
							   :name ',branch-name
							   :branch-name ',name
							   :branch-owner the-join
							   :parent parent)))
					 ,@(loop for input in inputs collect `(tell `[port input ,the-branch ,',input]))))))
       ,@(loop for (role-name . plist) in components
	     for models = (getf plist :models)
	     for type = (getf plist :type)
	     collect `(let ((sub-component (build-interface ',type ',role-name parent)))
			(build-exhaustives sub-component ',models)
			,@(loop for model in models
			      collect `(tell `[possible-model ,sub-component ,',model]))))
	 ;;; can go from normal to normal, or split-branch to normal or normal to join-branch
	 ;;; out-port and in-port are either before or after (can be extended to before-before, etc.)
       ,@(loop for (from-port-name from-component-name to-port-name to-component-name) in controlflows
	     collect
	       (cond
		((eql to-component-name type)
		 `(make-controlflow (component-named parent ',from-component-name) ',from-port-name
				    parent ',to-port-name))
		((eql from-component-name type)
		 `(make-controlflow parent ',from-port-name
				    (component-named parent ',to-component-name) ',to-port-name))
		(t
		 `(make-controlflow (component-named parent ',from-component-name) ',from-port-name
				    (component-named parent ',to-component-name) ',to-port-name))))
       ,@(loop for (from-port-name from-component-name to-port-name to-component-name) in dataflows
	     collect (cond
		      ((eql to-component-name type)
		       `(make-dataflow (component-named parent ',from-component-name) ',from-port-name
				       parent ',to-port-name))
		      ((eql from-component-name type)
		       `(make-dataflow  parent ',from-port-name
					(component-named parent ',to-component-name) ',to-port-name))
		      (t  `(make-dataflow (component-named parent ',from-component-name) ',from-port-name
					  (component-named parent ',to-component-name) ',to-port-name))))
       (handle-null-cases parent)
       parent)))

(defun make-controlflow (from-component from-port-name to-component to-port-name)
  (tell `[controlfow ,from-port-name ,from-component ,to-port-name ,to-component]))

(defun make-dataflow (from-component from-port-name to-component to-port-name)
  (tell `[dataflow ,from-port-name ,from-component ,to-port-name ,to-component]))

(defrule do-autostart (:forward)
  If [and [execution-status ?component ready] :support ?f1
	  [autostart ?component] :support ?f2]
  then (tell [execution-status ?component started]))

(defrule normal-start-select-model (:forward)
  If [execution-status ?component started]
  then (tell [selected-model ?component normal] :justification :assumption))

(defrule assume-no-bad-events (:forward)
  if [selected-model ?component normal]
  then [no-bad-events ?component])

(defun build-exhaustives (component models)
  (tell [ltms:contradiction]
        :justification `(must-have-a-model
			 nil
			 ,(loop for model in models
			      collect (tell `[selected-model ,component ,model]
					    :justification :none)))))

(defun hack-situation-into-assertion (situation assertion)
  (labels ((hack-a-primitive-statement (assertion)
	     (if (and (listp assertion) (eql (first assertion) 'predication-maker))
		 (multiple-value-bind (predicate connective body)
		     (destructure-predication-maker assertion)
		   (if (subtypep predicate 'situation-tagged-mixin)
		       (package-up-assertion connective body)
		     assertion))
	       assertion))
	   (package-up-assertion (connective body)
	     `(predication-maker (,connective ,(append body (list situation)))))
	   (destructure-predication-maker (assertion)
	     (let* ((statement (second assertion))
		    (connective (first statement))
		    (body (second statement)))
	       (values (predication-maker-predicate assertion) connective body)))
	   (hack-a-statement (assertion)
	     (if (and (listp assertion) (eql (first assertion) 'predication-maker))
		 (multiple-value-bind (predicate connective body)
		     (destructure-predication-maker assertion)
		   (cond
		    ((member predicate '(and or not))
		     (let* ((sub-statements (cdr body))
			    (processed-subs (loop for sub in sub-statements
						collect  (hack-a-statement sub)))
			    (processed-statement `(,predicate ,@processed-subs)))
		       `(predication-maker (,connective ,processed-statement))))
		    (t (hack-a-primitive-statement assertion))))
	       assertion)))
    (hack-a-statement assertion)
    ))

(defun smash (&rest names)
  (intern (format nil "~{~a~^-~}" names)))


(defmacro defbehavior-model ((component-type &rest model-names)
			     &key prerequisites post-conditions inputs outputs
				  invariants wrap-points
				  allowable-events
				  )
  (declare (ignore wrap-points))
  (let ((component-variable `(logic-variable-maker ,(intern "?COMPONENT")))
	(interval-variable `(logic-variable-maker ,(make-name "?INTERVAL" component-type)))
	(pre-situation-variable `(logic-variable-maker ,(make-name "?BEFORE" component-type)))
	(post-situation-variable `(logic-variable-maker ,(make-name "?AFTER" component-type)))
	(generated-rules nil))
    (setq invariants
      (loop for inv in invariants
	  collect (hack-situation-into-assertion interval-variable inv)))
    (setq prerequisites
      (loop for prereq in prerequisites
	  collect (hack-situation-into-assertion pre-situation-variable prereq)))
    (setq post-conditions
      (loop for post in post-conditions
	  collect (hack-situation-into-assertion post-situation-variable post)))
    (loop for model-name in model-names
	do (let* ((name (smash component-type model-name "BEHAVIOR-MODEL"))
 		  (prereqs-name (smash component-type model-name "PREREQUISITES"))
		  (allowables-name (smash component-type model-name "ALLOWABLE-EVENTS"))
		  (inputs-present-name (smash component-type "INPUTS-PRESENT"))
		  (output-lvs nil)
		  output-assertions
		  input-assertions)
	     (loop for output in outputs
		 for lv-name = (intern (format nil "?~a" output))
		 for lv = `(logic-variable-maker ,lv-name)
		 do (push `(predication-maker '(output ,output ,component-variable ,lv)) output-assertions)
		 unless (member output inputs)
		 do (push (cons lv-name output) output-lvs))
	     (loop for input in inputs
		 for lv = `(logic-variable-maker ,(intern (format nil "?~a" input)))
		 do (push `(predication-maker '(input ,input ,component-variable ,lv)) input-assertions))
	     (push
	      `(defrule ,allowables-name (:forward)
		 if (predication-maker
		     '(and
		       (predication-maker '(behavior ,component-variable ,component-type))
		       (predication-maker '(selected-model ,component-variable ,model-name))))
		 then (predication-maker `(allowable-events-for ,,component-variable
								,(make-instance 'fixed-membership-set :members ',allowable-events))))
	      generated-rules)
	     ;; This generates the rules for prerequisite-satisfied and all-inputs-present
	     ;; but only if the model is normal.
	     ;; In other models it's redundant which suggests a change in syntax in which
	     ;; there is only one form in which inputs, outputs and prerequisites are stated once
	     ;; and then there's a post-conditions for each model.
	     ;;
	     ;; the pattern for this is:
	     ;;  component type, then bind the input variables, bind the input-situation
	     ;;  check the prerequisites
	     ;;  -> prerequisites are satisfied
	     (when (eql model-name 'normal)
	       (push
		`(defrule ,inputs-present-name (:forward)
		   if (predication-maker
		       '(and (predication-maker '(behavior ,component-variable ,component-type))
			 ,@input-assertions))
		   then (predication-maker '(all-inputs-present ,component-variable))
		   )
		generated-rules)
	       (push
		`(defrule ,prereqs-name (:forward)
		   if (predication-maker
		       '(and
			 (predication-maker '(behavior ,component-variable ,component-type))
			 ,@input-assertions
			 (predication-maker '(situation ,component-variable before ,pre-situation-variable))
			 ,@prerequisites))
		   then (predication-maker '(prerequisites-satisfied ,component-variable)))
		generated-rules))
	     ;; this is the model-specific behavor rule
	     ;; Pattern here is
	     ;;  component type, bind inputs, bind outputs, bind situations and interval
	     ;;  prerequisites (in order to bind any variables in the prereqs)
	     ;;  execution-status = completed -> invariants and post-conditions
	     (push
	      `(defrule ,name (:forward)
		 if (predication-maker
		     '(and
		       (predication-maker '(behavior ,component-variable ,component-type))
		       (predication-maker '(selected-model ,component-variable ,model-name))
		       (predication-maker '(execution-status ,component-variable completed))
		       ,@input-assertions
		       ,@output-assertions
		       (predication-maker '(interval ,component-variable during ,interval-variable))
		       (predication-maker '(situation ,component-variable before ,pre-situation-variable))
		       (predication-maker '(situation ,component-variable after ,post-situation-variable))
		       ,@prerequisites
		       ))
		 then (predication-maker
		       '(and
			 ,@invariants
			 ,@post-conditions)))
	      generated-rules)))
    `(eval-when (:compile-toplevel :execute :load-toplevel)
       ,@generated-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Defining Resource Types
;;;  This takes the modes and vulnerabilities of the resouce type
;;;  As above, there's a generic function Instantiate-Resource to contruct the resource
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric Instantiate-Resource (resource-type resource-name owning-component))

(defmacro define-resource-type (type-name &key modes vulnerabilities prior-probabilities)
  `(defmethod Instantiate-resource ((type (eql ',type-name)) resource-name owning-component)
     (let ((resource (make-instance 'resource-object :type type :name resource-name :owner owning-component :users (list owning-component))))
       (tell `[resource-type-of ,resource ,type])
       (tell `[resource ,owning-component ,resource-name ,resource])
       (tell `[uses-resource ,owning-component ,resource])
       ;; process possile-modes
       ,@(loop for mode in modes
	     collect `(tell `[possible-model ,resource ,',mode]))
       ;; process prior probabilities of the modes
       ,@(loop for (mode prior-probability) in prior-probabilities
	     collect `(tell `[a-priori-probability-of ,resource ,',mode ,',prior-probability]))
       ;; now do the vulnerability mapping
       ,@(loop for vulnerability in vulnerabilities
	     collect `(tell `[has-vulnerability ,resource ,',vulnerability]))
       resource)))


(defmacro defsplit (behavior-name inputs &rest pairs)
  (let ((split-variable `(logic-variable-maker ,(intern "?SPLIT")))
	(pre-situation-variable `(logic-variable-maker ,(make-name "?BEFORE" behavior-name)))
	(input-assertions nil))
    (loop for input in inputs
	for lv = `(logic-variable-maker ,(intern (format nil "?~a" input)))
	do (push `(predication-maker '(input ,input ,split-variable ,lv)) input-assertions))
    `(eval-when (:compile-toplevel :execute :load-toplevel)
       ,@(loop for (branch-name condition) in pairs
	     for hacked-condition = (hack-situation-into-assertion pre-situation-variable condition)
	     for rule-name = (smash behavior-name branch-name "BEHAVIOR")
	     collect `(defrule ,rule-name (:Forward)
			if [and [component ?parent ?name ?split]
				[component-type ?split split]
				[behavior ?split ,behavior-name]
				[branch-of ,branch-name ?split ?branch]
				[situation ?split before ,pre-situation-variable]
				,@input-assertions
				,hacked-condition]
			then [selected-branch ?split ?branch])))))

(defrule normal-dataflow (:forward)
  If [and [dataflow ?producer-port-name ?producer ?consumer-port-name ?consumer]
	  [port output ?producer ?producer-port-name]
	  [port input ?consumer ?consumer-port-name]
          [output ?producer-port-name ?producer ?value]]
  then [input ?consumer-port-name ?consumer ?value])


(defrule in-in-dataflow (:forward)
  If [and [dataflow ?producer-port-name ?producer ?consumer-port-name ?consumer]
	  ;; this only happens between component and parent
	  [component ?producer ? ?consumer]
          [port input ?producer ?producer-port-name]
	  [port input ?consumer ?consumer-port-name]
	  [input ?producer-port-name ?producer ?value]]
  then [input ?consumer-port-name ?consumer ?value])

(defrule out-out-dataflow (:forward)
  If [and [dataflow ?producer-port-name ?producer ?consumer-port-name ?consumer]
	  ;; this only happens between component and parent
	  [component ?consumer ? ?producer]
          [port output ?producer ?producer-port-name]
	  [port output ?consumer ?consumer-port-name]
	  [output ?producer-port-name ?producer ?value]]
  then [output ?consumer-port-name ?consumer ?value])

(defrule normal-controlflow (:forward)
  If [and [controlflow after ?producer before ?consumer] :support ?f
          [execution-status ?producer completed]]
  then [controlflow-satisfied ?f])

;;; Similarly for control-flows
;;;(defrule before-before-controlflow (:forward)
;;;  If [and [controlflow before ?producer before ?consumer] :support ?f
;;;          [execution-status ?producer started]]
;;;  then [controlflow-satisfied ?f])
;;;
;;;;;; normal use of this is component to containing ensemble
;;;(defrule after-after-controlflow (:Forward)
;;;  If [and [controlflow after ?producer after ?consumer] :support ?f
;;;	  [execution-status ?producer completed]]
;;;  then [controlflow-satisfied ?f])

;;; time is either enter or exit
(defun get-running-and-ready-components ()
  (let ((running-components nil)
	(ready-components nil))
    (ask [and [component ?parent ?name ?component]
	      [execution-status ?component ready]]
	 #'(lambda (just1)
	     (declare (ignore just1))
	     (push ?component ready-components)
	     (block block2
	       (ask [execution-status ?component started]
		    #'(lambda (just2)
			(declare (ignore just2))
			(block block3
			  (setq ready-components (delete ?component ready-components))
			  (push ?component running-components)
			  (ask [execution-status ?component completed]
			       #'(lambda (just3)
				   (declare (ignore just3))
				   (setq running-components
				     (delete ?component running-components))
				   (return-from block3 t))))
			(return-from block2 t))))))
    (values ready-components running-components)))

(defun most-specific-running-component ()
  (multiple-value-bind (ready running) (get-running-and-ready-components)
    (declare (ignore ready))
    (most-specific-component running)))

;;; Fix ME? Is it OK to use delete below since c-set is passed in?
(defun most-specific-component (c-set)
    (labels ((kill-his-parents (c)
	       (let ((his-parent (parent c)))
		 (when his-parent
		   (Setq c-set (delete his-parent c-set))
		   (kill-his-parents his-parent)))))
      (loop for c in c-set
	  do (kill-his-parents c)))
    (first c-set))

;;; Means the client doesn't want us thinking about simulating
;;; the model right now
(defvar *suppress-event-processing* nil)

;;; Fix me:  This allows the same event to trigger several different things
;;; is that really the intent?  Or is the idea that the event is uniquely
;;; associated with one thing?
(defmethod notice-event (event-name event-type universal-time thread args)
  (declare (ignore thread universal-time))
  (unless *suppress-event-processing*
    ;; first handle mappings to inputs and outputs independent of
    ;; what state the component might be in.
    (let ((found-a-use nil))
      (multiple-value-bind (ready running) (get-running-and-ready-components)
	;; is this a completion event for a running component?
	(loop for component in running
	    do (ask `[event-for ,event-name ,event-type ,component completion]
		    #'(lambda (just)
			(declare (ignore just))
			(setq found-a-use t)
			;; first provide the outputs, then tell that it's completed
			;; this avoids generating symbolic names when we've actually
			;; seen real outputs.
			(ask `[event-map ,event-name ,event-type ,component outputs ?map]
			     #'(lambda (just)
				 (declare (ignore just))
				 (loop for name in ?map
				     for value in args
				     when name
				     do (tell `[output ,name ,component ,value])
					(tell `[data-type-of ,value ,(type-of value)]))))
			(tell `[execution-status ,component completed]))))
	;; or an allowable event in something running
	;; which can set output values as well
	(loop for component in running
	    do (ask `[allowable-events-for ,component ?set-of-allowed-events]
		    #'(lambda (just)
			(declare (ignore just))
			(when (member event-name (members ?set-of-allowed-events))
			  (setq found-a-use t)
			  (ask `[event-map ,event-name ,event-type ,component outputs ?map]
			       #'(lambda (just)
				   (declare (ignore just))
				   (loop for name in ?map
				       for value in args
				       when name
				       do (tell `[output ,name ,component ,value])
					  (tell `[data-type-of ,value ,(type-of value)])
					  )))))))
	;; An initiation event for something ready.  Recompute ready
	;; and running because doing one of the above things may have
	;; caused the status of something to change consider the case
	;; of an event that ends one thing and starts the next.
	(multiple-value-setq (ready running) (get-running-and-ready-components))
	(flet ((do-this-guys-inputs (component)
		 (ask `[event-for ,event-name ,event-type ,component start]
		      #'(lambda (just)
			  (declare (ignore just))
			  ;; first provide the inputs, then tell that it's started
			  (ask `[event-map ,event-name ,event-type ,component inputs ?map]
			       #'(lambda (just)
				   (declare (ignore just))
				   (loop for name in ?map
				       for value in args
				       when name
				       do (tell `[input ,name ,component ,value])
					  (tell `[data-type-of ,value ,(type-of value)]))))
			  (tell `[execution-status ,component started])
			  (tell `[selected-model ,component normal]
				:justification :assumption)
			  (setq found-a-use t)
			  ))))
	  ;; Special case for when nothing is ready and this is a start event for the top
	  ;; level task.
	  (when (and (null ready) (null running) (eql event-type 'entry))
	    (ask `[component () ?name ?component]
		 #'(lambda (just)
		     (declare (ignore just))
		     (do-this-guys-inputs ?component))))
	  (loop for component in ready
	      do (do-this-guys-inputs component)))

	;; Otherwise it shouldn't have happened.
	(unless found-a-use
	  (let ((allowable-assertions (loop with assertions = nil
					  for component in running
					  do (ask `[allowable-events-for ,component ?]
						  #'(lambda (just)
						      (push (ask-database-predication just) assertions)))
					  finally (return assertions))))
	    (let ((r (most-specific-component running)))
	      (tell `[bad-event-detected ,event-name ,event-type ,r ,(copy-seq args)]
		    :justification `(not-member-of-allowed ,allowable-assertions nil nil))
	      )))))))

;;; Note
;;; Really what we should do is have the behavioral model make an assertion saying these are the allowable events
;;; and check if its in that set.  This should be dependent on the selected-model assertion
;;; Then the bad-event detected can be dependent on that assertion, so when the behavioral model is switched
;;; the bad-event-detected will go out.  The new alternative model will assert a different such assertion which
;;; will either cause a bad-event deduction (and more backtracking) or not.



(defvar *attack-models* nil)

(defmacro define-attack-model (name &key attack-types vulnerability-mapping parents)
  `(progn
     (pushnew ',name *attack-models*)
     (defun ,name (compnent)
       ,@(when (and (null attack-types) (null parents))
           `((declare (ignore compnent))))
       ,@(loop for (attack-type a-priori-probability) in attack-types
               collect `(tell `[attack ,compnent ,',name ,',attack-type] :justification :premise)
               collect `(tell [a-priori-probability-of ,attack-type :true ,a-priori-probability] :justification :premise))
       ,@(loop for (vulnerability . attacks) in vulnerability-mapping
               append (loop for attack in attacks
                            collect `(tell [vulnerability-enables-attack ,vulnerability ,attack] :justification :premise)))
       ,@(loop for parent in parents
               collect `(apply-attack-model ',parent compnent))
       )))

(defun apply-attack-model (name component)
  (funcall name component))

;;;; building the equivalent ideal model

;;; predicates to map over:
;;;
;;; component
;;; resource
;;; possible-model
;;; a-priori-probability-of
;;; conditonal-probability
;;; set-up--evidence-nodes
;;;
;;; the dynamic part:
;;; selected-model

(defun build-ideal-model (ensemble)
  (let ((ideal-diagram nil))
    (setq ideal-diagram (build-nodes ensemble ideal-diagram 'component))
    (setq ideal-diagram (build-nodes ensemble ideal-diagram 'resource))
    (setq ideal-diagram (build-nodes ensemble ideal-diagram 'attack))
    (do-priors ensemble ideal-diagram)
    (do-conditional-probabilities ensemble ideal-diagram)
    (do-attack-conditional-probabilities ensemble ideal-diagram)
    ideal-diagram))

(defun build-nodes (componnet ideal-diagram node-type)
  (ask `[,node-type ,componnet ?name ?node]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (let ((states nil)
		 (qualified-name (if (eql node-type 'attack) ?node (qualified-name ?node))))
	     (unless (eql node-type 'attack)
	       (ask [possible-model ?node ?model-name]
		    #'(lambda (stuff)
			(declare (ignore stuff))
			(push ?model-name states))))
             (when (and (null states) (eql node-type 'attack))
               (setq states (list :false :true)))
	     (unless (and (eql node-type 'component)
			  (or (typep ?node 'split-object)
			      (typep ?node 'join-object)
			      (typep ?node 'primitive-branch-mixin)))
	       (multiple-value-bind (new-diagram ideal-node)
		   (ideal:add-node ideal-diagram
				   ;; if the node type is attack, the thing that
				   ;; matches ?node is the attack name
				   ;; otherwise we want the node anyway
				   :name qualified-name
				   :type :chance
				   :relation-type :prob
				   :state-labels states)
		 (setq ideal-diagram new-diagram)
		 (case node-type
		   (component
		    (setq ideal-diagram (build-corresponding-component-nodes
					 qualified-name ideal-node states ideal-diagram)))
		;; (resource
		;; (setq ideal-diagram (build-corresponding-resource-nodes
		   ;; (object-name ?node)
		   ;; ideal-node
		   ;; states
		   ;;ideal-diagram
		   ;; )))
		   ))))))
  ideal-diagram)

(defun build-corresponding-component-nodes (parent-node-name parent-node states ideal-diagram)
  (loop for state in states
        for new-name = (make-name parent-node-name state)
        do (multiple-value-bind (new-diagram child-node)
			        (ideal:add-node ideal-diagram
					        :name new-name
					        :type :chance
					        :relation-type :prob
					        :state-labels '(:false :true))
             (setq ideal-diagram new-diagram)
             ;; Add an arc from the parent node to it
             (ideal:add-arcs child-node (list parent-node))
             ;; Set the conditional probabilities on the child evidence node
             (ideal:for-all-cond-cases (parent-case parent-node)
               (let ((correct-corresponding-case
                      (eql (ideal:state-in parent-case)
                           (ideal:get-state-label parent-node state))))
                 (ideal:for-all-cond-cases (child-case child-node)
                   (let ((true-case (eql (ideal:state-in child-case)
                                         (ideal:get-state-label child-node :true))))
                     (if correct-corresponding-case
                       (setf (ideal:prob-of child-case parent-case)
                             (if true-case 1 0))
                       (setf (ideal:prob-of child-case parent-case)
                             (if true-case 0 1)))))))))
  ideal-diagram)

(defun build-corresponding-resource-nodes (original-node-name original-node states ideal-diagram)
  (let ((new-nodes nil) (n-nodes 0))
    (loop for state in states
          for new-name = (make-name original-node-name state)
          do (multiple-value-bind (new-diagram new-node) (ideal:add-node ideal-diagram
                                                                         :name new-name
                                                                         :noisy-or t
                                                                         :noisy-or-subtype :binary
                                                                         :state-labels '(:false :true))
               (setq ideal-diagram new-diagram)
               ;; Add an arc from the new node to the original
               (incf n-nodes)
               (push new-node new-nodes)))
    ;; make the new-nodes support the original
    (ideal:add-arcs original-node new-nodes)
    ;; Set the conditional probabilities on the new evidence node
    (ideal:for-all-cond-cases (new-case new-nodes)
      (let* ((number-true (loop for case on new-case
                                count (eql (ideal:state-in case)
                                           (ideal:get-state-label (ideal:node-in case) :true))))
             (how-much (if (zerop number-true) (/ 1 (float n-nodes)) (/ 1 (float number-true)))))
        (ideal:for-all-cond-cases (original-case original-node)
          (let* ((node (ideal:node-in original-case))
                 (state (ideal:state-in original-case))
                 (node-name (ideal:node-name node))
                 (state-name (ideal:label-name state))
                 (corresponding-case-name (make-name node-name state-name))
                 (value-to-set-this-time how-much))
            (unless (loop for (node-of-part . part-state) in new-case
                          for part-name = (ideal:node-name node-of-part)
                          thereis (and (eql part-name corresponding-case-name)
                                       (eql part-state (ideal:get-state-label node-of-part :true))))
              (unless (zerop number-true)
                (setq value-to-set-this-time 0)))
            (setf (ideal:prob-of original-case new-case) value-to-set-this-time)

            (format t "~%Setting ~a ~a <- ~{~a ~a~^ ~} to ~a"
                    (ideal:node-name (ideal:node-in original-case))
                    (ideal:label-name (ideal:state-in original-case))
                    (loop for case on new-case
                          collect (ideal:node-name (ideal:node-in case))
                          collect (ideal:label-name (ideal:state-in case)))
                    value-to-set-this-time)
            ))))
    ideal-diagram))

;;; question:
;;; Used to be (if (symbolp ?resource) ?resource (object-name ?resource)) instead of just ?resource-name
;;; why was that?
;;; Ideal insists that node names be symbols.
;;; So we'll arrange for every object in the system
;;; to have a qualified name (i.e. it's dotted pathname) that is unique
;;; to it.
;;; Components and Resources have actual objects
;;; Modes of these and Attacks just have names

(defun do-priors ( compnent ideal-diagram)
  (ask `[and [resource , compnent ? ?resource]
	     [a-priori-probability-of ?resource ?model ?probability]]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (let* ((ideal-node (ideal:find-node (qualified-name ?resource) ideal-diagram))
		  (state-label (ideal:get-state-label ideal-node ?model)))
             (unless (ideal:node-predecessors ideal-node)
	       (ideal:for-all-cond-cases (case ideal-node)
	         (when (eql (ideal:state-in case) state-label)
		   (setf (ideal:prob-of case nil) ?probability))))))))

(defun do-conditional-probabilities (component ideal-diagram)
  ;; first add arcs
  (ask `[component ,component ? ?component]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (unless (or (typep ?component 'split-object)
		       (typep ?component 'join-object)
		       (typep ?component 'primitive-branch-mixin))
	   (let ((component-node (ideal:find-node (qualified-name ?component) ideal-diagram)))
	     (ask [uses-resource ?component ?resource]
		#'(lambda (stuff)
		    (declare (ignore stuff))
		    (let ((resource-node (ideal:find-node (qualified-name ?resource) ideal-diagram)))
		      (ideal:add-arcs component-node (list resource-node)))))))))
  ;; now build conditional probabilities
  (ask [conditional-probability ?component ?c-model ?dependency-list ?probability]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (let* ((conditioning-case nil)
		  (resource-nodes nil)
		  (component-node (ideal:find-node (qualified-name ?component) ideal-diagram))
		  (component-label (ideal:get-state-label component-node ?c-model)))
	     ;; The dependency list is a list of pairs (conses) of a resource object and a mode name for
	     ;; that object.
	     (loop for (resource . resource-mode) in ?dependency-list
		 for resource-name =  (qualified-name resource)
		 do (push (ideal:find-node resource-name ideal-diagram) resource-nodes)
		 collect resource-name into resource-names
		 collect resource-mode into resource-states
		 finally (setq conditioning-case
			   (ideaL:make-cond-case resource-names resource-states ideal-diagram)))
	     (ideal:for-all-cond-cases (c-case component-node)
	       (when (eql (ideal:state-in c-case) component-label)
		 (ideal:for-all-cond-cases (r-case resource-nodes)
		   (when (equal r-case conditioning-case)
		     (setf (ideal:prob-of c-case r-case) ?probability)))))))))

;;; controls whether progress is reported as you go
(defvar *report-out-loud* nil)

(defun do-attack-conditional-probabilities (component ideal-diagram)
  ;; first add arcs
  (flet ((print-an-assignment (type resource resource-model-name attack-case prob)
           (when *report-out-loud*
             (format t "~%Setting ~a prob of ~a ~a <- ~{~a ~a~^, ~} to ~5,4f"
                     type
                     resource resource-model-name
                     (loop for a on attack-case
                           for a-name = (ideal:node-name (ideal:node-in a))
                           for s-name = (ideal:label-name (ideal:state-in a))
                           collect a-name collect s-name)
                     prob))))
    (ask `[resource ,component ? ?resource]
         #'(lambda (stuff)
             (declare (ignore stuff))
             (let ((resource-node (ideal:find-node (qualified-name ?resource) ideal-diagram))
                   (cond-case-alist nil)
                   (attack-nodes nil))
               (flet ((add-attack-entry (attack-case prob)
                        (let ((entry (assoc attack-case cond-case-alist :test #'equal)))
                          (unless entry
                            (setq entry (list (copy-tree attack-case) 0))
                            (push entry cond-case-alist))
                          (incf (second entry) prob))))
                 (ask [resource-might-have-been-attacked ?resource ?attack]
                      #'(lambda (just)
                          (declare (ignore just))
                          (let ((attack-node (ideal:find-node ?attack ideal-diagram)))
                            (push attack-node attack-nodes))))
                 (ideal:add-arcs resource-node attack-nodes)
                 (ideal:for-all-cond-cases (resource-case resource-node)
                   (let* ((model (ideal:state-in resource-case))
                          (resource-model-name (ideal:label-name model))
                          (got-an-assignment? nil))
                     (unless (eql resource-model-name 'normal)
                       (when attack-nodes
                         (ideal:for-all-cond-cases (attack-case attack-nodes)
                           (let ((probs nil))
                             (loop for attack on attack-case
                                   for attack-node = (ideal:node-in attack)
                                   for attack-name = (ideal:node-name attack-node)
                                   for state = (ideal:state-in attack)
                                   for state-name = (ideal:label-name state)
                                   when (eql state-name :true)
                                   do
                                   (ask `[attack-implies-compromised-mode ,attack-name ?resource ,resource-model-name ?probability]
                                        #'(lambda (just)
                                            (declare (ignore just))
                                            (push ?probability probs))))
                             (cond
                              (probs
                               (setq got-an-assignment? t)
                               (loop with neg-prob = 1
                                     for prob in probs
                                     do (setq neg-prob (* neg-prob (- 1 prob)))
                                     finally (let ((final-prob (- 1 neg-prob)))
                                               (print-an-assignment 'calculated ?resource resource-model-name attack-case final-prob)
                                               (setf (ideal:prob-of resource-case attack-case) final-prob)
                                               (add-attack-entry attack-case final-prob))))
                              (t (print-an-assignment 'calculated ?resource resource-model-name attack-case 0)
                                 (setf (ideal:prob-of resource-case attack-case) 0)
                                 (add-attack-entry attack-case 0))))))
                       (unless got-an-assignment?
                         (ask `[a-priori-probability-of ?resource ,resource-model-name ?probability]
                              #'(lambda (just)
                                  (declare (ignore just))
                                  (add-attack-entry nil ?probability)
                                  (print-an-assignment 'a-priori ?resource resource-model-name nil ?probability)
                                  (setf (ideal:prob-of resource-case nil) ?probability)))))))
                 (ideal:for-all-cond-cases (resource-case resource-node)
                   (when (eql (ideal:label-name (ideal:state-in resource-case)) 'normal)
                     (loop for (cond-case prob) in cond-case-alist
                           do (setq prob (- 1 prob))
                           (print-an-assignment 'residual ?resource 'normal cond-case prob)
                           (setf (ideal:prob-of resource-case cond-case) prob))))))))))




#+genera (import (mapcar #'(lambda (symbol) (intern (string-upcase symbol) 'clos))
                         (list "defclass" "defmethod" "with-slots" "setf" "make-instance")))


(defclass search-control ()
  ((component-name :initarg :component-name :accessor component-name)
   (component :initarg :component :accessor component)
   (nogoods :initform nil :accessor nogoods :initarg :nogoods)
   (ideal-diagram :initarg :ideal-diagram :accessor ideal-diagram)
   (resource-nodes :initarg :resource-nodes :accessor resource-nodes :initform nil)
   (component-nodes :initarg :component-nodes :accessor component-nodes :initform nil)
   (attack-nodes :initarg :attack-nodes :accessor attack-nodes :initform nil)
   (join-tree :initarg :join-tree :accessor join-tree)
   (join-tree-valid? :initform nil :accessor join-tree-valid?)
   (visited-states :initform nil :accessor visited-states)
   (remaining-states :initform nil :accessor remaining-states)
   (solution-states :initform nil :accessor solution-states)
   (bayes-calls :initform 0 :accessor bayes-calls)))

(defmethod report ((sc search-control) &optional (show-solutions nil))
   (initialize-resources-and-components sc)
   (format t "~%The Bayesian solver was called ~d times" (bayes-calls sc))
   (format t "~%There are ~d diagnoses" (length (solution-states sc)))
   (format t "~%There are ~d nogoods" (length (nogoods sc)))
   (ideal:diag-display-beliefs (resource-nodes sc))
   (ideal:diag-display-beliefs (component-nodes sc))
   (ideal:diag-display-beliefs (attack-nodes sc))
   (when show-solutions
   (loop for (prob . assertions) in (solution-states sc)
         do (format t "~%~5,4f ~:{[~a ~a]~^~}" prob
                    (loop for a in assertions collect
                          (with-statement-destructured (component model) a (list component model)))))))

(defmethod add-node-to-diagram ((sc search-control) new-node new-diagram)
  (with-slots (ideal-diagram join-tree-valid?) sc
    (unless (member new-node ideal-diagram)
      (setq join-tree-valid? nil))
    (setq ideal-diagram new-diagram)
    ))

(defmethod compute-probabilities ((sc search-control))
  (incf (bayes-calls sc))
  (unless (join-tree-valid? sc)
    (setf (join-tree sc) (ideal:create-jensen-join-tree (ideal-diagram sc))))
  (ideal:jensen-infer (join-tree sc) (ideal-diagram sc)))

(defmethod initialize-resources-and-components ((sc search-control))
  (with-slots (resource-nodes component-nodes attack-nodes component component-name ideal-diagram remaining-states) sc
    (unless (and resource-nodes component-nodes)
      (ask `[resource ,component ? ?resource]
	   #'(lambda (just)
	       (declare (ignore just))
	       (push (ideal:find-node (qualified-name ?resource) ideal-diagram) resource-nodes)))
      (ask `[attack ,component ?name ?attack-type]
           #'(lambda (just)
               (declare (ignore just))
               (push (ideal:find-node ?attack-type ideal-diagram) attack-nodes)))
      (let ((all-components nil))
	;; give each possible assumption a unique bit
	(let ((current-bit-position 1))
	  (ask `[and [component ,component ?sub-component-name ?sub-component]
		     ;; Note that we only assign bits to things that
		     ;; were actually involved in the computation
		     ;; I.e. that actually have already started
		     [execution-status ?sub-component started]
		     [possible-model ?sub-component ?y]]
	       #'(lambda (just)
		   (declare (ignore just))
		   (pushnew ?sub-component all-components)
		   (let ((assertion (tell [selected-model ?sub-component ?y] :justification :none)))
		     (setf (bit-pattern assertion) current-bit-position)
		     (setq current-bit-position (* current-bit-position 2))
		     (push (ideal:find-node (qualified-name ?sub-component) ideal-diagram) component-nodes)
		     ))))
	(labels ((do-one (remaining-components partial-state)
		   (if (null remaining-components)
		       (let ((bit-vector (bit-vector-from-assertion-set partial-state)))
			 (push (cons bit-vector partial-state) remaining-states))
		     (destructuring-bind (first-component . rest-components) remaining-components
		       (ask `[possible-model ,first-component ?model]
			    #'(lambda (just)
				(declare (ignore just))
				(let ((state-predication (tell `[selected-model ,first-component ?model]
							       :justification :none)))
				  (do-one rest-components (cons state-predication partial-state)))))))))
	  (do-one all-components nil))))))

(defmethod ideal-node-from-clause ((sc search-control) clause)
  (multiple-value-bind (mnemonic conseqeuent) (destructure-justification clause)
    (declare (ignore mnemonic))
    (ideal-node-from-assertion sc conseqeuent)))

(defmethod ideal-node-from-assertion ((sc search-control) assertion)
  (with-statement-destructured (component model) assertion
    (ideal:find-node (make-name (qualified-name component) model) (ideal-diagram sc))))

(defmethod belief-of-component-model ((sc search-control) component model)
  (let* ((node (ideal:find-node (qualified-name component) (ideal-diagram sc)))
         (state (ideal:get-state-label node model)))
    (ideal:for-all-cond-cases (case node)
      (when (eql (ideal:state-in case) state)
        (return-from belief-of-component-model (ideal:belief-of case))))))

(defun belief-of-binary-node (node)
  (let ((true-case (ideal:get-state-label node :true)))
    (ideal:for-all-cond-cases (case node)
      (when (eql (ideal:state-in case) true-case)
	(return-from belief-of-binary-node (ideal:belief-of case))))))

(defmethod belief-of-attack-node ((sc search-control) attack-name)
  (let ((attack-node (ideal:find-node attack-name (ideal-diagram sc))))
    (belief-of-binary-node attack-node)))

(defun relevant? (assertion)
  (not (zerop (bit-pattern assertion))))

(defmethod handle-nogood ((sc search-control) condition &key (stupid nil))
  (multiple-value-bind (nogood assumptions) (nogood-from-condition condition)
    (add-new-nogood sc nogood)
    (if stupid
	(values assumptions)
	(let ((nodes nil))
	  ;; pin all the selected model nodes as true except for those involved in the nogood
	  (multiple-value-bind (selection-alist negations) (build-selection-map sc)
	    (loop for (nil assertion) in selection-alist
		  for node = (ideal-node-from-assertion sc assertion)
		  unless (member assertion nogood)
		    do (setf (ideal:node-state node) (ideal:get-state-label node :true))
		       (push node nodes))
	    ;; also pin all the nodes corresponding to negated selected model assertions as false
	    (loop for (nil . assertions) in negations
		  do (loop for assertion in assertions
			   for node = (ideal-node-from-assertion sc assertion)
			   do (push node nodes)
			      (setf (ideal:node-state node) (ideal:get-state-label node :false))))
	    (compute-probabilities sc)
	    (loop with least-likely-assumption = nil
		  and least-prob = nil
		  for assertion in nogood
		  for assumption in assumptions
		  for node = (ideal-node-from-assertion sc assertion)
		  for prob = (belief-of-binary-node node)
		  when (or (null least-prob) (< prob least-prob))
		    do (setq least-prob prob
			     least-likely-assumption assumption)
		  finally (ideal:remove-evidence nodes)
			  (return (list least-likely-assumption))))))))

(defun nogood-from-condition (condition)
  #-sbcl(declare (values assertions assumptions))
  (let ((assumptions (tms-contradiction-non-premises condition)))
    (let ((real-assumptions nil)
	  (real-assertions nil))
      (loop for clause in assumptions
	  for assertion = (multiple-value-bind (mnemonic assertion)
			      (destructure-justification clause)
			    (declare (ignore mnemonic))
			    assertion)
	  when (relevant? assertion)
	  do (push clause real-assumptions)
	     (push assertion real-assertions))
    (values real-assertions
	    real-assumptions))))

(defun bit-vector-from-assertion-set (assertions)
  (loop with answer = 0
	for assertion in assertions
	do (setq answer (logior answer (bit-pattern assertion)))
	finally (return answer)))

(defun bit-vector-subset (v1 v2) (eql v2 (logior v1 v2)))
(defun bit-vector-superset (v1 v2) (eql v1 (logior v1 v2)))

(defmethod add-new-nogood ((sc search-control) nogood)
  (with-slots (nogoods remaining-states solution-states) sc
    (let ((bit-vector (bit-vector-from-assertion-set nogood)))
      (if (member bit-vector nogoods :test #'bit-vector-superset :key #'car)
	  (values nil nogoods)
	  (progn
            (when *report-out-loud*
	      (format t "~%Adding nogood")
	      (loop for thing in nogood
		  do (terpri)
		     (format t "  ")
		     (ji::print-without-truth-value thing)))
	    (push (cons bit-vector nogood) nogoods)
	    (setq remaining-states (delete bit-vector remaining-states :test #'bit-vector-subset :key #'car))
            (unless (and (null remaining-states) (null solution-states))
              (update-ideal-with-nogood sc nogood))
	    (when (null remaining-states)
              (loop for thing in nogood do (unjustify thing))
              (throw 'no-remaining-states (values)))
	    (values t nogoods))))))

(defmethod update-ideal-with-nogood ((sc search-control) nogood)
  (let ((nodes (loop for assertion in nogood
		   when (relevant? assertion)
		   collect (ideal-node-from-assertion sc assertion))))
    ;; build a new node representing the nogood
    (let* ((new-node (add-and-node sc nodes "CONTRDICTION-"))
           (false-case (ideal:get-state-label new-node :false)))
      ;; pin the contradiction at false
      (setf (ideal:node-state new-node) false-case))))

(defmethod add-nodes-for-solutions ((sc search-control))
  (let ((alist (loop for state in (solution-states sc)
                     for new-node = (add-node-for-solution sc state)
                     collect (cons new-node state))))
    (when *report-out-loud* (format t "~%Computing final probabilities"))
    (compute-probabilities sc)
    (loop for entry in alist
          for node = (first entry)
          for belief = (belief-of-binary-node node)
          do (setf (first entry) belief))
    (setq alist (sort alist #'> :key #'car))
    (setf (solution-states sc) alist)))

(defmethod add-node-for-solution ((sc search-control) solution)
  (let ((nodes (loop for assertion in solution
		   when (relevant? assertion)
		   collect (ideal-node-from-assertion sc assertion))))
    (add-and-node sc nodes "SOLUTION-")))

(defmethod add-and-node ((sc search-control) nodes mnemonic)
  ;; build a node for the solution
  (multiple-value-bind (new-diagram new-node) (ideal:add-node (ideal-diagram sc)
			                                      :name (gentemp mnemonic)
			                                      :type :chance
			                                      :relation-type :prob
			                                      :state-labels '(:true :false))
    (add-node-to-diagram sc new-node new-diagram)
    (let ((true-case (ideal:get-state-label new-node :true)))
      ;; make the new node depend on the old-nodes
      (ideal:add-arcs new-node nodes)
      ;; make the conditional probability matrix be "Boolean AND"
      (ideal:for-all-cond-cases (child-states nodes)
        (let ((all-true (loop for case on child-states
                              always (eql (ideal:state-in case)
                                          (ideal:get-state-label (ideal:node-in case) :true)))))
          (ideal:for-all-cond-cases (parent-case new-node)
            (if (eql (ideal:state-in parent-case) true-case)
              ;; parent case is true
              (if all-true
                ;; child is all true
                (setf (ideal:prob-of parent-case child-states) 1)
                ;; child is at least one false
                (setf (ideal:prob-of parent-case child-states) 0))
              ;; parent is false
              (if all-true
                ;; all children are true
                (setf (ideal:prob-of parent-case child-states) 0)
                ;; at least one child false
                (setf (ideal:prob-of parent-case child-states) 1)))))))
    new-node))

(defmethod find-solutions ((search-control search-control) &optional (do-all-solutions t))
  (handler-bind
      ((ltms:ltms-contradiction
	#'(lambda (condition)
	    (let ((clauses-to-retract (handle-nogood search-control condition)))
	      (multiple-value-bind (mnemonic assertion)
		  (destructure-justification (first clauses-to-retract))
		(declare (ignore mnemonic))
		(when *report-out-loud*
		  (with-statement-destructured (component model) assertion
		    (format t "~%Retracting Model ~a for ~a" model component))))
	      (invoke-restart
	       :unjustify-subset clauses-to-retract)))))
    (catch 'no-remaining-states
      ;; commented out the search for the best solution
      ;;(loop for guy-to-assert = (make-selection search-control)
      ;; until (null guy-to-assert)
      ;; finally (capture-solution search-control))
      ;; now enumerate remaining-states for exhaustive coverage
      (handler-bind
	  ((ltms:ltms-contradiction
	    #'(lambda (condition)
		(let ((clauses-to-retract (handle-nogood search-control condition :stupid t)))
		  (invoke-restart
		   :unjustify-subset clauses-to-retract)))))
	;; try state will thow to no-remaining-states when we run out
	(loop doing (try-state search-control)))))
  (remove-all-selected-components search-control)
  (remove-all-component-evidence search-control)
  (if do-all-solutions
      (add-nodes-for-solutions search-control)
    (compute-probabilities search-control))
  search-control)

(defun set-up-search-control (component-name component attack-models)
  (when attack-models
    (loop for attack-model in attack-models
	do (apply-attack-model attack-model component)))
  (let* ((ideal-model (build-ideal-model component))
	 (search-control (make-instance 'search-control
			   :component component
			   :component-name component-name
			   :ideal-diagram ideal-model)))
    (initialize-resources-and-components search-control)
    search-control))

(defun create-initial-inputs (component)
  (let ((input-descriptions (find-initial-inputs component)))
    (loop for (nil name component) in input-descriptions
	for new-name = (gentemp (format nil "~a-" name))
	do (tell `[input ,name ,component ,new-name])
	   )))


;;;(defun init-case (ensemble-name attack-models)
;;;  (clear)
;;;  (clrhash *component-map*)
;;;  (let* ((sc (set-up-search-control ensemble-name attack-models))
;;;	 (ensemble (ensemble sc)))
;;;    (values sc ensemble)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun all-output-ports (component)
  (let ((names nil))
    (ask `[port output ,component ?port-name]
	 #'(lambda (stuff)
	     (declare (ignore stuff))
	     (push ?port-name names)))
    names))

(defun successors-of-component (component)
  (let ((successors nil))
    (ask `[dataflow ? ,component ? ?successor]
	 #'(lambda (stuff)
	     (declare (ignore stuff))
	     (push ?successor successors)))
    successors))

(defun input-is-present (component port-name)
  (ask `[input ,port-name ,component ?value]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (return-from input-is-present (values t)))))


(defun all-inputs-are-present (component)
  (ask `[port input ,component ?port-name]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (unless (input-is-present component ?port-name)
	     (return-from all-inputs-are-present (values nil)))))
  t)

(defun input-named (port-name component)
  (ask `[input ,port-name ,component ?value]
       #'(lambda (stuff)
	   (return-from input-named (values ?value (ask-database-predication stuff))))
       :do-backward-rules nil
       :do-questions nil
       )
  nil)

(defun output-named (port-name component)
  (ask `[output ,port-name ,component ?value]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (return-from output-named (values ?value)))))

(defrule component-ready (:forward)
  if [and [prerequisites-satisfied ?component]
	  [all-inputs-present ?component]
	  [all-controlflows-satisfied ?component]]
  then [execution-status ?component ready])

;;; Question: Do we really want this to be automagic
;;; or do we want to control granularity of modeling
;;; could be a predicate method also.
(defrule expand-inside (:forward)
  if [and [execution-status ?component started]
	  [behavior ?component ?type]
	  (typep ?component 'compound-component)
	  (not (expanded? ?component))]
  then (build-implementation ?type ?component))

(defrule splits-ready-on-inputs (:forward)
  if [and [component ?parent ?name ?component]
	  [all-inputs-present ?component]
	  [all-controlflows-satisfied ?component]
	  [component-type ?component split]]
  then [execution-status ?component ready])

(defrule joins-ready-on-inputs (:forward)
  if [and [component ?parent ?name ?branch]
	  [all-inputs-present ?branch]
	  [all-controlflows-satisfied ?branch]
	  [component-type ?branch join-branch]
	  [branch-of ?branch-name ?join ?branch]]
  then [and [selected-branch ?join ?branch]
	    [execution-status ?branch ready]
	    [execution-status ?branch started]
	    [execution-status ?branch completed]
	    [execution-status ?join ready]
	    [execution-status ?join started]
	    [execution-status ?join completed]
	    ])

(defrule join-branch-propagates-when-selected (:forward)
    if [and [component ?parent ?name ?join]
	    [component-type ?join join]
	    [selected-branch ?join ?branch]
	    [input ?input-name ?branch ?value]]
    then [output ?input-name ?join ?value])

(defrule split-branch-completes-when-selected (:forward)
  if [and [component ?parent ?name ?component]
	  [component-type ?component split]
	  [execution-status ?component ready]
	  [selected-branch ?component ?branch]]
  then [and [execution-status ?branch ready]
	    [execution-status ?branch started]
	    [execution-status ?branch completed]
	    [execution-status ?component started]
	    [execution-status ?component completed]])

(defrule finished-when-outputs-and-cfs (:forward)
  if [and [all-outputs-present ?component]
	  [all-terminal-controlflows-satisfied ?component]]
  then [execution-status ?component completed])

;;; This is here only to allow stepping along
;;; some sort of simulation unattached to execution
;;; Normally the hooks on the simulation would
;;; make these assertions.

(defrule create-outputs-when-completed (:forward)
  if [and [component ?parent ?name ?component] :support ?f1
	  ;; only create outputs when there's a model
	  [selected-model ?component normal]
	  [execution-status ?component completed] :support ?f2
	  ]
  then (build-component-outputs ?component (list ?f1 ?f2)))

(defun build-component-outputs (component support)
  (when (all-inputs-are-present component)
    (flet ((create-output-for-port (component port-name)
	     ;; prevent duplicates by checking if its there already
	     (unless (output-named port-name component)
	       (multiple-value-bind (input-of-same-name input-just) (input-named port-name component)
		 (let ((his-support (if input-of-same-name (cons input-just support))))
		   (let ((output (or input-of-same-name (gentemp (format nil "~a-" port-name)))))
		     (tell `[output ,port-name ,component ,output]
			   :justification `(propagate-or-create-output ,his-support))))))))
      (loop for port-name in (all-output-ports component)
	  do (create-output-for-port component port-name)))))

;;; This is dead code
;;;(defun create-component-outputs (ensemble)
;;;  (multiple-value-bind (inputs components) (find-initial-inputs ensemble)
;;;    (declare (ignore inputs))
;;;    (let ((components-done nil)
;;;	  (components-to-do components))
;;;      (flet ((create-output-for-port (component port-name)
;;;	       (let ((input-of-same-name (input-named port-name component)))
;;;		 (let ((output (or input-of-same-name (gentemp (format nil "~a-" port-name)))))
;;;		   (tell `[output ,port-name ,component ,output])))))
;;;	(loop for component = (pop components-to-do)
;;;	    while component
;;;	    when (and (all-inputs-are-present component)
;;;		      (not (member component components-done)))
;;;	    do (loop for port-name in (all-output-ports component)
;;;		   do (create-output-for-port component port-name))
;;;	       (push component components-done)
;;;	       (let ((my-successors (successors-of-component component)))
;;;		 (loop for successor in my-successors
;;;		     unless (member successor components-done)
;;;		     do (setq components-to-do (nconc components-to-do (list successor))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defmethod remove-all-selected-components ((sc search-control))
  (ask `[component ,(component sc) ?sub-component-name ?sub-component]
       #'(lambda (just)
	   (declare (ignore just))
	   (ask [selected-model ?sub-component ?]
		#'(lambda (just)
		    (let ((predication (ask-database-predication just)))
		      (loop for current-justification = (current-justification predication)
			  while current-justification
			  do (unjustify predication current-justification))))))))

(defmethod try-state ((sc search-control))
  (with-slots (remaining-states) sc
    ;; remove all current state information
    (remove-all-selected-components sc)
    (when (null remaining-states)
      (throw 'no-remaining-states (values)))
    (let ((state-to-try (cdr (first remaining-states))))
      ;; (format t "~%Next state ~d states left" (length remaining-states))
      (format t "~%Trying state ~{~a~^, ~}" state-to-try)
      (loop with assertions-made = nil
	  for assertion in state-to-try
	  for interned-assertion = (tell assertion :justification :none)
	  do (push interned-assertion assertions-made)
	  do (justify interned-assertion +true+ :assumption)
	     (with-statement-destructured (component model) interned-assertion
	       (declare (ignore model))
	       (tell `[execution-status ,component completed]))
	  unless (loop for assertion in assertions-made
		     always (eql (predication-truth-value assertion) +true+))
	  return (values)
	  finally (return (capture-solution sc))))))

(defun is-subcomponent (parent putative-child)
  (labels ((next-level (this-parent)
	     (when (member putative-child (components this-parent))
	       (return-from is-subcomponent (values t)))
	     (loop for next-parent in (components this-parent)
		 do (next-level next-parent))))
    (next-level parent)
    (values nil)))

(defun walk-component-hierarchy (component function)
  (labels ((next-level (sub-component)
	     (funcall function sub-component)
	     (when (typep sub-component 'compound-component)
	       (loop for next-component in (components sub-component)
		 do (next-level next-component)))))
    (next-level component)))

(defmethod capture-solution ((sc search-control))
  (with-slots (solution-states remaining-states component) sc
    (let ((solution nil))
      (flet ((check-a-component (this-component)
	       (unless (eql this-component component)
		 (ask `[selected-model ,this-component ?model]
		      #'(lambda (just)
			  (push (ask-database-predication just) solution))))))
	(walk-component-hierarchy component #'check-a-component))
      (when *report-out-loud* (format t "~%Diagnosis found: ~{~%  ~a~^~}" solution))
      (push solution solution-states)
      ;; (break "Remaining States ~d" (length remaining-states))
      (let ((bit-vector (bit-vector-from-assertion-set solution)))
	(setq remaining-states (delete bit-vector remaining-states :test #'eql :key #'car))
	(when (null remaining-states)
	  (throw 'no-remaining-states (values)))
	(values solution)))))

(defmethod make-selection ((sc search-control))
  (multiple-value-bind (selection-alist negations components) (build-selection-map sc)
    (let ((nodes-affected (update-ideal-for-selection-map sc selection-alist negations)))
      (let ((best-probability 0) (best-component nil) (best-model nil))
        (loop for component in components
              unless (assoc component selection-alist)
              do (ask `[possible-model ,component ?model]
                      #'(lambda (just)
                          (let* ((node (ideal-node-from-assertion sc (ask-database-predication just)))
                                 (prob (belief-of-binary-node node)))
                            (when (> prob best-probability)
                              (setq best-probability prob
                                    best-component component
                                    best-model ?model))))))
        (ideal:remove-evidence nodes-affected)
        (when best-model
          (when *report-out-loud*
            (format t "~%Choosing model ~a for ~a" best-model best-component))
          (tell `[selected-model ,best-component ,best-model] :justification :assumption))))))

(defmethod build-selection-map ((sc search-control))
  (with-slots (component) sc
    (let ((selection-alist nil) (components nil) (negations nil))
      (ask `[component ,component ?sub-component-name ?sub-component]
           #'(lambda (just)
               (declare (ignore just))
               (push ?sub-component components)
               (let ((found-it nil))
                 (ask [selected-model ?sub-component ?model]
                      #'(lambda (just)
                          (setq found-it t)
                          (push (list ?sub-component (ask-database-predication just)) selection-alist)))
                 (unless found-it
                   (push (list ?sub-component) negations)
                   (ask `[not [selected-model ?sub-component ?]]
                        #'(lambda (just)
                            (let ((entry (assoc ?sub-component negations)))
                              (push (ask-database-predication just) (cdr entry)))))))))
      (values selection-alist negations components))))

(defmethod update-ideal-for-selection-map ((sc search-control) selection-alist negations)
  (let ((nodes nil))
    (loop for (nil assertion) in selection-alist
          for node = (ideal-node-from-assertion sc assertion)
          do (setf (ideal:node-state node) (ideal:get-state-label node :true))
          (push node nodes))
    (loop for (nil . assertions) in negations
          do (loop for assertion in assertions
                   for node = (ideal-node-from-assertion sc assertion)
                   do (setf (ideal:node-state node) (ideal:get-state-label node :false))
                       (push node nodes)))
    (compute-probabilities sc)
    (values nodes)))

(defmethod remove-all-component-evidence ((sc search-control))
  (let ((nodes nil))
    (with-slots (component) sc
      (ask `[and [component ,component ?sub-component-name ?sub-component] [possible-model ?sub-component ?y]]
           #'(lambda (just)
               (declare (ignore just))
               (let* ((assertion (tell [selected-model ?sub-component ?y] :justification :none))
                      (ideal-node (ideal-node-from-assertion sc assertion)))
                 (push ideal-node nodes)))))
    (ideal:remove-evidence nodes)))

(defun component-uses-resource (model)
  (ask `[uses-resource ,model ?resource]
       #'(lambda (just)
           (declare (ignore just))
           (return-from component-uses-resource (values ?resource))))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Gathering information about the ensemble
;;;
;;;  Fix?
;;;  Currently we have a duplication of representation:
;;;   Once as predications
;;;   Again within the data-structures
;;;   These routines make queries
;;;   But the same is probably more quickly accessible by traversing
;;;   the data structures
;;;   These are currently only used by graph-model in the editor file
;;;   which is pretty much obsolete at the moment.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;l

(defun components-in (diagram)
  (let ((answers nil))
    (ask `[component ,diagram ?component-name ?component]
         #'(lambda (just)
             (declare (ignore just))
             (push ?component answers)))
    answers))

(defun resources-in (diagram)
  (let ((answers nil))
    (ask `[resource ,diagram ?resource-name ?component]
         #'(lambda (just)
             (declare (ignore just))
             (push ?component answers)))
    answers))

(defun attacks-in (diagram)
  (let ((answers nil))
    (ask `[attack ,diagram ?name ?attack-type]
         #'(lambda (just)
             (declare (ignore just))
             (push ?attack-type answers)))
    answers))

(defun resource-for-component (component)
  (let ((answers nil))
    (ask `[uses-resource ,component ?resource]
         #'(lambda (just)
             (declare (ignore just))
             (push ?resource answers)))
    answers))

(defun attacks-against-resource (resource)
  (let ((answers nil))
    (ask `[resource-might-have-been-attacked ,resource ?attack]
         #'(lambda (just)
             (declare (ignore just))
             (push ?attack answers)))
    answers))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-name (name-1 name-2 &optional (delimiter "-"))
  (intern (concatenate 'string (string name-1) delimiter (string name-2))))

(defmethod io-named ((parent compound-component) name direction component-name)
  (let ((component (component-named parent component-name)))
    (when component
      (ask `[,direction ,name ,component ?object]
	   #'(lambda (stuff)
	       (declare (ignore stuff))
	       (return-from io-named (values ?object)))))))

(defmethod situation-named ((parent compound-component) before-or-after component-name)
  (let ((component (component-named parent component-name)))
    (when component
      (ask `[situation ,component ,before-or-after ?object]
	   #'(lambda (stuff)
	       (declare (ignore stuff))
	       (return-from situation-named (values ?object)))))))

(defmethod interval-named ((parent compound-component) before-or-after component-name)
  (let ((component (component-named parent component-name)))
    (when component
      (ask `[interval ,component ,before-or-after ?object]
	   #'(lambda (stuff)
	       (declare (ignore stuff))
	       (return-from interval-named (values ?object)))))))

(defmethod resource-named ((parent compound-component) name)
  (ask `[resource ,parent ,name ?resource]
       #'(lambda (stuff)
	   (declare (ignore stuff))
	   (return-from resource-named (values ?resource)))))


(defrule induce-attack (:forward)
  If [and [resource ?component ?resource-name ?resource]
          [has-vulnerability ?resource ?vulnerability]
          [vulnerability-enables-attack ?vulnerability ?attack-type]
          [attack ?component ?name ?attack-type]]
  Then [resource-might-have-been-attacked ?resource ?attack-type])
