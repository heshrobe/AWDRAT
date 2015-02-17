;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat ; readtable: joshua -*-

(in-package :awdrat)

(defrule dscs-consistency (:forward)
  if [and [dscs ?object ?type good ?situation]
	  [dscs ?object ?type bad ?situation]]
  then [Ltms:contradiction])

(define-ensemble maf-editor-create-model
    :inputs ()
    :outputs (the-model))

(define-ensemble maf-editor-add-legs-to-model
    :inputs (the-legs the-model) 
    :outputs (the-model))

(define-ensemble maf-editor-save-model
    :inputs (the-model) 
    :outputs (the-model the-output))

(define-ensemble maf-editor-null
    :inputs (the-object)
    :outputs (the-object))

(define-ensemble maf-editor
    :top-level t
    :inputs ()
    :outputs (the-model)
    :splits ((split1 maf-editor-split1 (a) (branch1 branch2)))
    :joins ((join1 (a) (branch1 branch2)))
    :components ((create-model :models (normal compromised) :type maf-editor-create-model)
		 (side-a :models (normal) :type maf-editor-null)
		 (side-b :models (normal) :type maf-editor-null)
		 (create-legs :models (normal compromised) :type maf-editor-create-legs)
		 (add-legs-to-model :models (normal compromised) :type maf-editor-add-legs-to-model)
		 (save-model :models (normal compromised) :type maf-editor-save-model))
    :dataflows ((the-model create-model a  split1)
		(the-model create-model the-object side-a)
		(the-model create-model the-object side-b)
		(the-object side-a a join1-branch1)
		(the-object side-b a join1-branch2) 
		(a join1 the-model create-legs)
		(the-legs create-legs the-legs add-legs-to-model)
		(the-model create-legs the-model add-legs-to-model)
		(the-model add-legs-to-model the-model save-model)
		(the-model save-model the-model maf-editor))
    :controlflows ((before maf-editor before create-model)
		   (after split1-branch1 before side-a)
		   (after side-a before join1-branch1)
		   (after split1-branch2 before side-b)
		   (after side-b before join1-branch2))
    ;; The resources used, their modes, and their a priori likelihood of being in each mode
    :resources ((imagery image-file (normal .7) (hacked .3)) 
		(code-in-core code-memory-image (normal .9) (hacked .1))
		(code-files loadable-files (normal .8) (hacked .2))
		(host-1 networked-host (normal .99) (slowed-down .01)))
    ;; this maps which resources are used by which components of the computation
    :resource-mappings ((create-model imagery)
			(create-legs code-files)
			(add-legs-to-model code-files)
			(save-model code-files))
    ;; this maps the conditional probabilities between the compromises and the misbehaviors
    :model-mappings ((create-model normal imagery normal .99)
		     (create-model compromised imagery normal .01)
		     (create-model normal imagery hacked .9)
		     (create-model compromised imagery hacked .1)
		     
		     (create-legs normal code-files normal .99)
		     (create-legs compromised code-files normal .01)
		     (create-legs normal code-files hacked .9)
		     (create-legs compromised code-files hacked .1)
		     
		     (add-legs-to-model normal code-files normal .99)
		     (add-legs-to-model compromised code-files normal .01)
		     (add-legs-to-model normal code-files hacked .9)
		     (add-legs-to-model compromised code-files hacked .1)
		     
		     (save-model normal code-files normal .99)
		     (save-model compromised code-files normal .001)
		     (save-model normal code-files hacked .01)
		     (save-model compromised code-files hacked .999))
    
    :vulnerabilities ((imagery reads-complex-imagery)
		      (code-in-core reads-complex-imagery)
		      (code-files loads-code)
		      (host-1 performance-depends-on-network)
		      )
    )

;;; behavior models

(defbehavior-model (maf-editor-create-model normal)
     :inputs ()
     :outputs (the-model)
     :invariants ([not [data-written maf-file]])
     :prerequisites ()
     :post-conditions 
     ([dscs ?the-model mission-object good] 
      [executed-in-protected-memory ?component]))

(defbehavior-model (maf-editor-create-model compromised)
     :inputs ()
     :outputs (the-model)
     :prerequisites ()
     :post-conditions 
     ([dscs ?the-model mission-object bad]
      [not [executed-in-protected-memory ?component]]))

(defbehavior-model (maf-editor-create-legs normal)
     :inputs (the-model)
     :outputs (the-model the-legs)
     :prerequisites ([dscs ?the-model mission-object ?value])
     :post-conditions 
     ([dscs ?the-model mission-object ?value] 
      [dscs ?the-legs set-of-mission-legs good]
      [executed-in-protected-memory ?component]))

(defbehavior-model (maf-editor-create-legs compromised)
     :inputs (the-model)
     :outputs (the-model the-legs)
     :prerequisites ()
     :post-conditions 
     ([dscs ?the-model mission-object bad]
      [dscs ?the-legs set-of-mission-legs bad]
      [not [executed-in-protected-memory ?component]]))

(defbehavior-model (maf-editor-add-legs-to-model normal)
     :inputs (the-model the-legs)
     :outputs (the-model)
     :prerequisites ([dscs ?the-model mission-object ?model-value]
		     [dscs ?the-legs set-of-mission-legs ?legs-value])
     :post-conditions 
     ([dscs ?the-model mission-object ?model-value] 
      [executed-in-protected-memory ?component]))

(defbehavior-model (maf-editor-add-legs-to-model compromised)
     :inputs (the-model the-legs)
     :outputs (the-model)
     :prerequisites ()
     :post-conditions 
     ([dscs ?the-model mission-object bad]
      [not [executed-in-protected-memory ?component]]))

(defbehavior-model (maf-editor-save-model normal)
     :inputs (the-model)
     :outputs (the-output the-model)
     :prerequisites ([dscs ?the-model mission-object ?value])
     :post-conditions 
     ([dscs ?the-output mission-object-xml ?value]
      [dscs ?the-model mission-object ?value]
      [executed-in-protected-memory ?component]))

(defbehavior-model (maf-editor-save-model compromised)
     :inputs (the-model)
     :outputs (the-output)
     :prerequisites ()
     :post-conditions 
     ([dscs ?the-output mission-object bad]
      [dscs ?the-model mission-object bad]
      [not [executed-in-protected-memory ?component]]))

(defbehavior-model (maf-editor-null normal)
    :inputs (the-object)
    :outputs (the-object)
    :prerequisites ()
    :post-conditions ([dscs ?the-object mission-object good]))

(defsplit (maf-editor-split1) (a)
  (branch1 [dscs ?a mission-object good])
  (branch2 [dscs ?a mission-object bad]))


;;; attack models
(define-attack-model hacked-image-file-attack
    :attack-types ((hacked-image-file-attack .3) (hacked-code-file-attack .5))
    :vulnerability-mapping ((reads-complex-imagery hacked-image-file-attack)
			    (loads-code hacked-code-file-attack)))

(define-attack-model packet-flood
  :attack-types ((packet-flood .5))
  :vulnerability-mapping ((performance-depends-on-network packet-flood)))

;;; rules mapping conditional probabilities of vulnerability and attacks

(defrule bad-image-file-takeover (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource image-file]
	  [resource-might-have-been-attacked ?resource hacked-image-file-attack]]
  then [and [attack-implies-compromised-mode hacked-image-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-image-file-attack ?resource normal .1 ]])

(defrule bad-image-file-takeover-2 (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource code-memory-image]
	  [resource-might-have-been-attacked ?resource hacked-image-file-attack]]
  then [and [attack-implies-compromised-mode hacked-image-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-image-file-attack ?resource normal .1 ]])

(defrule hacked-code-file-takeover (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource loadable-files]
	  [resource-might-have-been-attacked ?resource hacked-code-file-attack]]
  then [and [attack-implies-compromised-mode hacked-code-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-code-file-attack ?resource normal .1 ]])

(defrule hacked-code-file-takeover-2 (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource loadable-files]
	  [resource-might-have-been-attacked ?resource hacked-code-file-attack]]
  then [and [attack-implies-compromised-mode hacked-code-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-code-file-attack ?resource normal .1 ]])


(defrule flood-slowdown (:forward)
  If [and [resource ?ensemble ?resource-name ?resource]
          [resource-type-of ?resource networked-host]
          [resource-might-have-been-attacked ?resource packet-flood]]
  then [and [attack-implies-compromised-mode packet-flood ?resource slowed-down .7 ]
            [attack-implies-compromised-mode packet-flood ?resource normal .3 ]])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;      Hacked Code file attacks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defrule bad-code-file-takeover (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource code-file]
	  [resource-might-have-been-attacked ?resource hacked-code-file-attack]]
  then [and [attack-implies-compromised-mode hacked-code-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-code-file-attack ?resource normal .1 ]])

(defrule bad-code-file-takeover-2 (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource code-memory-image]
	  [resource-might-have-been-attacked ?resource hacked-code-file-attack]]
  then [and [attack-implies-compromised-mode hacked-code-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-code-file-attack ?resource normal .1 ]])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Detritus
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; (eval-when (:compile-toplevel :execute :load-top-level)
;   (define-predicate mobility-plan-exists (plan))
;   (define-predicate input-file-exists (application plan recency)))

; (define-service (maf-caf [mobility-plan-exists ?plan])
;     (data-currency fresh recent stale)
;   (communication protected unprotected)
;   )

; (define-method normal-maf-caf
;  :service maf-caf
;  :features ((data-currency fresh) (communication unprotected))
;  :resources (?database ?machine ?screen-server ?pipe)
;  :other-parameters (maf-caf-site)
;  :prerequisite ([object-type-of ?database database]
; 				[object-type-of ?screen-server computer]
; 				[object-type-of ?machine computer])
;  :context ([value-of (?database machines) ?machine]
; 	   [value-of (?machine site) ?site]
;            (eql (role-name ?site) 'maf-caf-site)
; 	   )
;  :resource-constraints ([screen-connection ?pipe ?machine ?screen-server ?controls]))

; ;;; Should have a bitway between input file and machine running database
; ;;; security of that controls communication privacy

; (define-method replay-maf-caf
;  :service maf-caf
;  :features ((data-currency ?recency) (communication unprotected))
;  :resources (?database ?input-file ?machine)
;  :other-parameters (?site)
;  :prerequisite ([object-type-of ?database database])
;  :context ([value-of (?database machines) ?machine]
; 	   [value-of (?machine site) ?site])
;  :resource-constraints 
;  ([input-file-exists maf-caf ?input-file ?recency]))

; (defun test1 ()
;   (let ((utility-function
; 	  (utility-function-for-service 
; 	    'maf-caf
; 	    '((data-currency fresh (>> 1.1) data-currency recent)
; 	      (data-currency recent (>> 2) data-currency stale)
; 	      (communication protected (>> 3) communication unprotected)
; 	      ))))
;     (find-em 'maf-caf utility-function)))


; (define-ensemble demval
;     :components  ((aodb :models (normal compromised) :inputs () :outputs (as loc))
; 		  (pub-as :models (normal compromised) :inputs (in) :outputs (out))
; 		  (pub-loc :models (normal compromised) :inputs (in) :outputs (out))
; 		  (maf :models (normal compromised) :inputs (as loc) :outputs (proposed-mi))
; 		  (pub-proposed-mi :models (normal compromised) :inputs (in) :outputs (out))
; 		  (caf :models (normal compromised) :inputs (proposed-mi as loc) :outputs (approved-mi))
; 		  (pub-approved-mi :models (normal compromised) :inputs (in) :outputs (out)))
;     :dataflows ((as aodb in pub-as)
; 		(loc aodb in pub-loc)
; 		(out pub-as as maf)
; 		(out pub-as as caf)
; 		(out pub-loc loc maf)
; 		(out pub-loc loc caf)
; 		(proposed-mi maf in pub-proposed-mi)
; 		(out pub-proposed-mi proposed-mi caf)
; 		(approved-mi caf in pub-approved-mi))
;     :resources ((box-1 (normal .9) (hacked .1)) (box-2 (normal .9) (hacked .1)))
;     :model-mappings ()
;     )

; (defbehavior-model (aodb normal)
;      :inputs ()
;      :outputs (as loc)
;      :prerequisites ()
;      :post-conditions ([well-formed ?AS AS] 
; 		       [well-formed ?loc loc] 
; 		       [executed-in-protected-memory ?component]))




(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; A bitway is any path that can connect two things, the controls field says
  ;; how to configure it.
  (define-predicate screen-connection (pipe screen-server application-server controls))
  ;; This describes how mux-like things connect other things
  (define-predicate switched-by (switch thing direction port))
  (define-predicate cost-of-failure (method cost))
  (define-predicate state-of (device state probability)))

(define-object-type mux
    )

(define-object-type network-path
    :slots ((path) (source) (destination)))

(defrule path-working (:backward)
  then [state-of ?network-path working ?]
  if [and [object-type-of ?network-path network-path]
          [value-of (?network-path path) ?components]
	  (let ((components ?components))
	    ;; needed to fix something about the way loop 
	    ;; works as of allegro 9.0
	    (loop for thing in components
	        always (is-working thing)))
	  ]
  )
      


;;; Calling this bitway seems wrong
;;; we're looking for a screen-way

;;;(defrule null-screen-connection (:backward)
;;;  then [screen-connection direct-connection ?x ?x nil]
;;;  if t)
;;;
;;;(defrule screen-connection-by-video-mux (:backward)
;;;  then [screen-connection ?mux ?x ?y (connnect ?port-in ?port-out)]
;;;  if [and [object-type-of ?mux mux]
;;;          [switched-by ?mux ?x input ?port-in]
;;;          [switched-by ?mux ?y output ?port-out]])
;;;
;;;(defun make-pathway-between-parts (p1 p2 path)
;;;  (let* ((name (gentemp "CONNECTOR-"))
;;;	 (object (make-object 'network-path :name name)))
;;;    (tell `[value-of (,object path) ,path])
;;;    (tell `[value-of (,object source) ,p1])
;;;    (tell `[value-of (,object destination) ,p2])
;;;    object))
;;;
;;;(defrule screen-connection-by-network (:backward)
;;;  then [screen-connection ?connector ?screen-server ?compute-server remote-screen]
;;;  if [and [object-type-of ?screen-server computer]
;;;          [object-type-of ?compute-server computer]
;;;	  [connected ?screen-server ?compute-server ?network-pathway]
;;;	  [value-of (?screen-server ip-addresses) ?address]
;;;	  (path-is-acceptable-for-connection-type
;;;	   (copy-object-if-necessary ?network-pathway)
;;;	   ?address
;;;	   'remote-screen)
;;;	  (unify ?connector (make-pathway-between-parts ?screen-server ?compute-server ?network-pathway))
;;;	  ])