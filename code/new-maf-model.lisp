;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat; readtable: joshua -*-

(in-package :awdrat)

(define-ensemble maf-editor
    :entry-events :auto
    :inputs ()
    :outputs (the-model)
    :components ((startup :type maf-startup :models (normal compromised))
		 (create-model :type maf-create-model :models (normal compromised))
		 (create-events :type maf-create-events :models (normal compromised))
		 (save :type maf-save :models (normal compromised)))
    :controlflows ((before maf-editor before startup)
		   (after startup before create-model))
    :dataflows ((the-model create-model the-model create-events)
		(the-model create-events the-model save)
		(the-model save the-model maf-save-model))
    ;; The resources used, their modes, and their a priori likelihood of being in each mode
    :resources ((imagery image-file (normal .7) (hacked .3)) 
		(code-files loadable-files (normal .8) (hacked .2)))
    ;; this maps which resources are used by which components of the computation
    :resource-mappings ((startup imagery)
			(create-model code-files)
			(create-events code-files)
			(save-model code-files))
    ;; this maps the conditional probabilities between the compromises and the misbehaviors
    :model-mappings ((startup normal ((imagery normal)) .99)
		     (startup compromised ((imagery normal)) .01)
		     (startup normal ((imagery hacked)) .9)
		     (startup compromised ((imagery hacked)) .1)
		     
		     (create-model normal ((code-files normal)) .99)
		     (create-model compromised ((code-files normal)) .01)
		     (create-model normal ((code-files hacked)) .9)
		     (create-model compromised ((code-files hacked)) .1)
		     
		     (create-events normal ((code-files normal)) .99)
		     (create-events compromised ((code-files normal)) .01)
		     (create-events  normal ((code-files hacked)) .9)
		     (create-events compromised ((code-files hacked)) .1)
		     
		     (save normal ((code-files normal)) .99)
		     (save compromised ((code-files normal)) .001)
		     (save normal ((code-files hacked)) .01)
		     (save compromised ((code-files hacked)) .999))
    
    :vulnerabilities ((imagery reads-complex-imagery)
		      (code-files loads-code)
		      ))
		 
(define-ensemble maf-startup
    :entry-events (startup)
    :exit-events (startup)
    :allowable-events (post-validate create-client-frame 
				     center-action load-image)
    :inputs ()
    :outputs ())

;;; Need to pick predicates for distinguishing these
;;; The compromise possible in startup is an image file
;;; attack leading to out of code execution?
(defbehavior-model (maf-startup normal)
    :inputs ()
    :outputs ()
    :prerequisites ()
    :post-conditions ())

(defbehavior-model (maf-startup compromised)
    :inputs ()
    :outputs ()
    :prerequisites ()
    :post-conditions ())

;;; Need defbehaviors for each of these even if its empty

(define-ensemble maf-create-model
    :entry-events (create-mission-action-action-performed)
    :exit-events (mission-builder-submit)
    :allowable-events (create-mission-builder-with-client-panel
		       create-mission-builder
		       create-mission-builder-with-hash-table
		       mission-builder-submit
		       (set-initial-info exit (the-model nil))
		       create-mission-action-action-performed
		       retrieve-info
		       create-mission-action-action-performed
		       (set-initial-info entry)
		       )
    :inputs ()
    :outputs (the-model))

(defbehavior-model (maf-create-model normal)
    :inputs ()
    :outputs (the-model)
    :prerequisites ()
    :post-conditions ([dscs ?the-model mission-builder good])
    )

(defbehavior-model (maf-create-model compromised)
    :inputs ()
    :outputs (the-model)
    :prerequisites ()
    :post-conditions ([not [dscs ?the-model mission-builder good]])
    )

(define-ensemble maf-create-events
    :entry-events :auto 
    :exit-events ()
    :allowable-events ()
    :inputs (the-model)
    :outputs (the-model)
    :components ((get-next-cmd :type maf-get-next-cmd :models (normal))
		 (get-event-info :type maf-get-event-info :models (normal compromised))
		 (add-event-to-model :type maf-add-event-to-model :models (normal compromised))
		 (get-leg :type maf-get-leg :models (normal compromised))
		 (get-movement :type maf-get-movement :models (normal compromised))
		 (get-sortie :type maf-get-sortie :models (normal compromised))
		 (add-additional-info-to-model :type maf-add-additional-info :models (normal compromised))
		 (continue :type maf-create-events :models (normal compromised)))
    :dataflows ((the-model maf-create-events the-model join-exit-exit)
		(the-model maf-create-events the-model add-event-to-model)
		(the-cmd get-next-cmd cmd more-events?)
		(the-event get-event-info the-event add-event-to-model)
		(the-model add-event-to-model the-model join-events-non-take-off)
		(the-event get-event-info event takeoff?)
		(the-leg get-leg the-leg add-additional-info-to-model)
		(lms-event-counter get-leg event-number add-additional-info-to-model)
		(the-movement get-movement the-movement add-additional-info-to-model)
		(the-sortie get-sortie the-sortie add-additional-info-to-model)
		(the-model add-event-to-model the-model add-additional-info-to-model)
		(the-model add-additional-info-to-model the-model join-events-take-off)
		(the-model join-events the-model continue)
		(the-model continue the-model join-exit-recur)
		(the-model join-exit the-model maf-create-events)
		)
    :controlflows ((after more-events?-build-event before add-event-to-model)
		   (after more-events?-exit before join-exit-exit)
		   (after takeoff?-get-additional-info before get-leg)
		   (after takeoff?-get-additional-info before get-movement)
		   (after takeoff?-get-additional-info before get-sortie)
		   (after takeoff?-exit before join-events-non-take-off))
    :splits ((more-events? maf-more-events? (cmd) (build-event exit))
	     (takeoff? maf-takeoff? (event) (get-additional-info exit)))
    :joins ((join-events (the-model) (take-off non-take-off))
	    (join-exit (the-model) (recur exit)))
        ;; The resources used, their modes, and their a priori likelihood of being in each mode
    :resources ((code-files loadable-files (normal .8) (hacked .2)))
    ;; this maps which resources are used by which components of the computation
    :resource-mappings ((get-event-info  code-files)
			(add-event-to-model code-files)
			(get-leg code-files)
			(get-movement code-files)
			(get-sortie code-files)
			(add-additional-info-to-model code-files)
			(continue code-files))
    ;; this maps the conditional probabilities between the compromises and the misbehaviors
    :model-mappings ((get-event-info normal code-files normal .99)
		     (get-event-info compromised code-files normal .01)
		     (get-event-info normal code-files hacked .9)
		     (get-event-info compromised code-files hacked .1)
		     
		     (add-event-to-model normal code-files normal .99)
		     (add-event-to-model compromised code-files normal .01)
		     (add-event-to-model  normal code-files hacked .9)
		     (add-event-to-model compromised code-files hacked .1)
		     
		     (get-leg normal code-files normal .99)
		     (get-leg compromised code-files normal .001)
		     (get-leg normal code-files hacked .01)
		     (get-leg compromised code-files hacked .999)
		     
		     (get-movement normal code-files normal .99)
		     (get-movement compromised code-files normal .001)
		     (get-movement normal code-files hacked .01)
		     (get-movement compromised code-files hacked .999)
		     
		     (get-sortie normal code-files normal .99)
		     (get-sortie compromised code-files normal .001)
		     (get-sortie normal code-files hacked .01)
		     (get-sortie compromised code-files hacked .999)
		     
		     (add-additional-info-to-model normal code-files normal .99)
		     (add-additional-info-to-model compromised code-files normal .001)
		     (add-additional-info-to-model normal code-files hacked .01)
		     (add-additional-info-to-model compromised code-files hacked .999)
		     
		     (continue normal code-files normal .99)
		     (continue compromised code-files normal .001)
		     (continue normal code-files hacked .01)
		     (continue compromised code-files hacked .999))
    :vulnerabilities ((code-files loads-code))
    )

(defbehavior-model (maf-create-events normal)
    :inputs (the-model)
    :outputs (the-model)
    :prerequisites ([dscs ?the-model mission-builder good])
    :post-conditions ([dscs ?the-model mission-builder good])
    )

(defbehavior-model (maf-create-events compromised)
    :inputs (the-model)
    :outputs (the-model)
    :prerequisites ([dscs ?the-model mission-builder good])
    :post-conditions ([not [dscs ?the-model mission-builder good]])
    )

(define-ensemble maf-get-next-cmd
    :entry-events (next-cmd)
    :exit-events ((next-cmd exit (the-cmd)))
    :inputs ()
    :outputs (the-cmd))

(defbehavior-model (maf-get-next-cmd normal)
    :inputs ()
    :outputs (the-cmd)
    :prerequisites ()
    :post-conditions ())

(define-ensemble maf-get-event-info
    :entry-events (create-mission-event-point)
    :allowable-events (set-current-point 
		       (create-mission-event-point exit)
		       create-mission-event-object
		       meo-set-information 
		       mpl-action-performed
		       close-form 
		       add-new-event-internal)
    :exit-events ((got-event-info exit (the-event)))
    :inputs ()
    :outputs (the-event))

(defbehavior-model (maf-get-event-info normal)
    :inputs ()
    :outputs (the-event)
    :prerequisites ()
    :post-conditions ([dscs ?the-event event good]))

(defbehavior-model (maf-get-event-info compromised)
    :inputs ()
    :outputs (the-event)
    :prerequisites ()
    :post-conditions ([not [dscs ?the-event event good]]))

(define-ensemble maf-add-event-to-model
    :entry-events (update-msn-evt)
    :allowable-events 
    ((update-msn-evt exit (mb event-number event))
     add-new-event-internal
     create-new-additional-mission-info-panel
     )
    :exit-events (mpl-action-performed)
    :inputs (the-event the-model)
    :outputs (the-model event-number))

(defbehavior-model (maf-add-event-to-model normal)
    :inputs (the-event the-model)
    :outputs (the-model event-number)
    :prerequisites ([dscs ?the-event event good]
		    [dscs ?the-model mission-builder good])
    :post-conditions 
    ([add-to-map (events ?the-model)?event-number ?the-event
		 ?before-maf-add-event-to-model]
     [dscs ?the-model mission-builder good]))

(defbehavior-model (maf-add-event-to-model compromised)
    :inputs (the-event the-model)
    :outputs (the-model event-number)
    :prerequisites ([not [dscs ?the-event event good]]
		    [not [dscs ?the-model mission-builder good]])
    :post-conditions 
    ([dscs ?the-model mission-builder good]))

(define-ensemble maf-get-leg
    :entry-events (retrieve-leg)
    :exit-events ((retrieve-leg exit (nil the-leg lms-event-counter)))
    :allowable-events (create-mission-leg-object mlo-set-information)
    :inputs ()
    :outputs (the-leg lms-event-counter))

(defbehavior-model (maf-get-leg normal)
    :inputs ()
    :outputs (the-leg lms-event-counter)
    :prerequisites ()
    :post-conditions ([dscs ?the-leg leg good]))

(defbehavior-model (maf-get-leg compromised)
    :inputs ()
    :outputs (the-leg lms-event-counter)
    :prerequisites ()
    :post-conditions ([not [dscs ?the-leg leg good]]))

(define-ensemble maf-get-movement
    :entry-events (retrieve-movement)
    :exit-events ((retrieve-movement exit (nil the-movement)))
    :allowable-events 
    (create-mission-movement-object mmo-set-information)
    :inputs ()
    :outputs (the-movement))

(defbehavior-model (maf-get-movement normal)
    :inputs ()
    :outputs (the-movement)
    :prerequisites ()
    :post-conditions ([dscs ?the-movement movement good]))

(defbehavior-model (maf-get-movement compromised)
    :inputs ()
    :outputs (the-movement)
    :prerequisites ()
    :post-conditions ([not [dscs ?the-movement movement good]]))

(define-ensemble maf-get-sortie
    :entry-events (retrieve-sortie)
    :exit-events ((retrieve-sortie exit (nil the-sortie)))
    :allowable-events 
    (create-mission-sortie-object mso-set-information)
    :inputs ()
    :outputs (the-sortie))

(defbehavior-model (maf-get-sortie normal)
    :inputs ()
    :outputs (the-sortie)
    :prerequisites ()
    :post-conditions ([dscs ?the-sortie sortie good]))

(defbehavior-model (maf-get-sortie compromised)
    :inputs ()
    :outputs (the-sortie)
    :prerequisites ()
    :post-conditions ([not [dscs ?the-sortie sortie good]]))

(define-ensemble maf-add-additional-info
    :entry-events ((retrieve-sortie exit))
    :exit-events (Mission-builder-add-info)
    :inputs (the-model the-leg the-movement the-sortie event-number)
    :outputs (the-model))

(defbehavior-model (maf-add-additional-info normal)
    :inputs (the-model the-leg the-movement the-sortie event-number)
    :outputs (the-model)
    :prerequisites  ([dscs ?the-leg leg good]
		     [dscs ?the-movement movement good]
		     [dscs ?the-sortie sortie good]
		     [dscs ?the-model mission-builder good])
    :post-conditions ([add-to-map (legs ?the-model) ?event-number ?the-leg
				  ?before-maf-add-additional-info]
		      [add-to-map (sorties ?the-model) ?event-number ?the-sortie
				  ?before-maf-add-additional-info]
		      [add-to-map (movements ?the-model) ?event-number ?the-movement
				  ?before-maf-add-additional-info]
		      [dscs ?the-model mission-builder good]))

(defbehavior-model (maf-add-additional-info compromised)
    :inputs (the-model the-leg the-movement the-sortie event-number)
    :outputs (the-model)
    :prerequisites  ([dscs ?the-leg leg good]
		     [dscs ?the-movement movement good]
		     [dscs ?the-sortie sortie good]
		     [dscs ?the-model mission-builder good])
    :post-conditions ([not [dscs ?the-model mission-builder good]]))

(defsplit maf-more-events? (cmd)
  (build-event (equal ?cmd 'new-event))
  (exit (equal ?cmd 'save-mission)))

(defsplit maf-takeoff? (event)
  (get-additional-info (take-off-event? ?event))
  (exit (not (take-off-event? ?event))))

(define-ensemble maf-save
    :inputs (the-model)
    :outputs ())

(defbehavior-model (maf-save normal)
    :inputs (the-model)
    :outputs ()
    :prerequisites ([dscs ?the-model mission-builder good])
    :post-conditions ([dscs ?the-model mission-builder good]))

(defbehavior-model (maf-save compromised)
    :inputs (the-model)
    :outputs ()
    :prerequisites ([dscs ?the-model mission-builder good])
    :post-conditions ([not [dscs ?the-model mission-builder good]]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; attack models
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-attack-model maf-attacks
    :attack-types ((hacked-image-file-attack .3) (hacked-code-file-attack .5))
    :vulnerability-mapping ((reads-complex-imagery hacked-image-file-attack)
			    (loads-code hacked-code-file-attack)))

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

