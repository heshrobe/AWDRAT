;;; -*- Mode: common-lisp; Syntax: joshua; Package: awdrat; readtable: joshua -*-

;;; A Node space is a mapping of feature sets onto numerically ordered
;;; nodes The original version of this used binary features exclusively,
;;; this is a redesign for features that take on 1 of n values (e.g.
;;; speed in {fast medium slow}).  Each feature is assigned a byte of
;;; enough bits to cover the number of possible values and then the
;;; values are assigned values from 0 to n - 1 within that space.  The total
;;; feature vector is then the concatenation of these individual bytes.
;;;
;;; The node space has these components:
;;; The alist of features and their possible values
;;;
;;; The forward-map: A hash-table mapping feature-name to a byte-specifier
;;; for that feature and the list of values in order
;;; 
;;; An inverse-map for mapping the numerical encoding to feature and value 
;;; the inverse-map is an set of triples
;;; byte-specifier feature-name feature-values
;;;
;;; A vector of nodes, each corresponding to an element of the powerset
;;; of individual feature assignments.

;;; For example: if size is the second feature in bits 2 - 3
;;; encoding values large, medium small
;;; then large =  0000  ->  0
;;;      medium = 0100  ->  8
;;;      small  = 1000  -> 16

;;; programming notes:
;;; (ldb (byte size position) number)
;;; (dpb newbyte (byte size position) number)
;;; are the common lisp ways of accesses bit-fields
;;; size and position are in bits

(in-package :awdrat)

(defun needed-bits (feature-list)
  (ceiling (log (length feature-list) 2)))


(defclass netnode ()
  ((number :accessor node-number :initarg :number :initform nil)
   (outgoing-links :accessor outgoing-links :initform nil)
   (incoming-links :accessor incoming-links :initform nil)
   (value :accessor node-value :initform nil)
   (node-space :accessor node-space :initform nil :initarg :node-space)
  ))

(defclass netlink ()
    ((incoming-node :accessor incoming-node :initarg :incoming-node :initform nil)
     (outgoing-node :accessor outgoing-node :initarg :outgoing-node :initform nil)
     (weight :accessor weight :initarg :weight :initform 1)))

(defmethod initialize-instance :after ((link netlink) &rest ignore)
  (declare (ignore ignore))
  (with-slots (incoming-node outgoing-node) link
    ;; (format t "~%link ~a incoming ~a outgoing ~a" link incoming-node outgoing-node)
    (when incoming-node
      (pushnew link (outgoing-links incoming-node)))
    (when outgoing-node
      (pushnew link (incoming-links outgoing-node))))
  link)
      
(defclass node-space ()
  ((forward-map :accessor forward-map :initarg :forward-map)
   (inverse-map :accessor inverse-map :initarg :inverse-map)
   (node-vector :accessor node-vector :initarg :node-vector)
   (ordered-vector :accessor ordered-vector :initarg :ordered-vector)
   (features :accessor features :initarg :features)
   (scale-factor :accessor scale-factor :initform 1)
   (maximum-value :accessor maximum-value :initform 0)
   (intended-maximum-value :accessor intended-maximum-value :initform 0)))

;;; here the feature set is a set of (feature . values)
(defmethod make-node-space (feature-set)
  (let ((forward-map (make-hash-table))
	(byte-position 0)
        (inverse-map nil))
    (loop for (feature-name . feature-values) in feature-set
	  for number-of-bits = (needed-bits feature-values)
	  for byte-specifier = (byte number-of-bits byte-position)
	  do (push (list* byte-specifier feature-name feature-values)
		   inverse-map)
	     (setf (gethash feature-name forward-map)
		   (list* byte-specifier feature-values))
	     (incf byte-position number-of-bits))
    (let* ((network-size (ash 1 byte-position))
	   (node-vector (make-array network-size))
	   (node-space (make-instance 'node-space 
			 :features feature-set
			 :forward-map forward-map
			 :inverse-map inverse-map
			 :node-vector node-vector)))
        (loop for i below network-size
	    for entry = (make-instance 'netnode 
			  :number i 
			  :node-space node-space)
	    do (setf (aref node-vector i) entry))
	node-space
	)))

;;; reminder:
;;; the inverse-map is an set of triples
;;; byte-specifier feature-name feature-values

(defmethod decode-node ((node netnode))
  (let* ((ns (node-space node))
	 (inverse-map (inverse-map ns))
	 (number (node-number node)))
    (loop for (byte-specifier feature-name . feature-values) in inverse-map
	  for feature-number  = (ldb byte-specifier number)
	  for value = (nth feature-number feature-values)
	if value
	collect (list feature-name value)
	else return nil)))

(defmethod decode-node-space ((ns node-space))
  (loop for n across (node-vector ns)
      for i from 0
      for decode = (decode-node n)
      if decode
      do (format t "~%node ~d ~{~a~^,~}" i decode)
      else do (format t "~%node ~d not used" i)))

;;; given a set of feature-name feature-value pairs find the designated
;;; node

(defmethod find-feature-set-node (feature-set (ns node-space))
  (with-slots (node-vector) ns
    (loop with key = 0
          for (feature-name feature-value) in feature-set
	  do (multiple-value-bind (byte-specifier feature-value-numer)
		 (map-feature-name-and-value feature-name feature-value ns)
	       (setq key (dpb feature-value-numer
			      byte-specifier
			      key)))
	  finally (return (aref node-vector key)))))

(defmethod map-feature-name-and-value (feature-name feature-value (ns node-space))
  (declare (values byte-specifier value-number))
  (with-slots (forward-map) ns
    (let ((feature-entry (or (gethash feature-name forward-map)
			     (error "invalid feature-name ~a" feature-name))))
      (destructuring-bind (byte-specifier . feature-values) feature-entry
	(let ((value-number (or (position feature-value feature-values)
				(error "invalid value ~a for feature ~a"
				       feature-value feature-name))))
	  (values byte-specifier value-number))))))



;;; find all nodes matching a description
;;; and apply a function to each
;;; a description is a list of literals
;;; each literal is a list of feature-name and a specific-feature-value
;;; 
;;; variable features are the feature-names for which we don't care
;;; what value they take on, we find
;;; all nodes with any value for this feature-name

(defmethod find-feature-set-nodes (feature-set variable-features (ns node-space) continuation)
  (with-slots (forward-map node-vector) ns
    (let ((fixed-key 0))
      (loop for (feature-name feature-value) in feature-set
            do (multiple-value-bind (byte-specifier feature-value-number)
		   (map-feature-name-and-value feature-name feature-value ns)
		 (setq fixed-key (dpb feature-value-number
				      byte-specifier
				      fixed-key))))
      (labels
	((do-one-more-dont-care (remaining-features key-so-far accumulated-dont-cares)
	   (cond
	     ((null remaining-features)
	      (funcall continuation (aref node-vector key-so-far) accumulated-dont-cares))
	     (t (destructuring-bind (next-feature-name . remaining-features) remaining-features
		  (let ((feature-entry (or (gethash next-feature-name forward-map)
					   (error "invalid feature-name ~a" 
						  next-feature-name))))
		    ;; since it can be any of the values we need to map over all of them
		    (destructuring-bind (byte-specifier . feature-values) feature-entry
		      (loop for i from 0
			    for feature-value in feature-values
			    do (do-one-more-dont-care
				 remaining-features
				 (dpb i byte-specifier key-so-far)
				 `((,next-feature-name ,feature-value)
				   ,@accumulated-dont-cares))))))))))
        (do-one-more-dont-care variable-features fixed-key nil)))))

;;; this is used by canonicalize-rule below to combine the negative of the lhs of a rule
;;; with the rhs of the rule and vice-versa.
;;; by negative we mean all possible features other than the one
;;; actually specified 
;;; e.g. if the right hand side say (quality low)
;;; then we need to add to the left hand side 
;;; (quality high) and (quality medium)

;;; so if we have (speed fast) > (quality low)
;;; where speed takes on values fast slow
;;; and quality takes on values high medium low
;;; then what we mean is 
;;; (speed fast) & (quality high) > (speed slow) & (quality low)
;;; (speed fast) & (quality medium) > (speed slow) & (quality low)

(defmethod distribute (and-term and-term-to-negate (ns node-space))
  (with-slots (features) ns
    (let ((answers nil))
      (labels 
	  ((do-all-remaining-dont-cares (dont-care-terms stuff-so-far)
	     (cond ((null dont-care-terms)
		    (pushnew (sort (copy-list stuff-so-far) #'my-order) answers 
			     :test #'equal))
		   (t (destructuring-bind (feature-name feature-value)
			  (pop dont-care-terms)
			(if (assoc feature-name and-term)
			    (do-all-remaining-dont-cares dont-care-terms stuff-so-far)
			  (let ((feature-values (cdr (assoc feature-name features))))
			    (loop for value in feature-values
				unless (eql value feature-value)
				do (let* ((new-term (list feature-name value))
					  (accumulated-stuff (if (member new-term stuff-so-far 
									 :test #'equal)
								 stuff-so-far
							       (cons new-term stuff-so-far))))
				     (do-all-remaining-dont-cares 
					 dont-care-terms accumulated-stuff)))))))))
	   (my-order (a b)
	     (string-lessp (string (first a)) (string (first b)))))
	(do-all-remaining-dont-cares and-term-to-negate and-term))
      answers)))

(defmethod canonicalize-rule (lhs rhs (ns node-space))
  (let ((completed-left (distribute lhs rhs ns))
        (completed-right (distribute rhs lhs ns))
        (answers nil))
    (loop for l in completed-left
	do (loop for r in completed-right
	       do (pushnew (list l r) answers :test #'equal)))
    answers))

(defgeneric process-a-rule (better-features worse-features weight node-space))

(defmethod process-a-rule (better-features worse-features weight (ns node-space))
  (let ((all-features (mapcar #'first (features ns)))
	(dont-cares nil)
	(used-features nil))
    (flet ((do-symbols-in-thing (conjunction)
             (loop for term in conjunction
                   do (pushnew (first term) used-features))))
      (do-symbols-in-thing better-features)
      (do-symbols-in-thing worse-features))
    (setq dont-cares (copy-seq (set-difference all-features used-features)))
     ;; (format t "~%better ~{~a~^,~} worse ~{~a~^,~} dont care ~{~a~^,~}"
     ;;         better-features worse-features dont-cares)
    (flet ((dominate-nodes (better worse)
	     ;; (format t "~%better ~{~a~^,~} worse ~{~a~^,~}" better worse)
             (find-feature-set-nodes
              better dont-cares ns
              #'(lambda (better-node accumulated-dont-cares)
                  (find-feature-set-nodes
                   (append accumulated-dont-cares worse) nil ns
                   #'(lambda (worse-node ignore)
                       (declare (ignore ignore))
		       ;; (format t "~%domination ~{~a~^,~} ~{~a~^,~}"
		       ;;        (decode-node better-node ns) (decode-node worse-node ns))
		       ;; side effect of make instance is to link them up
		       (make-instance 'netlink
			 :incoming-node better-node
			 :outgoing-node worse-node
			 :weight weight)
		       ;; (format t "~%linking ~a to ~% ~a"
		       ;;   (reverse (decode-node better-node))
		       ;;   (reverse (decode-node worse-node)))
		       ))))))
      (let ((pairs (canonicalize-rule better-features worse-features ns)))
        (loop for (better worse) in pairs
	    do (dominate-nodes better worse))))))

(defun process-all-rules (rules feature-set intended-max-value combining-function base-value)
  (let ((node-space (make-node-space feature-set)))
    (loop for (lhs rhs weight) in rules
          do (process-a-rule lhs rhs weight node-space)
	  ;; (format t "~%~{~a~^,~} -> ~{~a~^,~}" lhs rhs)
	     )
    (let ((his-maximum-calculated-value (assign-order node-space intended-max-value combining-function base-value)))
      (values node-space his-maximum-calculated-value))))

;;; I've experimented with both multiplicative and additve interpretation of the preference
;;; weight.  Should generalize so that you can choose.
(defmethod assign-order ((node-space node-space) intended-max-value combining-function base-value)
  (let* ((node-vector (node-vector node-space))
	(maximum-calculated-value nil)
	(ordered-vector (copy-seq node-vector)))
    (setf (ordered-vector node-space) ordered-vector)
    (labels ((do-one-node (node path-so-far)
	       ;; (format t "~%do one node ~a ~a ~a" (decode-node node) path-so-far (node-value node))
	       (when (member node path-so-far)
		 (error "cycle ~{~%~a~^,~}" 
			(loop for bad-node in (cons node path-so-far) 
			      collect (decode-node bad-node))))
               (unless (node-value node)
                 (let* ((outgoing-links (outgoing-links node))
			(best-of-descendants (if (null outgoing-links)
						 ;; if there are no outgoing links the value is 0
						 ;; for additive model or 1 for multiplicative
						 base-value
					       (loop for outgoing-link in (outgoing-links node)
						   for descendant = (outgoing-node outgoing-link)
						   for weight = (weight outgoing-link)
						   do (do-one-node descendant (cons node path-so-far))
						      ;; + for additive model, * for multiplicative
						   maximize (funcall combining-function weight (node-value descendant)))))
                        (my-value  best-of-descendants))
                   ;; (format t "~%setting-value of ~a to ~d" node my-value)
                   (setf (node-value node) my-value)
		   (when (or (null maximum-calculated-value) (> my-value maximum-calculated-value))
		     (setq maximum-calculated-value my-value))
		   ))))
      (loop for node across node-vector do (do-one-node node nil)))
    ;; patch for additive case and no preferences
    (when (zerop maximum-calculated-value)
      (setq maximum-calculated-value 1))
    (setf (maximum-value node-space) maximum-calculated-value
	  (intended-maximum-value node-space) intended-max-value
	  (scale-factor node-space) (/ (float intended-max-value) maximum-calculated-value))
    ;; so best guys are first
    (sort ordered-vector #'> :key #'node-value)
      ))

(defmethod utility (feature-set (node-space node-space))
  (let ((node (find-feature-set-node feature-set node-space)))
    (* (node-value node) (scale-factor node-space))
    ))

(defmethod utility-bounds (bound-features unbound-features (node-space node-space))
  (let ((min nil)
	(max nil))
    (find-feature-set-nodes 
     bound-features unbound-features node-space
     #'(lambda (node &rest ignore)
	 (declare (ignore ignore))
	 (let ((node-value (node-value node)))
	 (when (or (null min) (< node-value min))
	   (setq min node-value))
	 (when (or (null max) (> node-value max))
	   (setq max node-value)))))
    (values (* (scale-factor node-space) min)
	    (* (scale-factor node-space) max))
    ))

(defmethod make-mask-and-key (feature-alist (node-space node-space))
  (let ((fixed-key 0)
	(mask 0))
    ;; build a mask key which is all 1s in the features provided and zero elsewhere
    ;; and a vector which is just the features provided and zero elsewhere
    ;; check that the feature is actually bound to a value.  
    (loop for (feature-name  feature-value) in feature-alist
	unless (unbound-logic-variable-p feature-value)
	do (multiple-value-bind (byte-specifier feature-value-number)
	       (map-feature-name-and-value feature-name feature-value node-space)
	     (setq mask (dpb -1 byte-specifier mask))
	     (setq fixed-key (dpb feature-value-number byte-specifier fixed-key))))
    (values mask fixed-key)))

(defmethod utility-upper-bounds (feature-alist (node-space node-space) &optional cutoff no-good-list)
  ;; cutoff can be nil in which case do full search
  (with-slots (ordered-vector scale-factor) node-space
    (multiple-value-bind (mask fixed-key) (make-mask-and-key feature-alist node-space)
      ;; If my key is a superset of a no-good then I'm a loser.
      ;; Reasoning: If the nogood had no completion that's better than my best
      ;; And I'm a superset of the nogood than any completion of me is a completion of the nogood
      ;; and I've already determined that they're all losers.
      ;; (format t "~%Checking value ~o ~o" mask fixed-key)
      (loop for (no-good-mask no-good-value) in no-good-list
	  ;; do  (format t "~%Checking against ~o ~o" no-good-mask no-good-value)
	     ;; he's good at more features bound than the nogood
	  if (and (= (logand no-good-mask mask) no-good-mask)
		  (= no-good-value (logand no-good-mask fixed-key)))
	  do ;; (format t "~%Cutoff because ~o is subsumer of ~o" fixed-key no-good-value)
	     (return-from utility-upper-bounds (values nil))
	  ;; else do (format t "~%No Cutoff because ~o is not subsumer of ~o" fixed-key no-good-value)
	     )
      (let ((scaled-cutoff (and cutoff (/ cutoff scale-factor))))
	;; now search from the front of the ordered-vector for something that has
	;; the same fixed values and has anything in other fields
	;; do this by first anding with the specified bits and then testing for =
	;; stop looking when you hit something that's worse than the cutoff, because you can't win
	;; compare to the cutoff value scaled to internal node values, then scale internal node
	;; values to external when an answer is found, fewer multiplies that way.
	(loop for node across ordered-vector
	    for node-number = (node-number node)
	    for node-value = (node-value node)
	    ;; if he's a loser return him as a new nogood.
	    when (and scaled-cutoff (< node-value scaled-cutoff))
	    do ;; (format t "~&Adding nogood ~o ~o" mask fixed-key)
	       (return (values nil (list mask fixed-key)))
	    when (= (logand node-number mask) fixed-key)
	    return (values (* scale-factor node-value) node)
		   )))))

(defun convert-surface-rule (constraint)
  (let ((pos (position-if #'listp constraint)))
    (let ((lhs (subseq constraint 0 pos))
	  (rhs (subseq constraint (1+ pos)))
	  (weight (second (nth pos constraint)))
	  )
      (flet ((group-it (plist)
	       (loop for (key value) on plist by #'cddr
		     collect (list key value))))
	(list (group-it lhs) (group-it rhs) weight)))))

(defun convert-surface-rules (constraints)
  (mapcar #'convert-surface-rule constraints))

;;; i'm not sure that this is very useful given that you can just call 
;;; utilty on the feature-set and the node-space
;;; This code used to scale the value returned by utility, but it appears
;;; that utility does that already.

(defun make-utility-function (feature-set preferences intended-max-value 
			      &optional (combining-function #'+) (base-value 0))
  (let ((constraints (mapcar #'convert-surface-rule preferences)))
    (multiple-value-bind (his-ns his-max-value) 
	(process-all-rules constraints feature-set intended-max-value combining-function base-value)
      (declare (ignore his-max-value))
      (values
	 #'(lambda (features)
	     (utility features his-ns))
	 his-ns))))

;;; same comment here about scaling
(defun make-utility-bounds-function (feature-set preferences intended-max-value
			      &optional (combining-function #'+) (base-value 0))
  (let ((constraints (mapcar #'convert-surface-rule preferences)))
    (multiple-value-bind (his-ns his-max-value) 
	(process-all-rules constraints feature-set intended-max-value combining-function base-value)
      (declare (ignore his-max-value))
      (values
       #'(lambda (feature-alist &optional cutoff no-goods)
	   (utility-upper-bounds feature-alist his-ns cutoff no-goods)
	   )
       his-ns))))

;; (eval-when (:execute :load-toplevel)
;;   (export '(make-utility-function make-utility-bounds-function ->)))

#|

simple tests

(defvar ns nil)
(setq ns (make-node-space '((speed fast slow) 
			    (quality high medium low)
			    (privacy public private))))

(defvar node nil)
(setq node (find-feature-set-node '((speed fast) (quality low) (privacy private)) 
				  ns))
(print (decode-node node))

(loop for v1 in '(fast slow)
      do (loop for v2 in '(high medium low)
	       do (loop for v3 in '(private public)
		      for node = (find-feature-set-node `((speed ,v1) 
							  (quality ,v2) 
							  (privacy ,v3))
							ns)
			for decode = (decode-node node)
			do (format t "~%expected ~a ~a ~a got ~a ~a ~a"
				   v1 v2 v3
				   (second (assoc 'speed decode))
				   (second (assoc 'quality decode))
				   (second (assoc 'privacy decode))
				   ))))

(find-feature-set-nodes '((speed fast)) '(quality privacy) ns 
			#'(lambda (node accumulated-dont-cares)
			    (print (decode-node node))
			    (format t "~{~a~^,~}"
				    accumulated-dont-cares)))

(print (distribute '((quality high)) '((quality medium)) ns))
(print (distribute '((speed fast)) '((speed slow)) ns))
(print (distribute '((speed fast)) '((quality low) (privacy private)) ns))
(print (distribute '((privacy public)) '((speed fast) (quality low)) ns))

(print (canonicalize-rule '((quality high)) '((quality medium)) ns))
(print (canonicalize-rule '((speed fast)) '((quality low)) ns))
(print (canonicalize-rule '((speed fast)) '((speed slow)) ns))


(process-a-rule '((quality high)) '((quality medium)) 2 ns)
(process-a-rule '((speed fast)) '((quality low)) 3 ns)
(process-a-rule '((speed fast)) '((speed slow)) 2 ns)

(defparameter rules
  (convert-surface-rules
     '((speed fast (>> 2) speed slow)
       (quality high (>> 2) quality medium)
       (quality medium (>> 2) quality low)
       (privacy private (>> 2) privacy public)
       (speed fast (>> 2) privacy private)
       (quality medium speed fast (>> 2) privacy private)
       (privacy private speed fast (>> 2) quality low))))

(defparameter features
     '((speed fast slow) (quality high medium low) (privacy private public)))

(defparameter feature-evaluator (process-all-rules rules features 10 #'+ 0))

(defun print-em-all ()
  (loop for quality-value in '(high medium low)
      do (loop for speed-value in '(fast slow)
	       do (loop for privacy-value in '(private public)
		      for value = (utility `((speed ,speed-value) 
					     (privacy ,privacy-value) 
					     (quality ,quality-value))
					   feature-evaluator)
			do (format t "~% ~a ~a ~a ~d"
				   quality-value speed-value privacy-value
				   value
				   )))))

(defun umax-new (&optional (features '((speed fast))) 
			   (cutoff 6))
  (utility-upper-bounds features cutoff feature-evaluator))

(defun umax-old ()
  (multiple-value-bind (min max) (utility-bounds '((speed fast)) '(quality privacy) feature-evaluator)
    (format t "~%max = ~d, min = ~d" max min)))

(defparameter util-func1
    (make-utility-function
     '((speed fast slow) (quality high medium low) (privacy private public))
     '((speed fast (>> 2) speed slow)
       (quality high (>> 2) quality medium)
       (quality medium (>> 2) quality low)
       (privacy private (>> 2) privacy public)
       (speed fast (>> 2) privacy private)
       (quality medium speed fast (>> 2) privacy private)
       (privacy private speed fast (>> 2) quality low))
     10))

(defparameter util-func2
    (make-utility-bounds-function 
     '((speed fast slow) (quality high medium low) (privacy private public))
     '((speed fast (>> 2) speed slow)
       (quality high (>> 2) quality medium)
       (quality medium (>> 2) quality low)
       (privacy private (>> 2) privacy public)
       (speed fast (>> 2) privacy private)
       (quality medium speed fast (>> 2) privacy private)
       (privacy private speed fast (>> 2) quality low))
     10))


(funcall util-func1 '((speed fast) (quality high) (privacy private)))
(funcall util-func1 '((speed fast) (quality high) (privacy public)))

(funcall util-func1 '((speed fast) (quality medium) (privacy private)))
(funcall util-func1 '((speed fast) (quality medium) (privacy public)))

(funcall util-func1  '((speed fast) (quality low) (privacy 
(funcall util-func1  '((speed fast) (quality low) (privacy public)))

(funcall util-func1 '((speed slow) (quality high) (privacy private)))
(funcall util-func1 '((speed slow) (quality high) (privacy public)))

(funcall util-func1 '((speed slow) (quality medium) (privacy private)))
(funcall util-func1 '((speed slow) (quality medium) (privacy public)))

(funcall util-func1  '((speed slow) (quality low) (privacy private)))
(funcall util-func1  '((speed slow) (quality low) (privacy public)))

(defparameter feature-set '((speed fast slow) (quality high medium low) (privacy private public)))

(defpreference rule1 (speed fast -> speed slow))
(defpreference rule2 (quality high -> quality medium))
(defpreference rule3 (quality medium -> quality low))
(defpreference rule4 (privacy private -> privacy public))
(defpreference rule5 (speed fast -> privacy private))
(defpreference rule6 (quality medium speed fast -> privacy private))
(defpreference rule7 (privacy private speed fast -> quality low))

(defparameter rules (list rule1 rule2 rule3 rule4 rule5 rule6 rule7))

(defparameter node-space (process-all-rules rules feature-set))

(utility '((speed fast) (quality high) (privacy private)) node-space)
(utility '((speed fast) (quality high) (privacy public)) node-space)

(utility '((speed fast) (quality medium) (privacy private)) node-space)
(utility '((speed fast) (quality medium) (privacy public)) node-space)

(utility  '((speed fast) (quality low) (privacy private)) node-space)
(utility  '((speed fast) (quality low) (privacy public)) node-space)

(utility '((speed slow) (quality high) (privacy private)) node-space)
(utility '((speed slow) (quality high) (privacy public)) node-space)

(utility '((speed slow) (quality medium) (privacy private)) node-space)
(utility '((speed slow) (quality medium) (privacy public)) node-space)

(utility  '((speed slow) (quality low) (privacy private)) node-space)
(utility  '((speed slow) (quality low) (privacy public)) node-space)
         

|#