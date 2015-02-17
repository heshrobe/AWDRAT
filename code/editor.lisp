;;; -*- Mode: Lisp; package: awdrat; readtable: joshua; syntax: joshua -*-

(in-package :awdrat) 

(defvar *component-map* (make-hash-table))


(clim:define-application-frame awdrat
  ()
  ((current-diagram :initform nil :accessor current-diagram)   ; the current system description under simulation
   (system-or-model-mode :initform :system :accessor system-or-model-mode)
   (display-output-tick :initform 0 :accessor display-output-tick )
   (attack-plans :initform nil :accessor attack-plans)
   (merged-attack-plan :initform nil :accessor merged-attack-plan  )
   (show-timings? :initform nil :accessor show-timings)
   )
  (:top-level (awdrat-top-level))
  (:menu-bar nil)
  (:panes
   #-mcl
   (title :title
          :max-height 28
          :display-string "AWDRAT") 
   #-genera
   (pointer :pointer-documentation :borders t
	    :height '(1 :line)
            :max-height '(1 :line))
   (display :application
            :redisplay-after-commands t
            :incremental-redisplay t
            :display-function 'show-system
            :scroll-bars t
            :borders t)
   (conflicts :application
              :height .25 :width .5
              :redisplay-after-commands t
              :incremental-redisplay t
              :display-function 'show-conflicts
              :label "conflicts"
              :scroll-bars t
              :borders t)
   (solutions :application
              :height .25 :width .5
              :redisplay-after-commands t
              :incremental-redisplay t
              :label "solutions"
              :display-function 'show-solutions
              :scroll-bars t
              :borders t)
   (probabilities :application
                  :height .5 :width .5
                  :redisplay-after-commands t
                  :incremental-redisplay t
                  :display-function 'show-probabilities
                  :label "Probabilities"
                  :scroll-bars t
                  :borders t)
   (attacks :application
            :height .25 :width .5
            :redisply-after-commands t
            :incremental-redisplay t
            :display-function 'show-attacks
            :label "Attacks"
            :scroll-bars t
            :borders t)            
   (menu :command-menu 
	 :max-height '(3 :line)
         :height :compute
         :display-function '(clim:display-command-menu :n-columns 6 :row-wise t)
         :scroll-bars nil
         :borders t)
   (interactor :interactor
	       :max-height '(7 :line)
	       :min-height '(4 :line)
	       :initial-cursor-visibility :off
	       :scroll-bars :vertical
	       :end-of-line-action :wrap)
   
   (attack-structure :application
		     :redisplay-after-commands nil
		     :incrmental-redisplay nil
		     :scroll-bars t
		     :borders t)
   )
  (:layouts
   (attack-viewing
    (clim:vertically ()
      #-mcl title
      (:fill attack-structure)
      #-genera
      pointer
      interactor))
   (the-layout
    (clim:vertically ()
      #-mcl title
      (:fill display)
      (clim:horizontally ()
        (clim:vertically () conflicts probabilities)
        (clim:vertically () solutions attack-structure))
      menu
      #-genera
       pointer
      interactor)))
  (:command-definer define-awdrat-command)
  (:command-table awdrat))


(defvar *editor* nil)
(defvar *process* nil)

(defun screen-size ()
  (let ((graft (clim:find-graft)))
    (clim:rectangle-size (clim:sheet-region graft))))

(defmethod awdrat-top-level ((frame awdrat) &REST OPTIONS)
  (let ((*package* (find-package (string-upcase "awdrat"))))
    (APPLY #'clim:default-frame-top-level
	   frame
	   :prompt ">"
	   OPTIONS)))

#-genera
(defun run-editor ()
  (process-run-function 
   "Frame Top Level"
   #'(lambda ()
       (multiple-value-bind (width height) (screen-size)
         (setq *editor* (clim:make-application-frame 'awdrat
                                                     :pretty-name "Model Based Troubleshooter"
                                                     #-allegro :parent #-allegro (clim:find-port)
                                                     :width (floor (* .7 width))
                                                     :height (floor (* .8 height)))))
       (clim:run-frame-top-level *editor*))))


(clim-env::define-lisp-listener-command (com-start-awdrat :name t)
                                        ()
                                        (run-editor))



(defun find-initial-inputs (system)
  (declare (values ports components))
  (let ((ports nil) (components nil))
    (ask `[and [component ,system ?component-name ?component]
               [port input ?component ?port-name]
               [not [known [dataflow ? ? ?port-name ?component]]]]
           #'(lambda (stuff)
               (declare (ignore stuff))
               (pushnew(list 'input ?port-name ?component) ports)
               (pushnew ?component components)))
    (values ports components)))

(defun find-final-outputs (system)
  (let ((answers nil))
    (ask `[and [component ,system ?component-name ?component]
               [port output ?component ?port-name]
               [not [known [dataflow ?port-name ?component ? ? ]]]]
           #'(lambda (stuff)
               (declare (ignore stuff))
               (push (list 'output ?port-name ?component) answers)))
    answers))

(defun earliest-time-of-port (direction port-name component)
  (let ((answer nil))
    (case direction
      (input (ask `[earliest-arrival-time ,port-name ,component ?time]
                  #'(lambda (stuff)
                      (declare (ignore stuff))
                      (setq answer ?time))))
      (output (ask `[earliest-production-time ,port-name ,component ?time]
                   #'(lambda (stuff)
                       (declare (ignore stuff))
                       (setq answer ?time)))))
    answer))

(defun latest-time-of-port (direction port-name component)
  (let ((answer nil))
    (case direction
      (input (ask `[latest-arrival-time ,port-name ,component ?time]
                  #'(lambda (stuff)
                      (declare (ignore stuff))
                      (setq answer ?time))))
      (output (ask `[latest-production-time ,port-name ,component ?time]
                   #'(lambda (stuff)
                       (declare (ignore stuff))
                       (setq answer ?time)))))
    answer))

(define-awdrat-command (com-select-system :name t :menu t)
    ((system-name `((clim:member ,@*top-level-components*)))
     (attack-models `(clim:sequence ((member ,@*attack-models*)))))
  (clear)
  (clrhash *component-map*)
  (let* ((outside (build-interface system-name (intern (gentemp (concatenate 'string (string-upcase (string system-name)) "-")))))
	 (inside (build-implementation system-name outside))
	 (sc (set-up-search-control system-name inside attack-models)))
    (setf (current-diagram clim:*application-frame*) sc
          (display-output-tick clim:*application-frame*) 0)))

(define-awdrat-command (com-clear :name t :menu t)
                    ()
  (setf (current-diagram clim:*application-frame*) nil
        (display-output-tick clim:*application-frame*) 0)
  (case (clim:frame-current-layout clim:*application-frame*)
    (the-layout
     (clim:window-clear *standard-output*)
     (clim:window-clear *standard-input*)
     (clrhash *component-map*)
     (clim:window-clear (clim:get-frame-pane clim:*application-frame* 'solutions))
     (clim:window-clear (clim:get-frame-pane clim:*application-frame* 'conflicts)))
    (otherwise
     (clim:window-clear (clim:get-frame-pane clim:*application-frame* 'attack-structure)))))
                                                                                   

(define-awdrat-command (com-refresh :name t :menu t)
                    ()
  (incf (display-output-tick clim:*application-frame*))
  ;; this is an enormous kludge to force the command-menu to get redisplayed
  ;; when cilm screws up
  (incf (slot-value (clim:find-command-table 'awdrat) 'clim-internals::menu-tick))
  (values))

(defmethod show-conflicts ((m awdrat) stream)
  (let* ((sc (current-diagram m))
	 (system (when sc (component sc)))
         (conflicts nil)
         (components nil))
    (when sc
      (clim:updating-output (stream :unique-id 'table 
                                    :cache-value  (list (display-output-tick m) sc)
                                    :cache-test #'equal)
        (setq conflicts  (when sc (nogoods sc)))        
        (ask `[component ,system ?component-name ?component]
             #'(lambda (just)
                 (declare (ignore just))
                 (push ?component components)))
        (setq components (sort components #'string-lessp :key #'object-name))
        (clim:formatting-table (stream)
          (clim:updating-output (stream :unique-id 'column-header 
                                        :cache-value (list (display-output-tick m) sc)
                                        :cache-test #'equal)
            (clim:formatting-row (stream)
              (loop for c in components 
                    do (clim:updating-output (stream :unique-id c :cache-value c)
                         (clim:formatting-cell (stream) 
                           (format stream "~a" (object-name c)))))))
          (loop for (nil . conflict) in (reverse conflicts)
                for i from 0
                for alist = (loop for a in conflict
                                  collect (with-statement-destructured (component model) a
                                            (cons component model)))
                for entry = (loop for c in components collect (cdr (assoc c alist)))
                do 
                (clim:updating-output (stream :unique-id i :cache-value entry :cache-test #'equal)
                  (clim:formatting-row (stream)
                    (loop for e in entry
                          for c in components
                          do 
                          (clim:updating-output (stream :unique-id c :cache-value e :cache-test #'equal)
                            (clim:formatting-cell (stream)
                              (when e
                                (format stream "~a" e)))))))))))))

(defmethod show-solutions ((m awdrat) stream)
  (let* ((sc (current-diagram m))
         (system (when sc (component sc)))
         (solutions (when sc (solution-states sc)))
         (components nil))
    (when sc
      (clim:updating-output (stream :unique-id 'table 
                                    :cache-value  (list (display-output-tick m) sc)
                                    :cache-test #'equal)
        (ask `[component ,system ?component-name ?component]
             #'(lambda (just)
                 (declare (ignore just))
                 (push ?component components)))
        (setq components (sort components #'string-lessp :key #'object-name))
        (clim:formatting-table (stream)
          (clim:updating-output (stream :unique-id 'column-header :cache-value (display-output-tick m))
            (clim:formatting-row (stream)
              (loop for c in components 
                    do (clim:updating-output (stream :unique-id c :cache-value c)
                         (clim:formatting-cell (stream) (format stream "~a" (object-name c)))))
              ))
          (loop for solution in (reverse solutions)
                for i from 0
                for alist = (loop for a in solution
                                  collect (with-statement-destructured (component model) a
                                            (cons component model)))
                for entry = (loop for c in components collect (cdr (assoc c alist)))
                do 
                (clim:updating-output (stream :unique-id i :cache-value entry :cache-test #'equal)
                  (clim:formatting-row (stream)
                    (loop for e in entry
                          for c in components
                          do (clim:updating-output (stream :unique-id c :cache-value e :cache-test #'equal)
                               (clim:formatting-cell (stream)
                                 (format stream "~a" e))))))))))))

(defmethod show-attacks ((m awdrat) stream)
  (let* ((sc (current-diagram m))
         (system (when sc (component sc)))
         (attacks nil))    
    (clim:updating-output (stream :unique-id 'table 
                                  :cache-value  (list (display-output-tick m) sc)
                                  :cache-test #'equal)
      (when sc
        (ask `[attack ,system ?attack-name ?attack]
             #'(lambda (just)
                 (declare (ignore just))
                 (push ?attack attacks)))
        (setq attacks (sort attacks #'string-lessp))
        (clim:formatting-table (stream)
          (clim:updating-output (stream :unique-id 'column-header 
                                        :cache-value (DISPLAY-OUTPUT-TICK M) 
                                        :cache-test #'equal)
            (clim:formatting-row (stream)
              (clim:formatting-cell (stream) (write-string "Attack" stream))
              (clim:formatting-cell (stream) (write-string "A Priori" stream))
              (clim:formatting-cell (stream) (write-string "Posterior" stream))))
          (loop for attack in attacks
                for prior = (block find-it
                              (ask `[a-priori-probability-of ,attack :true ?prob]
                                   #'(lambda (just)
                                       (declare (ignore just))
                                       (return-from find-it ?prob))))
                for posterior = (ignore-errors (belief-of-attack-node sc attack))
                do (clim:updating-output (stream :unique-id attack
                                                 :cache-value (list prior posterior)
                                                 :cache-test #'equal)
                     (clim:formatting-row (stream)
                       (clim:formatting-cell (stream)
                         (write-string (string attack) stream))
                       (clim:updating-output (stream :unique-id (list attack 'prior)
                                                     :id-test #'equal
                                                     :cache-value prior)
                         (clim:formatting-cell (stream)
                           (format stream "~7,3f" prior)))
                       (clim:updating-output (stream :unique-id (list attack 'posterior)
                                                     :id-test #'equal
                                                     :cache-value posterior)
                         (clim:formatting-cell (stream)
                           (if posterior
                             (format stream "~7,3f" posterior)
                             (format stream "???"))))))))))))

(defmethod show-system ((m awdrat) stream)
  (let* ((sc (current-diagram m))
         (system-or-model-mode (system-or-model-mode m))
         (system (when sc (component sc))))
    (when system
      (clim:updating-output (stream :unique-id sc
                                    :cache-test #'equal
                                    :cache-value (list (display-output-tick m) system-or-model-mode))
        (terpri stream)
        (clim:with-local-coordinates (stream)
          (case system-or-model-mode
            (:system (graph-diagram sc system stream (show-timings m)))
            (:model (graph-models sc system stream)))
          ))))) 

(defmethod trivial-arc-drawer (collector from-object to-object x1 y1 x2 y2)
  (declare (ignore from-object to-object))
  (funcall collector x1 y1 x2 y2))

#||

(defun graph-diagram (sc system-name stream)
  (clim:updating-output (stream :unique-id 'graph :cache-value (display-output-tick clim:*application-frame*))
    (let ((initial-inputs (find-initial-inputs system-name)))
        (clim:format-graph-from-roots
         initial-inputs
         #'(lambda (object stream)
             (typecase object
               (symbol 
                (let ((selected-model (selected-model-for-component object))
                      (resource (component-uses-resource object))
                      (state-alist nil))
                  (ask `[possible-model ,object ?model]
                       #'(lambda (stuff)
                           (declare (ignore stuff))
                           (let ((belief (ignore-errors (belief-of-component-model sc object ?model))))
                             (push (list ?model belief) state-alist))))
                  (clim:updating-output (stream :unique-id object :cache-value (cons selected-model state-alist))
                    (clim:surrounding-output-with-border (stream :shape :rectangle)
                      (format stream "~a" object )
                      (clim:with-text-size (stream :small)
                        (format stream "~& ~a" resource))
                      (loop for (model belief) in state-alist 
                            do
                            (clim:updating-output (stream :unique-id model
                                                          :cache-value (list (eql model selected-model) belief))
                              (clim:with-text-face (stream (if (eql model selected-model) :bold nil))
                                (format stream "~%  ~a ~5,3f" model belief ))))))))
               (cons 
                (destructuring-bind (direction port-name component) object
                  (let ((early (earliest-time-of-port direction port-name component))
                        (late (latest-time-of-port direction port-name component)))
                    (clim:updating-output (stream :unique-id object :id-test #'equal
                                                  :cache-value (list early late))
                      (clim:surrounding-output-with-border (stream :shape :oval)
                        (if (or (eql direction 'output)
                                (member object initial-inputs :test #'equal))
                          (format stream "~a~&[~a ~a]" port-name early late)
                          (format stream "~a" port-name)))))))))
         #'(lambda (object)
             (typecase object
               (symbol (let ((answers nil))
                         (ask `[port output ,object ?port-name]
                              #'(lambda (stuff)
                                  (declare (ignore stuff))
                                  (push (list 'output ?port-name object) answers)))
                         (sort answers #'string-lessp :key #'second)))
               (cons (destructuring-bind (direction port-name component) object
                       (case direction
                         (input (list component))
                         (output (let ((answers nil))
                                   (ask `[dataflow ,port-name ,component ?new-port ?new-component]
                                        #'(lambda (stuff)
                                            (declare (ignore stuff))
                                            (push (list 'input ?new-port ?new-component) answers)))
                                   (sort answers #'string-lessp :key #'third))))))))
         ;; :graph-type :cad
         ;; :arc-drawer #'trivial-arc-drawer
         :stream stream
         :orientation :horizontal
         :merge-duplicates t))))

||#

(defmethod show-probabilities ((m awdrat) stream)
  (let* ((sc (current-diagram m))
         (system (when sc (component sc))))
    (when system
      (table-resources sc system stream))))


(defun all-resource-probabilities (sc)
  (let ((system (component sc))
	(answers nil))
    (ask `[resource ,system ?resource-name ?resource]
	 #'(lambda (just)
	     (declare (ignore just)) 
	     (let ((models nil))
	       (ask [possible-model ?resource ?model]
		    #'(lambda (just)
			(declare (ignore just))
			(let ((belief (ignore-errors (belief-of-component-model sc ?resource ?model)))
			      (apriori (block found
                                           (ask [a-priori-probability-of ?resource ?model ?ap-prob]
                                                #'(lambda (just)
                                                    (declare (ignore just))
                                                    (return-from found ?ap-prob)))
                                           nil)))
                            (push (list ?model belief apriori)  models))))
	       (push (cons ?resource-name models) answers))))
    answers))

(defun table-resources (sc system stream)
  (declare (ignore system))
  (clim:updating-output (stream :unique-id 'table :cache-value (if (typep clim:*application-frame* 'awdrat) (display-output-tick clim:*application-frame*) nil))
    (let ((rows (all-resource-probabilities sc)))
      (setq rows (sort rows #'string-lessp :key #'first))
      (let ((number-of-models (loop for r in rows
                                    for n-of-models = (1- (length r))
                                    maximize n-of-models)))
        (clim:formatting-table (stream)
          (clim:updating-output (stream :unique-id 'header :cache-value number-of-models)
            (clim:formatting-row (stream)
              (clim:formatting-cell (stream) (write-string "resource" stream))
              ;; it's necessary to do the updating outputs below in order to create unique-ids for the 
              ;; repeated headers for model, a-priori, posterior
              (loop for n below number-of-models
                    do 
                    (clim:updating-output (stream :unique-id (list n 'model) :id-test #'equal :cache-value t)
                      (clim:formatting-cell (stream :align-x :center) (write-string "model" stream)))
                    (clim:updating-output (stream :unique-id (list n 'apriori) :id-test #'equal :cache-value t)
                      (clim:formatting-cell (stream :align-x :center) (write-string "a-priori" stream)))
                    (clim:updating-output (stream :unique-id (list n 'posterior) :id-test #'equal :cache-value t)
                      (clim:formatting-cell (stream :align-x :center) (write-string "post" stream))))))
          (loop for (resource . models) in rows
                do (clim:updating-output (stream :unique-id resource :cache-value models :cache-test #'equal)
                     (clim:formatting-row (stream)
                       (clim:updating-output (stream :unique-id 'resource :cache-value resource)
                         (clim:formatting-cell (stream) (format stream "~a" resource)))
                       (loop for (model belief apriori) in models
                             do 
                             (clim:updating-output (stream :unique-id model)
                               (clim:formatting-cell (stream) 
                                 (format stream "~a" model)))
                             (clim:updating-output (stream :unique-id (list model 'apriori)
                                                           :cache-value apriori)
                               (clim:formatting-cell (stream)
                                 (format stream "~7,3f" apriori)))
                             (clim:updating-output (stream :unique-id (list model 'value)
                                                           :cache-value belief)
                               (clim:formatting-cell (stream)
                                 (if belief
                                   (format stream "~7,3f" belief)
                                   (format stream "???")))))))))))))

(defun selected-model-for-component (component-name)
  (ask `[selected-model ,component-name ?model-name]
       #'(lambda (just)
           (declare (ignore just))
           (return-from selected-model-for-component ?model-name)))
  (values nil))

(define-awdrat-command (com-show-timings :name t :menu t)
    ((show? 'boolean))
  (setf (show-timings clim:*application-frame*) show?))

(define-awdrat-command (com-apply-input-timings :name t :menu t)
    ()
  (let* ((sc (current-diagram clim:*application-frame*))
         (system (when sc (component sc)))
         (*editor-in-control* t))
    (declare (special *editor-in-control*))
    (incf (display-output-tick clim:*application-frame*))
    (apply-inputs
     (loop for (nil port-name component) in (find-initial-inputs system)
	 for time = (clim:accept 'number 
				 :prompt (format nil "When was the input ~a of ~a applied?" 
						 port-name component))
	 do (terpri *standard-input*)
	 collect (list port-name component time)))))

(define-awdrat-command (com-apply-output-timings :name t :menu t)
    ()
  (let* ((sc (current-diagram clim:*application-frame*))
         (system (when sc (component sc)))
         (*editor-in-control* t))
    (declare (special *editor-in-control*))
    (incf (display-output-tick clim:*application-frame*))
    (apply-observations
     (loop for (nil port-name component) in (find-final-outputs system)
	 for time = (clim:accept 'number 
				 :prompt (format nil "When was the output ~a of ~a observed?" 
						 port-name component))
	 do (terpri *standard-input*)
	 collect (list port-name component time)))))

(define-awdrat-command (com-apply-observation :name t :menu t)
    ((the-observation 'predication))
  (let* ((sc (current-diagram clim:*application-frame*))
	 (ensemble (component sc))
	 (reformed-predication (parse-observation the-observation ensemble)))
    (tell reformed-predication)
   ))
  
(define-awdrat-command (com-select-models :name t :menu t)
                    ()
  (let* ((sc (current-diagram clim:*application-frame*))
         (system (when sc (component sc))))
    (incf (display-output-tick clim:*application-frame*))
    (remove-all-selected-components sc)
    (ask `[component ,system ?component-name ?component]
         #'(lambda (stuff)
             (declare (ignore stuff))
             (ask `[selected-model ?component ?model]
                  #'(lambda (just)
                      (unjustify (ask-database-predication just))))
             (let ((possible-models nil))
               (ask [possible-model ?component ?model-name]
                    #'(lambda (stuff)
                        (declare (ignore stuff))
                        (push ?model-name possible-models)))
               (let ((selected-model (progn (terpri *standard-input*)
                                            (clim:accept `(clim:member ,@possible-models)
                                                         :display-default t
                                                         :prompt (format nil "Select a model for ~a" ?component)))))
                 (tell `[selected-model ?component ,selected-model] :justification :assumption)))))))

(define-awdrat-command (com-unselect-models :name t :menu t)
                    ()
  (let* ((sc (current-diagram clim:*application-frame*)))
    (incf (display-output-tick clim:*application-frame*))
    (remove-all-selected-components sc)
    (values)))

(defvar *editor-in-control* nil)

(define-awdrat-command (com-solve :name t :menu t)
                    (&key (report 'clim:boolean :default nil))
  (let* ((sc (current-diagram clim:*application-frame*))
         (*report-out-loud* report)
         (*editor-in-control* t))
    (declare (special *report-out-loud* *editor-in-control))
    (find-solutions sc nil)
    (incf (display-output-tick clim:*application-frame*))
    )) 

(defmethod capture-solution :before ((sc search-control))
  (when *editor-in-control*
    (incf (display-output-tick clim:*application-frame*))
    (clim:redisplay-frame-pane clim:*application-frame* 'display)
    ))    

(defmethod capture-solution :after ((sc search-control))
  (when *editor-in-control*
    (clim:redisplay-frame-pane clim:*application-frame* 'solutions)
    ;; (clim:redisplay-frame-pane clim:*application-frame* 'probabilities)
    (format *standard-input* "~%solution found type anything, period skips redisplay")
    (when (char-equal (read-char *standard-input*) #\.)
      (setq *editor-in-control* nil)))) 

(defmethod handle-nogood :after ((sc search-control) condition &key (stupid nil))
  (declare (ignore stupid condition))
  (when *editor-in-control*
    (incf (display-output-tick clim:*application-frame*))
   )) 

(defmethod add-new-nogood :around ((sc search-control) nogood)
  (declare (ignore nogood))
  (multiple-value-bind (new? new-guy) (call-next-method)
    (when *editor-in-control*
      (when new?
        (incf (display-output-tick clim:*application-frame*))
        (clim:redisplay-frame-pane clim:*application-frame* 'conflicts)
        (compute-probabilities sc)
        (clim:redisplay-frame-pane clim:*application-frame* 'probabilities)
        (format *standard-input* "~%Nogood found type anything, period skips redisplay")
        (when (char-equal (read-char *standard-input*) #\.)
          (setq *editor-in-control* nil))))
    (values new? new-guy)))
  

(define-awdrat-command (com-toggle-display-mode :name t :menu t)
                    ()
  (let* ((awdrat clim:*application-frame*)
         (mode (system-or-model-mode awdrat)))
    (case mode
      (:system (setf (system-or-model-mode awdrat) :model))
      (:model (setf (system-or-model-mode awdrat) :system)))
    ))

(defun graph-models (sc system stream)
  (declare (ignore sc))
  (terpri stream)
  (write-string "   " stream)
  (clim:updating-output (stream :unique-id 'model-graph :cache-value (display-output-tick clim:*application-frame*))
    (let ((components (components-in system))
          (resources (resources-in system)))
      (clim:format-graph-from-roots 
       components
       #'(lambda (object stream)
           (clim:updating-output (stream :unique-id object :cache-value object)
                  (clim:surrounding-output-with-border (stream :shape :rectangle)
                    (format stream "~a ~a" 
                            (cond ((member object components) 'component)
                                  ((member object resources) 'resource)
                                  (t 'attack))
			    (if (symbolp object) 
				object
			      (object-name object))))))
       #'(lambda (object)
           (cond 
            ((member object components)
             (resource-for-component object))
            ((member object resources)
             (attacks-against-resource object))))
       :stream stream
       :orientation :horizontal
       :merge-duplicates t)))) 

(defun ports (component direction entry-maker)
  (let ((answers nil))
    (ask `[port ,direction ,component ?port-name]
         #'(lambda (just)
             (declare (ignore just))
             (push (funcall entry-maker ?port-name) answers)))
    (nreverse answers)))



(defstruct (component-map)
  input-alist
  output-alist
  box-width
  box-height
  line-height
  successors
  predecessors
  (tick 0)
  )

(defvar *state-format-string* "~a ~5,3f")

(defun component-entry (component &optional stream)
  (declare (values entry new?))
  (let ((entry (gethash component *component-map*))
        (new? nil))
    (when (and (null entry) (not (null stream)))
      (setq new? t)
      (flet ((entry-maker (name) (list name nil nil)))
        (let* ((inputs  (ports component 'input #'entry-maker))
               (outputs (ports component 'output #'entry-maker))
               (delay-box-size (clim:text-size stream "[NIL, NIL]"))
               (one-char (clim:text-size stream " "))
               (two-char (* 2 one-char))
               (predecessors nil)
               (successors nil)
               (state-alist (state-alist component))
               (pins-on-max-side (max (length inputs) (length outputs))))
          (setq predecessors (task-predecessors component)
                successors (task-successors component))
          (multiple-value-bind (box-width title-height) (clim:text-size stream (string (object-name component)))
            (setq box-width (+ two-char
                               (max box-width
                                    (clim:with-text-face (stream :bold)
                                      (loop for (state) in state-alist
                                            maximize (clim:text-size stream (format nil *state-format-string* state 0.0)))))))
            (let ((box-height (max (+ (* 2 title-height) (* title-height pins-on-max-side 2))
                                   (* title-height (1+ (length state-alist))))))
              (setq entry (make-component-map :input-alist inputs :output-alist outputs
                                              :line-height title-height
                                              :box-width box-width :box-height box-height
                                              :tick 0
                                              :predecessors predecessors :successors successors))
              (let ((pitch (floor box-height (1+ (length inputs))))
                    (max-width (max (if (null predecessors) delay-box-size (clim:text-size stream " "))
                                    (+ two-char
                                       (loop for (input) in inputs
                                             maximize (+ (clim:text-size stream (string input))))))))
                ;; if we're an input component we also include delay in the display of input pins
                (loop for input in inputs
                      for y from pitch by pitch
                      do (setf (second input) (- max-width)
                               (third input) y)))
              (let ((pitch (floor box-height (1+ (length outputs))))
                    (max-width (max delay-box-size
                                    (+ two-char 
                                       (loop for (output) in outputs
                                             maximize (clim:text-size stream (string output)))))))
                (loop for output in outputs
                      for y from  pitch by pitch
                      do (setf (second output) (+ max-width box-width)
                               (third output) y)))                
              (setf (gethash component *component-map*) entry))))))
    (values entry new?)))

(defun display-component (component stream sc show-timings)
  (let* ((entry (component-entry component stream))
         (tick (component-map-tick entry))
         (initial-component? (null (component-map-predecessors entry)))
         (input-alist (component-map-input-alist entry))
         (output-alist (component-map-output-alist entry))
         (line-height (component-map-line-height entry))
         (one-char (clim:text-size stream " "))
         (box-width (component-map-box-width entry))
         (box-mid (floor box-width 2))
         (box-height (component-map-box-height entry)))
    (multiple-value-bind (state-alist selected-model) (state-alist component sc)
      (clim:updating-output (stream :unique-id component :cache-value (list tick selected-model state-alist))
        (clim:draw-rectangle* stream 0 0 box-width box-height :filled nil)
        ;; the component name
        (clim:draw-text* stream (string (object-name component))
                         box-mid 0
                         :align-y :top
                         :align-x :center)
        ;; the states and probabilities
        (loop for (model belief) in state-alist 
              for y from line-height by line-height
              do
              (clim:updating-output (stream :unique-id model
                                            :cache-value (list (eql model selected-model) belief))
                (clim:with-text-face (stream (if (eql model selected-model) :bold nil))
                  (clim:draw-text* stream (string model)
                                   one-char y
                                   :align-x :left :align-y :top)
                  (clim:draw-text* stream (format nil "~5,3f" (or belief "???"))
                                   (- box-width one-char) y
                                   :align-x :right :align-y :top))))
        ;; the inputs and pins
        (loop for (input x y) in input-alist
              do (clim:draw-line* stream x y 0 y)
              if initial-component? 
              do (multiple-value-bind (early late) (arrival-time-of input component)
                   (clim:updating-output (stream :unique-id (list component 'input input)
						 :id-test #'equal
                                                 :cache-value (list early late))
                     (clim:draw-text* stream (string input)
                                      (- 0 one-char) y
                                      :align-x :right
                                      :align-y :top)
		     (when show-timings
		       (clim:draw-text* stream (format nil "[~a ~a]" early late)
					(- 0 one-char) (+ y line-height)
					:align-x :right
					:align-y :top))))
	    else do (clim:updating-output (stream :unique-id (list component 'input input)
						  :id-test #'equal
                                                    :cache-value (list nil nil))
                        (clim:draw-text* stream (string input) (- 0 one-char) y
                                         :align-x :right :align-y :top)))
        (loop for (output x y) in output-alist
              do (clim:draw-line* stream box-width y x y)
              (multiple-value-bind (early late) (production-time-of output component)
                (clim:updating-output (stream :unique-id (list component 'output output) 
					      :id-test #'equal
                                              :cache-value (list early late)) 
                  (clim:draw-text* stream (string output)
                                   (+ one-char box-width) y
                                   :align-y :top
                                   :align-x :left)
		  (when show-timings
		    (clim:draw-text* stream (format nil "[~a ~a]" early late)
				     (+ one-char box-width) (+ y line-height)
				     :align-y :top
				     :align-x :left)))))))))

(defun state-alist (component &optional sc)
  (declare (values state-alist selected-model ))
  (let ((selected-model (selected-model-for-component component))
        (state-alist nil))
    (ask `[possible-model ,component ?model]
         #'(lambda (stuff)
             (declare (ignore stuff))
             (let ((belief (when sc (ignore-errors (belief-of-component-model sc component ?model)))))
               (push (list ?model belief) state-alist))))
    (values state-alist selected-model)))

(defun state-alist-by-name (component-name sc)
  (let ((component (component-named (component sc) component-name)))
    (state-alist component sc)))

(defun production-time-of (port-name component)
  (values (earliest-time-of-port 'output port-name component)
          (latest-time-of-port 'output port-name component)))

(defun arrival-time-of (port-name component)
  (values (earliest-time-of-port 'input port-name component)
          (latest-time-of-port 'input port-name component))) 

(defun task-successors (object) 
  (let ((successors nil))
    (ask `[dataflow ? ,object ? ?successor]
         #'(lambda (just)
             (declare (ignore just))
             (pushnew ?successor successors)))
    (nreverse successors)))

(defun task-predecessors (object) 
  (let ((predecessors nil))
    (ask `[dataflow ? ?predecessor ? ,object]
         #'(lambda (just)
             (declare (ignore just))
             (pushnew ?predecessor predecessors)))
    (nreverse predecessors)))

(defun task-connection-maker (collector from-object to-object x1 y1 x2 y2)
  (let* ((from-entry (component-entry from-object))
         (from-box-height (component-map-box-height from-entry))
         (from-y-0 (- y1 (floor from-box-height 2)))
         (from-output-alist (component-map-output-alist from-entry))
         (to-entry (component-entry to-object))
         (to-box-height (component-map-box-height to-entry))
         (to-y-0 (- y2 (floor to-box-height 2)))
         (to-input-alist (component-map-input-alist to-entry)))
    (ask `[dataflow ?from-port ,from-object ?to-port ,to-object]
         #'(lambda (just)
             (declare (ignore just))
             (let ((from-entry (assoc ?from-port from-output-alist))
                   (to-entry (assoc ?to-port to-input-alist)))
               (destructuring-bind (from-x from-y) (cdr from-entry)
                 (declare (ignore from-x))
                 (destructuring-bind (to-x to-y) (cdr to-entry)
                   (declare (ignore to-x))
                   (funcall collector
                            x1 (+ from-y from-y-0)
                            x2 (+ to-y to-y-0)))))))))
                        
             

(defun graph-diagram (sc system stream show-timings)
  (clim:updating-output (stream :unique-id 'graph :cache-value (display-output-tick clim:*application-frame*))
    (multiple-value-bind (ports components) (find-initial-inputs system)
      (declare (ignore ports))
      (clim:format-graph-from-roots
       components
       #'(lambda (object stream)
           (display-component object stream sc show-timings))
       #'task-successors
       :graph-type :cad
       :arc-drawer #'task-connection-maker
       :stream stream
       :orientation :horizontal
       :merge-duplicates t))))

(define-predicate-method (notice-truth-value-change earliest-arrival-time :after) (old-truth-value)
  (when *editor-in-control*
    (update-component-for-change self old-truth-value)))

(define-predicate-method (notice-truth-value-change earliest-production-time :after) (old-truth-value)
  (when *editor-in-control*
    (update-component-for-change self old-truth-value)))

(define-predicate-method (notice-truth-value-change latest-arrival-time :after) (old-truth-value)
  (when *editor-in-control*
    (update-component-for-change self old-truth-value)))

(define-predicate-method (notice-truth-value-change latest-production-time :after) (old-truth-value)
  (when *editor-in-control*
    (update-component-for-change self old-truth-value))) 

(defun update-component-for-change (predication old-truth-value)
  (when (not (eql (predication-truth-value predication) old-truth-value))
    (with-statement-destructured (port component time) predication
      (declare (ignore time port))
      (let ((entry (component-entry component)))
        (incf (component-map-tick entry))))))

(defun dump-posterior-probabilities (sc pathname)
  (let* ((probabilities (all-resource-probabilities sc))
	 (posteriors-only nil))
    (loop for (resource . alist) in probabilities
	do (push (cons resource
		       (loop for (resource posterior nil) in alist
			   append (list resource posterior)))
		 posteriors-only))
    (with-open-file (f pathname :direction :output 
		     :if-exists :supersede
		     :if-does-not-exist :create)
      (loop for row in posteriors-only
	  do (print row f)))))
