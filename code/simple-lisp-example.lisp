;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat; readtable: joshua -*-

(in-package :awdrat)

(defvar *exfiltration-attack* nil)
(defvar *piggy-back-data-exfiltration-attack* nil)
(defvar *data-loss-attack* nil)
(defvar *trace-buffers* nil)

;;; Note: in this version rearranging so that resources and all the stuff associated
;;; isn't all pushed to the top level
;;; A shared resource is described at the lub of the parts that share it
;;; and is passed down as an argument to the sub-parts

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; A simple program written to test the lisp monitoring version of AWDRAT
;;;
;;; For lack of a better idea, I'll use the example from the natural-software seedling
;;; a 3 step pipeline that 
;;; 1) Reads buffers from a queue
;;; 2) Reformats the buffers into a stream of packets
;;; 3) Queues the packets into an output queue
;;;
;;; The single attack to be modeled is that the second stage also opens a stream and writes to it
;;; Presumbably because of a "buffer overflow in stage 1) that gives the attacker control
;;;   Actually we'll just put that into the code
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;; There are two processes:
;;;  1) A process that writes images to a stream
;;;  2) A process that reads imagesa from the stream and reformats them into "buffers"
;;;     that are queued

;;; This top level ties the two together 
;;; Makes sure that *port-number* is unused (sort of) and 
;;; then passes that number to the two processes
;;;  one for the write and one 
;;; tie the two processes together

(defun simple-example-driver ()
  ;; Make sure there's a socket 
  ;; and make sure that it's a new port-number
  (let ((image-queue (clim-utils::make-queue)))
    (let ((simulated-device-process (mp:process-run-function "producer" #'create-image-source-queue image-queue))
	  (buffer-queue (clim-utils:make-queue)))
      (pipeline-processor image-queue buffer-queue)
      (values buffer-queue image-queue simulated-device-process))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The listening stream
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pipeline-processor (image-queue output-queue)
  (let ((image (read-image-from-device image-queue)))
    (reformat-image image output-queue)
    output-queue))

(defun read-image-from-device (image-queue)
  (declare (special *exfiltration-attack*))
  (when (null image-queue) (error "image queue can't be null"))
  (mp:process-wait "waiting for image"
		   #'(lambda (queue)
		       (not (clim-utils:queue-empty-p queue)))
		   image-queue)
  (let ((image (clim-utils:queue-get image-queue)))
    (declare (special *exfiltration-attack*))
    (when *exfiltration-attack*
      (with-open-file (F "~/exfiltration.text" :if-does-not-exist :create :if-exists :append :direction :output)
	(write image :stream f)))
    image))
    


(defun enqueue (queue thing)
  (clim-utils:queue-put queue thing)
  (values thing queue))

(defun reformat-image (image queue)
  (declare (special *exfiltration-attack* *piggy-back-data-exfiltration-attack* *data-loss-attack* *trace-buffers*))
  (let ((buffer-number 0))
    (destructuring-bind (x y) (array-dimensions image)
      (loop with buffer = (make-array 512 :element-type '(unsigned-byte 8) :fill-pointer 0)
	  for i below x
	  do (loop for j below y
		 for pixel = (aref image i j)
		 do (loop for byte-number below 32 by 8
			for next-byte = (ldb (byte 8 byte-number)  pixel)
			do (vector-push next-byte buffer)
			when (eql (length buffer) 512)
			do (when (or (null *data-loss-attack*) (oddp (+ i j)))
			     (enqueue queue buffer))
			   (when *trace-buffers*
			     (format t "~%Enqueueing buffer ~d" buffer-number))
			   (when *piggy-back-data-exfiltration-attack*
			     ;; this is an attack where extra buffers filled with other data
			     ;; are enqueue and shipped off
			     (enqueue queue (make-array 512. :element-type '(unsigned-byte 8) :fill-pointer 512.)))
			   (setq buffer (make-array 512 :element-type '(unsigned-byte 8) :fill-pointer 0))))))
    (values queue)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The source stream
;;;
;;; simulating a device stream
;;; not really part of the application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun create-image-source-queue (image-queue)
  (let ((image (make-array '(256. 256.) :element-type '(unsigned-byte 32))))
      (clim-utils:queue-put image-queue image))
  (values))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The AWDRAT Model for the above
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Relevant Events

;;; enqueuing a buffer
(register-event buffer-enqueued enqueue)
;;; the main loop of reading an image and reformatting it
(register-event reformat-image reformat-image)
;;; somebody doing an open, possibly for exfiltration
(register-event open open)
;;; the whole program
(register-event main-program pipeline-processor)
;;; getting an image from the stream
(register-event get-image read-image-from-device)
;;; opening a stream on a socket
(register-event open-socket socket:accept-connection)

;;; should be low, normal or high
(define-predicate number-of-packets (qualitative-amount situation)
  (modeling-mixin))

(defrule packet-consistency (:forward)
  if [and [number-of-packets ?value1 ?situation]
	  [number-of-packets ?value2 ?situation]
	  (not (eql ?value1 ?value2))
	  ]
  then [ltms:contradiction]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Defining the structural model
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; There are no shared resources so this is pretty simple
(define-component-type simple-example
    :top-level t
    :primitive nil
    :entry-events (main-program)
    :exit-events (main-program)
    :allowable-events (get-image)
    :inputs (image-queue queue)
    :outputs (updated-queue)
    :components ((get-image :type get-image :models (normal exfiltration))
		 (reformat-image :type reformat-image :models (normal piggy-back data-loss)))
    :dataflows ((image-queue simple-example image-queue get-image)
		(image get-image image reformat-image)
		(queue simple-example queue reformat-image)
		(updated-queue reformat-image updated-queue simple-example))
    :controlflows ()
    :behavior-modes (normal)
    )

(defbehavior-model (simple-example normal)
    :inputs (image-queue queue)
    :outputs (updated-queue)
    )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Get-Image
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-resource-type code-file
    :modes (normal hacked)
    :prior-probabilities ((normal .8) (hacked .2))
    :vulnerabilities (loads-code-file reads-code-file))

(define-component-type get-image
    :primitive t
    :inputs (image-queue)
    :outputs (image)
    :entry-events (get-image)
    :exit-events (get-image)
    :resources ((get-image-code code-file))
    :behavior-modes (normal exfiltration)
    :behavior-dependencies (;; get-image will almost certainly behave normall if the code is OK
			    (normal ((get-image-code normal)) .9)
			    (normal ((get-image-code hacked)) .1)
			    ;; but likely to behave abnormally if hacked
			    (exfiltration ((get-image-code  hacked)) .9) 
			    (exfiltration ((get-image-code  normal)) .1))
    )

(defbehavior-model (get-image normal)
    :inputs (image-queue)
    :outputs (image)
    :prerequisites ([data-type-of ?image-queue clim-utils:queue])
    :post-conditions ([data-type-of ?image array])
    )

(defbehavior-model (get-image exfiltration)
    :inputs (image-queue)
    :outputs (image)
    :prerequisites ([data-type-of ?image-queue clim-utils:queue])
    :post-conditions ([data-type-of ?image array])
    :allowable-events (open write)
    )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Reformat Image
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-component-type reformat-image
    :primitive t
    :inputs (image queue)
    :outputs (updated-queue)
    :entry-events (reformat-image)
    :exit-events (reformat-image)
    :allowable-events (buffer-enqueued)
    :resources ((reformatter-code code-file))
    :behavior-modes (normal data-loss exfiltration piggy-back)
    :behavior-dependencies ( ;; reformat-image will almost certainly behave normally if the code is OK
			    ;; and is very unlikely to behave normally if the code is hacked
			    (normal ((reformatter-code normal)) .9) 
			    (normal ((reformatter-code hacked)) .1)
			    ;; it's very likely to behave abnormally if the code is hacked
			    (piggy-back ((reformatter-code  hacked)) .9) 
			    (piggy-back ((reformatter-code  normal)) .1)
			    ;; similarly for data-loss
			    (data-loss ((reformatter-code  hacked)) .9) 
			    (data-loss ((reformatter-code  normal)) .1)
			    ;; and exfiltration
			    (exfiltration ((reformatter-code  hacked)) .9)
			    (exfiltration ((reformatter-code  hacked)) .9)
			    )
    )


(defbehavior-model (reformat-image normal)
    :inputs (image queue) 
    :outputs (updated-queue)
    :prerequisites ([data-type-of ?image array]
		    [data-type-of ?queue clim-utils:queue])
    :post-conditions ([data-type-of ?updated-queue clim-utils:queue]
		      [number-of-packets normal]
		      )
    )

(defbehavior-model (reformat-image exfiltration)
    :inputs (image queue)
    :outputs (updated-queue)
    :prerequisites ([data-type-of ?image array]
		    [data-type-of ?queue clim-utils:queue])
    :post-conditions ([data-type-of ?updated-queue clim-utils:queue]
		      [number-of-packets normal]
		      )
    )

(defbehavior-model (reformat-image piggy-back)
    :inputs (image queue)
    :outputs (updated-queue)
    :prerequisites ([data-type-of ?image array]
		    [data-type-of ?queue clim-utils:queue])
    :post-conditions ([data-type-of ?updated-queue clim-utils:queue]
		      [number-of-packets high])
    )

(defbehavior-model (reformat-image data-loss)
    :inputs (image queue)
    :outputs (updated-queue)
    :prerequisites ([data-type-of ?image array]
		    [data-type-of ?queue clim-utils:queue])
    :post-conditions ([data-type-of ?updated-queue clim-utils:queue]
		      [number-of-packets low])
    )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Tracers that gather data during execution
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *number-of-pixels-read* 0)
(defparameter *number-of-bytes-enqueued* 0)
(defparameter *number-of-enqueues* 0)

(deftracer (main-program entry) (image-queue queue &rest ignore)
  (declare (ignore image-queue queue ignore))
  (setq *number-of-enqueues* 0
	*number-of-bytes-enqueued* 0
	*number-of-pixels-read* 0)
  ;; this is now done by the generic notice event method
  ;; catch the initial inputs and provide them to the simulator
  ;; (tell `[input socket ,*my-component* ,socket])
  ;; (tell `[input queue ,*my-component* ,queue])
  )

(deftracer (get-image exit) (image &rest ignore)
  (declare (ignore ignore))
  (let ((x-dim (array-dimension image 0))
	(y-dim (array-dimension image 1)))
    (incf *number-of-pixels-read* (* x-dim y-dim))))

(deftracer (buffer-enqueued exit) (buffer queue)
  (declare (ignore queue))
  (incf *number-of-enqueues*)
  (incf *number-of-bytes-enqueued* (length buffer))
  ;; should check if too many bytes are enqueued
  ;; and if so barf by asserting that the wrong number of 
  ;; enqueues have happened and also asserting that
  ;; the right number of enqueues have happened justified by the 
  ;; assumption that the normal mode of execution for reformat image
  ;; has been selected.  This would happen normally on completion
  ;; of reformat-image, but we might never get to the conclusion
;;;  (when (> *number-of-bytes-enqueued* (* 4 *number-of-pixels-read*))
;;;    (let ((situation (situation-named *my-ensemble* 'after 'reformat-image)))
;;;      ;; assert that this screwed up
;;;      (tell `[number-of-packets high ,situation])
;;;      )
;;;    ;; and make him think that he saw the exit for the enclosing routine
;;;    (notice-event 'reformat-image 'exit (get-universal-time) mp:*current-process*
;;;		  (list queue)))
  )


(deftracer (reformat-image exit) (queue)
  (declare (ignore queue))
  (declare (special *my-ensemble*))
  (let ((number-of-bytes-read (* *number-of-pixels-read* 4))
	(number-of-bytes-enqueued *number-of-bytes-enqueued*)
	(situation (situation-named *my-ensemble* 'after 'reformat-image)))
    (cond
     ((= number-of-bytes-read number-of-bytes-enqueued)
      (tell `[number-of-packets normal ,situation]))
     ((< number-of-bytes-read number-of-bytes-enqueued)
      (tell `[number-of-packets high ,situation]))
     (t (tell `[number-of-packets low ,situation]))
      )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Attack Modeling
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-attack-model hacked-code-files
    :attack-types ((hacked-code-file-attack .5)
		   (hacked-image-file-attack .5)
		   )
    :vulnerability-mapping (
			    (reads-complex-imagery hacked-image-file-attack)
			    (loads-code-file hacked-code-file-attack)
			    ))

;;; rules mapping conditional probabilities of vulnerability and attacks

;;; A hacked image file attack can corrupt the file
(defrule bad-image-file-takeover (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource image-file]
	  [resource-might-have-been-attacked ?resource hacked-image-file-attack]]
  then [and [attack-implies-compromised-mode hacked-image-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-image-file-attack ?resource normal .1 ]])

;;; This is really short-hand for a hacked image file can inject code thereby compromising
;;; the code in memory
(defrule bad-image-file-takeover-2 (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource code-memory-image]
	  [resource-might-have-been-attacked ?resource hacked-image-file-attack]]
  then [and [attack-implies-compromised-mode hacked-image-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-image-file-attack ?resource normal .1 ]])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;      Hacked Code file attacks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A hacked code file attack can corrupt the file
(defrule hacked-code-file-takeover (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource code-file]
	  [resource-might-have-been-attacked ?resource hacked-code-file-attack]]
  then [and [attack-implies-compromised-mode hacked-code-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-code-file-attack ?resource normal .1 ]])

;;; 
(defrule hacked-code-file-takeover-2 (:forward)
  if [and [resource ?ensemble ?resource-name ?resource]
	  [resource-type-of ?resource code-memory-image]
	  [resource-might-have-been-attacked ?resource hacked-code-file-attack]]
  then [and [attack-implies-compromised-mode hacked-code-file-attack ?resource hacked .9 ]
	    [attack-implies-compromised-mode hacked-code-file-attack ?resource normal .1 ]])


;;; I think this is just a copy of the above
;;;(defrule bad-code-file-takeover (:forward)
;;;  if [and [resource ?ensemble ?resource-name ?resource]
;;;	  [resource-type-of ?resource code-file]
;;;	  [resource-might-have-been-attacked ?resource hacked-code-file-attack]]
;;;  then [and [attack-implies-compromised-mode hacked-code-file-attack ?resource hacked .9 ]
;;;	    [attack-implies-compromised-mode hacked-code-file-attack ?resource normal .1 ]])
;;;
;;;(defrule bad-code-file-takeover-2 (:forward)
;;;  if [and [resource ?ensemble ?resource-name ?resource]
;;;	  [resource-type-of ?resource code-memory-image]
;;;	  [resource-might-have-been-attacked ?resource hacked-code-file-attack]]
;;;  then [and [attack-implies-compromised-mode hacked-code-file-attack ?resource hacked .9 ]
;;;	    [attack-implies-compromised-mode hacked-code-file-attack ?resource normal .1 ]])


(defun simple-example-harness (&key (exfiltration nil)
				    (piggy-back nil)
				    (data-loss nil)
				    (trace-buffers nil))
  (let ((*exfiltration-attack* exfiltration)
	(*piggy-back-data-exfiltration-attack* piggy-back)
	(*data-loss-attack* data-loss)
	(*trace-buffers* trace-buffers))
    (declare (special *exfiltration-attack* *piggy-back-data-exfiltration-attack* *data-loss-attack* *trace-buffers*))
    (with-harness (simple-example)
      (simple-example-driver))))

 