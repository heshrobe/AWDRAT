;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat; readtable: joshua -*-

(in-package :awdrat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; A simple program written to test the lisp monitoring version of AWDRAT
;;;
;;; For lack of a better idea, I'll use the example from the natural-software seedling
;;; a 3 step pipeline that 
;;; 1) Reads buffers from a stream
;;; 2) Reformats the buffers into a stream of packets
;;; 3) Queues the packets into an output queue
;;;
;;; The single attack to be modeled is that the second stage also opens a stream and writes to it
;;; Presumbably because of a "buffer overflow in stage 1) that gives the attacker control
;;;   Actually we'll just put that into the code
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *port-number* 35794.)
(defparameter *listening-socket* nil)
(defparameter *listening-stream* nil)
(defparameter *image-source-stream* nil)

(defun open-listening-stream (port-number)
  (let ((socket (socket:make-socket :connect :passive 
				    :local-port port-number
				    :local-host "localhost")))
    (setq *listening-socket* socket)
    (let ((stream (socket:accept-connection socket)))
      (setq *listening-stream* stream)
      (values *listening-stream* *listening-socket*))))

(defun read-image-from-device (stream)
  (when (null stream) (error "stream can't be null"))
  (read stream))

(defun pipeline-processor (input-port output-queue)
  (multiple-value-bind (stream socket) (open-listening-stream input-port)
    (unwind-protect
	(let ((image (read-image-from-device stream)))
	  (reformat-image image output-queue))
      (close stream)
      (close socket)
      (setq *listening-stream* nil
	    *listening-socket* nil)))
  output-queue)

(defun enqueue (queue thing)
  (clim-utils:queue-put queue thing))

(defun reformat-image (image queue)
  (with-open-file (F "~/exfiltration.text" :if-does-not-exist :create :if-exists :supersede :direction :output)
  (destructuring-bind (x y) (array-dimensions image)
    (loop with buffer = (make-array 512 :element-type '(unsigned-byte 8) :fill-pointer 0)
	for i below x
	do (loop for j below y
	       for pixel = (aref image i j)
	       do (loop for byte-number below 32 by 8
		      for next-byte = (ldb (byte 8 byte-number)  pixel)
		      do (vector-push next-byte buffer)
		      when (eql (length buffer) 512)
		      do (enqueue queue buffer)
			 (format f "~%buffer written")
			 (setq buffer (make-array 512 :element-type '(unsigned-byte 8) :fill-pointer 0))))))))


;;; simulating a device stream
;;; not really part of the application

(defun create-image-source-stream ()
  (let ((port-number *port-number*))
    (let ((image (make-array '(100 1000) :element-type '(unsigned-byte 32))))
      (let ((stream (open-image-source-socket port-number)))
	(unwind-protect
	    (write image :stream stream)
	  (close stream)))))
  (values))

(defun open-image-source-socket (port-number &optional (host "localhost"))
  (let ((socket (socket:with-pending-connect 
		    (mp:with-timeout (100 (print "Counldn't connect"))
		      (socket:make-socket 
		       :connect :active 
		       :remote-port port-number
		       :remote-host host
		       )))))
    (setq *image-source-stream* socket)
    socket
    ))
  

;;; tie the two processes together

(defun simple-example-driver ()
  (let ((simulated-device-process (mp:process-run-function "producer" #'create-image-source-stream))
	(queue (clim-utils:make-queue)))
    (pipeline-processor (incf *port-number*) queue)
    (values queue simulated-device-process)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The AWDRAT Model for the above
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Relevant Events

;;; The connection to the "device stream"
(register-event stream-started open-listening-stream)
;;; enqueuing a buffer
(register-event buffer-enqueued enqueue)
;;; the main loop of reading an image and reformatting it
(register-event reformat-image reformat-image)
;;; the whole program
(register-event main-program pipeline-processor)
;;; getting an image from the stream
(register-event get-image read-image-from-device)

(define-predicate appropriate-number-of-enqueues (queue situation)
  (modeling-mixin))

(define-ensemble simple-example
    :top-level t
    :entry-events (main-program)
    :exit-events (main-program)
    :allowable-events (get-image)
    :inputs (port-number queue)
    :outputs (updated-queue)
    :components ((open-stream :type open-stream :models (norma))
		 (reformat-image :type reformat-image :models (normal exfilitration)))
    :dataflows ((port-number simple-example port-number open-stream)
		(stream open-stream stream reformat-image)
		(queue simple-example queue reformat-image)
		(updated-queue reformat-image updated-queue simple-example))
    :controlflows ()
    :resources ((stream-open-code code-file)
		(reformatter-code code-file))
    :resource-mappings ((open-stream open-stream-code)
			(reformat-image reformatter-code))
    :model-mappings (;; reformat-image will almost certainly behave normally if the code is OK
		     ;; and is very unlikely to behave normally if the code is hacked
		     (reformat-image normal ((reformatter-code normal)) .9) 
		     (reformat-image normal ((reformatter-code hacked)) .1)
		     ;; it's very likely to behave abnormally if the code is hacked
		     ;; and is very unlikely to behave abnormally if the code is OK
		     (reformat-image exfilitration ((reformatter-code  hacked)) .9) 
		     (reformat-image exfilitration ((reformatter-code  hacked)) .1)
		     )
    )

(define-ensemble open-stream
    :inputs (port-number)
    :outputs (stream)
    :entry-events (stream-started)
    :exit-events ((stream-started exit (stream)))
    :allowable-events (open-socket)
    )

(defbehavior-model (open-stream normal)
    :inputs (port-number)
    :outputs (stream)
    :prerequisites ((typep ?port-number '(integer 0)))
    :post-conditions ((typep ?stream 'stream))
    )

(define-ensemble reformat-image
    :inputs (stream queue)
    :outputs (updated-queue)
    :entry-events (reformat-image)
    :exit-events (reformat-image)
    :allowable-events (buffer-enqueued)
    )

(defbehavior-model (reformat-image normal)
    :inputs (stream queue) 
    :outputs (updated-queue)
    :prerequisites 
    ((typep ?stream 'stream)
		    (typep ?queue 'clim-utils:queue))
    :post-conditions ((typep ?updated-queue 'clim-utils:queue)
		      [appropriate-number-of-enqueues ?updated-queue]
		      )
    )

(defbehavior-model (reformat-image exfiltration)
    :inputs (stream queue)
    :outputs (updated-queue)
    :prerequisites ((typep ?stream 'stream)
		    (typep ?queue 'clim-utils:queue))
    :postconditions ((typep ?updated-queue 'clim-utils:queue)
		     [appropriate-number-of-enqueues ?updated-queue]
		     ))

(defparameter *my-ensemble* nil)
(defparameter *my-component* nil)

(defparameter *number-of-pixels-read* 0)
(defparameter *number-of-enqueues* 0)

(deftracer (get-image exit) (image &rest ignore)
  (declare (ignore ignore))
  (let ((x-dim (array-dimension image 0))
	(y-dim (array-dimension image 1)))
    (incf *number-of-pixels-read* (* x-dim y-dim))))

(deftracer (buffer-enqueued exit) (&rest ignore)
  (declare (ignore ignore))
  (incf *number-of-enqueues*))

(deftracer (reformat-image exit) (queue &rest ignore)
  (declare (ignore ignore))
  (let ((number-of-bytes-read (* *number-of-pixels-read* 4))
	(number-of-enqueued-bytes (* *number-of-enqueues* 512.))
	(situation (situation-named *my-ensemble*'after 'reformat-image)))
    (if (= number-of-bytes-read number-of-enqueued-bytes)
	(tell `[appropriate-number-of-enqueues ,queue ,situation])
      (tell `[not [appropriate-number-of-enqueues ,queue ,situation]])
      )))

(deftracer (main-program entry) (port-number queue &rest ignore)
  (declare (ignore ignore))
  (setq *number-of-enqueues* 0
	*number-of-enqueues* 0)
  ;; catch the initial inputs and provide them to the simulator
  (tell `[input port-number ,*my-component* ,port-number])
  (tell `[input queue ,*my-component* ,queue]))


(defun simple-example-harness ()
  (clear)
  ;; this means we'll only get events from this thread, not others
  ;; running concurrently (e.g. the "device-stream" thread)
  (clim-utils:letf-globally ((*monitored-threads* (list mp:*current-process*)))
    (install-all-events)
    (unwind-protect
	(let* ((outside (build-outside 'simple-example 'my-example))
	       (inside (build-inside 'simple-example outside)))
	  (setq *my-ensemble* inside *my-component* outside)
	  (simple-example-driver))
      (uninstall-all-events)
      )))
    