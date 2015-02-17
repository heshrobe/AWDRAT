;;; -*- Syntax: Ansi-common-lisp; Package: cl-USER; Base: 10; Mode: LISP -*-

(in-package :cl-user)

(defpackage awdrat
  (:import-from "MP" "PROCESS-RUN-FUNCTION")
  (:import-from "EXCL" "DEF-FWRAPPER" "FWRAP" "FUNWRAP" "CALL-NEXT-FWRAPPER")
  (:nicknames "aw")
  (:export ;; Trust Model Associated
	   "READ-IN-TRUST-MODEL" 
	   "TRUST-MODEL-CASE"
	   "UPDATE-TRUST-MODEL" 
	   "WRITE-OUT-TRUST-MODEL"
	   "*TRUST-MODEL*"	   
	   ;; Defining Architectural Model
	   "DEFINE-ENSEMBLE" "DEFBEHAVIOR-MODEL" "DEFSPLIT"
	   "DEFINE-ATTACK-MODEL" "BUILD-OUTSIDE" "BUILD-INSIDE"
	   ;; dynamic status of the simulation
	   "EXECUTION-STATUS" "READY" "COMPLETED" "STARTED" "NORMAL"
	   "ENTRY" "EXIT" "ALLOWABLE" "SELECTED-MODEL"
	   ;; Diagnosis and Architectural Model Tracking
	   "GET-PROXY"
	   "REGISTER-EVENT" "REGISTER-CLASS" "CLEAR-REGISTRIES"
	   "GENERATE-WRAPPER-SUPPORT"
	   "DEFTRACER"
	   "NOTICE-EVENT"
	   "SEARCH-CONTROL" 
	   "ENSEMBLE"
	   "IO-NAMED" 
	   "SITUATION-NAMED" 
	   "INTERVAL-NAMED"
	   "*REPORT-OUT-LOUD*" 
	   "*EDITOR-IN-CONTROL*"
	   "FIND-SOLUTIONS"
	   "INIT-CASE"
	   "INPUT" "OUTPUT" "BEFORE" "AFTER" "DURING"
	   ;; Getting Diagnosis out
	   "ALL-RESOURCE-PROBABILITIES"
	   "SOLUTION-STATES" 
	   "STATE-ALIST-BY-NAME"
	   "CONVERT-RESOURCE-PROBABILITIES"
	   ;; Couplling to the AWDRAT GUI
	   "RUN-EDITOR" 
	   )
  (:USE COMMON-LISP JOSHUA))



