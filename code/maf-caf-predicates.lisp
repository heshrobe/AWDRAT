;;; -*- Mode: LISP; Syntax: Joshua; Package: awdrat ; readtable: joshua -*-

(in-package :awdrat)

(define-predicate image-quality (image-type image-quality))
(define-predicate image-type-consistent-with-method (image-type method))
(define-predicate image-loaded (image file))
(define-predicate image-file-exists (path type image-file))

(define-predicate well-formed (thing type situation) (modeling-mixin))
(define-predicate executed-in-protected-memory (component situation) (modeling-mixin))

(define-predicate code-file-exists (pathname) (modeling-mixin))


;;; DSCS = data structure consistency status
(define-predicate dscs (thing type value situation) (modeling-mixin))
;;; Predicates related to data access during a program module's execution
(define-predicate data-written (data-category interval) (modeling-mixin))
(define-predicate data-read (data-category interval) (modeling-mixin))
(define-predicate data-transmitted (data-category interval) (modeling-mixin))