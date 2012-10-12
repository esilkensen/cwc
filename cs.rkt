#lang racket

;; This file defines the abstract syntax of Core Scheme (CS).

(require redex)

(provide CS)

(define-language CS
  (M V
     (let (x M) M)
     (if0 M M M)
     (M M ...)
     (O M ...))
  (V c x (λ (x ...) M))
  (c number)
  (O + - * /)
  (x variable-not-otherwise-mentioned))
