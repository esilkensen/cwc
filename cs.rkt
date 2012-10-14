#lang racket

;; This file defines the abstract syntax of Core Scheme (CS) and utility
;; metafunctions for operating on its terms.

(require redex)

(provide CS δ extend lookup subst)

(define-language CS
  (M V
     (let (x M) M)
     (if0 M M M)
     (M M ...)
     (O M ...))
  (V c x (λ (x ...) M))
  (c number)
  (O + - * /)
  ((x k) variable-not-otherwise-mentioned))

;; Evaluating primitive operations:
(define-metafunction CS
  δ : O (number ...) -> number
  [(δ + (number ...)) ,(apply + (term (number ...)))]
  [(δ - (number ...)) ,(apply - (term (number ...)))]
  [(δ * (number ...)) ,(apply * (term (number ...)))]
  [(δ / (number ...)) ,(apply / (term (number ...)))])

;; Extending environments:
(define-metafunction CS
  extend : ((x any) ...) (x ...) (any ...) -> ((x any) ...)
  [(extend ((x_1 any_1) ...) (x ..._n) (any ..._n))
   ((x_1 any_1) ... (x any) ...)])

;; Looking up bindings in environments:
(define-metafunction CS
  lookup : ((x any) ...) x -> any
  [(lookup ((x_1 any_1) ... (x any) (x_2 any_2) ...) x) any
   (side-condition (not (member (term x) (term (x_2 ...)))))])
   
;; Capture-avoiding substitution:
(define-metafunction CS
  [(subst (λ (x_1) any_1) x_1 any_2)
   (λ (x_1) any_1)]
  [(subst (λ (x_1) any_1) x_2 any_2)
   (λ (x_3)
     (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2))
                                (term x_1)))]
  [(subst (let (x_1 any_1) any_2) x_1 any_3)
   (let (x_1 (subst any_1 x_2 any_3)) any_2)]
  [(subst (let (x_1 any_1) any_2) x_2 any_3)
   (let (x_3 (subst any_1 x_2 any_3))
     (subst (subst-var any_2 x_1 x_3) x_2 any_3))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2 any_3))
                                (term x_1)))]
  [(subst x_1 x_1 any_1) any_1]
  [(subst (any_2 ...) x_1 any_1)
   ((subst any_2 x_1 any_1) ...)]
  [(subst any_2 x_1 any_1) any_2])

(define-metafunction CS
  [(subst-var (any_1 ...) variable_1 variable_2)
   ((subst-var any_1 variable_1 variable_2) ...)]
  [(subst-var variable_1 variable_1 variable_2) variable_2]
  [(subst-var any_1 variable_1 variable_2) any_1])
