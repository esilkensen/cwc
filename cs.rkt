#lang racket

;; This file defines the abstract syntax of Core Scheme (CS) and a
;; capture-avoiding substitution function.

(require redex)

(provide CS subst)

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
