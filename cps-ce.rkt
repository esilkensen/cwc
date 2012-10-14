#lang racket

;; This file defines the CE-machine for CPS.

(require redex "cps.rkt")

(provide eval-n CPS+E cps-ce)

;; Semantics:
(define (eval-n P)
  (define results
    (let ([S (term (,P ((k stop) (k (cl x (k x))))))])
      (apply-reduction-relation* cps-ce S)))
  (define match-reduction-result
    (term-match/single CPS+E [((k x) ((x c) (k stop))) (term c)]))
  (unless (= (length results) 1)
    (error 'eval-d "term ~s had multiple reductions: ~s" (term P) results))
  (match-reduction-result (car results)))

;; Data Specifications:
(define-extended-language CPS+E CPS
  (S (P E))
  (E ((x W*) ...))
  (W* c (cl (k x ...) P E) (cl x P E) stop))

;; Transition Rules:
(define cps-ce
  (reduction-relation
   CPS+E
   #:domain S
   [--> S S "cek1"]
   [--> S S "cek2"]
   [--> S S "cek3"]
   [--> S S "cek4"]
   [--> S S "cek5"]
   [--> S S "cek6"]
   [--> S S "cek7"]))

;; Converting values to machine values:
(define-metafunction CPS+E
  μ : W E -> W*
  [(μ c E) c]
  [(μ x ((x_1 W*_1) ... (x W*) (x_2 W*_2) ...)) W*
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(μ (λ (k x ...) P) E) (cl (k x ...) P E)])
