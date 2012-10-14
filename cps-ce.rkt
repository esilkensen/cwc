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
   [--> ((k W) E_1)
        (P (extend E_2 (x) ((μ W E_1))))
        (where (cl x P E_2) (lookup E_1 k))
        "ce1"]
   [--> ((let (x W) P) E)
        (P (extend E (x) ((μ W E))))
        "ce2"]
   [--> ((if0 W P_1 P_2) E)
        ,(if (eq? (term (μ W E)) 0)
             (term ((P_1 E)))
             (term ((P_2 E))))
        "ce3"]
   [--> ((W k W_1 ...) E)
        (P_1 (extend E_1 (k_1 x_1 ...) ((lookup E k) (μ W_1 E) ...)))
        (where (cl (k_1 x_1 ...) P_1 E_1) (μ W E))
        "ce4"]
   [--> ((W (λ (x) P) W_1 ...) E)
        (P_1 (extend E_1 (k_1 x_1 ...) ((cl x P E) (μ W_1 E) ...)))
        (where (cl (k_1 x_1 ...) P_1 E_1) (μ W E))
        "ce5"]
   [--> ((O k W_1 ...) E)
        (P_1 (extend E_1 (x) ((δ O (μ W_1 E) ...))))
        (where (cl x P_1 E_1) (lookup E k))
        "ce6"]
   [--> ((O (λ (x) P) W_1 ...) E)
        (P (extend E (x) ((δ O (μ W_1 E) ...))))
        "ce7"]))

;; Converting values to machine values:
(define-metafunction CPS+E
  μ : W E -> W*
  [(μ c E) c]
  [(μ x E) (lookup E x)]
  [(μ (λ (k x ...) P) E) (cl (k x ...) P E)])
