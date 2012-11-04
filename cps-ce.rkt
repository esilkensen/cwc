#lang racket

;; This file defines the CE-machine for CPS.

(require redex "cs.rkt" "cps.rkt")

(provide eval-n CPS+E cps-ce)

;; Semantics:
(define-metafunction CPS
  eval-n : W -> c
  [(eval-n (λ (k) P))
   ,(let ([S (term (P ((k (cl x (k x) ((k stop)))))))])
      (define results (apply-reduction-relation* cps-ce S))
      (define match-reduction-result
        (term-match/single CPS+E [((k x) ((k stop) (x c))) (term c)]))
      (unless (= (length results) 1)
        (error 'eval-d "term ~s had multiple reductions: ~s" (term P) results))
      (match-reduction-result (car results)))])

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
   [--> ((k W) E)
        (P (extend E_2 (x) (W*)))
        (where ((cl x P E_2) W*)
               ((lookup E k) (μ W E)))
        "ce1"]
   [--> ((let (x W) P) E)
        (P (extend E (x) (W*)))
        (where W* (μ W E))
        "ce2"]
   [--> ((if0 W P_1 P_2) E)
        ,(if (eq? (term W*) 0)
             (term (P_1 E))
             (term (P_2 E)))
        (where W* (μ W E))
        "ce3"]
   [--> ((W k W_1 ...) E)
        (P_1 (extend E_1 (k_1 x_1 ...) (W* W*_1 ...)))
        (where ((cl (k_1 x_1 ...) P_1 E_1) W* W*_1 ...)
               ((μ W E) (lookup E k) (μ W_1 E) ...))
        "ce4"]
   [--> ((W (λ (x) P) W_1 ...) E)
        (P_1 (extend E_1 (k_1 x_1 ...) ((cl x P E) W*_1 ...)))
        (where ((cl (k_1 x_1 ...) P_1 E_1) W*_1 ...)
               ((μ W E) (μ W_1 E) ...))
        "ce5"]
   [--> ((O k W_1 ...) E)
        (P_1 (extend E_1 (x) ((δ O (W*_1 ...)))))
        (where ((cl x P_1 E_1) W*_1 ...)
               ((lookup E k) (μ W_1 E) ...))
        "ce6"]
   [--> ((O (λ (x) P) W_1 ...) E)
        (P (extend E (x) ((δ O (W*_1 ...)))))
        (where (W*_1 ...) ((μ W_1 E) ...))
        "ce7"]))

;; Converting values to machine values:
(define-metafunction CPS+E
  μ : W E -> W* or #f
  [(μ c E) c]
  [(μ x E) (lookup E x)]
  [(μ (λ (k x ...) P) E) (cl (k x ...) P E)])

;; -----------------------------------------------------------------------------

(module+ test
  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))
  
  (test-equal (term (eval-n (cps ,p1))) 6)
  (test-equal (term (eval-n (cps ,p2))) 1)
  (test-equal (term (eval-n (cps ,p3))) 118))