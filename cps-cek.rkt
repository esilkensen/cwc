#lang racket

;; This file defines the CEK-machine for CPS.

(require redex "cs.rkt" "cps.rkt")

(provide eval-c CPS+EK cps-cek)

;; Semantics:
(define-metafunction CPS
  eval-c : W -> c
  [(eval-c (λ (k) P))
   ,(let ([S (term (P () (ar x (k x) () stop)))])
      (define results (apply-reduction-relation* cps-cek S))
      (define match-reduction-result
        (term-match/single CPS+EK [((k x) ((x c)) stop) (term c)]))
      (unless (= (length results) 1)
        (error 'eval-d "term ~s had multiple reductions: ~s" (term P) results))
      (match-reduction-result (car results)))])

;; Data Specifications:
(define-extended-language CPS+EK CPS
  (S (P E K))
  (E ((x W*) ...))
  (W* c (cl (k x ...) P E))
  (K stop (ar x P E K)))

;; Transition Rules:
(define cps-cek
  (reduction-relation
   CPS+EK
   #:domain S
   [--> ((k W) E (ar x P E_1 K_1))
        (P (extend E_1 (x) (W*)) K_1)
        (where W* (μ W E))
        "cek1"]
   [--> ((let (x W) P) E K)
        (P (extend E (x) (W*)) K)
        (where W* (μ W E))
        "cek2"]
   [--> ((if0 W P_1 P_2) E K)
        ,(if (eq? (term W*) 0)
             (term (P_1 E K))
             (term (P_2 E K)))
        (where W* (μ W E))
        "cek3"]
   [--> ((W k W_1 ...) E K)
        (P (extend E_1 (x_1 ...) (W*_1 ...)) K)
        (where ((cl (k_1 x_1 ...) P E_1) W*_1 ...)
               ((μ W E) (μ W_1 E) ...))
        "cek4"]
   [--> ((W (λ (x) P) W_1 ...) E K)
        (P_1 (extend E_1 (x_1 ...) (W*_1 ...)) (ar x P E K))
        (where ((cl (k_1 x_1 ...) P_1 E_1) W*_1 ...)
               ((μ W E) (μ W_1 E) ...))
        "cek5"]
   [--> ((O k W_1 ...) E (ar x P_1 E_1 K_1))
        (P_1 (extend E_1 (x) ((δ O (W*_1 ...)))) K_1)
        (where (W*_1 ...) ((μ W_1 E) ...))
        "cek6"]
   [--> ((O (λ (x) P) W_1 ...) E K)
        (P (extend E (x) ((δ O (W*_1 ...)))) K)
        (where (W*_1 ...) ((μ W_1 E) ...))
        "cek7"]))

;; Converting values to machine values:
(define-metafunction CPS+EK
  μ : W E -> W* or #f
  [(μ c E) c]
  [(μ x E) (lookup E x)]
  [(μ (λ (k x ...) P) E) (cl (k x ...) P E)])

;; -----------------------------------------------------------------------------

(module+ test
  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))

  (test-equal (term (eval-c (cps ,p1))) 6)
  (test-equal (term (eval-c (cps ,p2))) 1)
  (test-equal (term (eval-c (cps ,p3))) 118))
