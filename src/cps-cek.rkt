#lang racket

;; This file defines the CEK-machine for CPS.

(require redex/reduction-semantics "cs.rkt" "cps.rkt")

(provide eval-c CPS+EK ->cps-cek)

;; Semantics:
(define-metafunction CPS
  eval-c : W -> c
  [(eval-c (λ (k) P))
   (result ,(apply-reduction-relation*
             ->cps-cek (term (P () (ar x (k x) () stop)))))])

(define-metafunction CPS
  result : [((k x) ((x c)) stop)] -> c
  [(result (((k x) ((x c)) stop))) c])

;; Data Specifications:
(define-extended-language CPS+EK CPS
  (S (P E K))
  (E ((x W*) ...))
  (W* c (cl (k x ...) P E))
  (K stop (ar x P E K)))

;; Transition Rules:
(define ->cps-cek
  (reduction-relation
   CPS+EK
   #:domain S
   [--> ((k W) E (ar x P E_1 K_1))
        (P (extend E_1 (x) ((μ W E))) K_1)
        "cek1"]
   [--> ((let (x W) P) E K)
        (P (extend E (x) ((μ W E))) K)
        "cek2"]
   [--> ((if0 W P_1 P_2) E K)
        ,(if (eq? (term (μ W E)) 0)
             (term (P_1 E K))
             (term (P_2 E K)))
        "cek3"]
   [--> ((W k W_1 ...) E K)
        (P (extend E_1 (x_1 ...) ((μ W_1 E) ...)) K)
        (where (cl (k_1 x_1 ...) P E_1) (μ W E))
        "cek4"]
   [--> ((W (λ (x) P) W_1 ...) E K)
        (P_1 (extend E_1 (x_1 ...) ((μ W_1 E) ...)) (ar x P E K))
        (where (cl (k_1 x_1 ...) P_1 E_1) (μ W E))
        "cek5"]
   [--> ((O k W_1 ...) E (ar x P_1 E_1 K_1))
        (P_1 (extend E_1 (x) ((δ O ((μ W_1 E) ...)))) K_1)
        "cek6"]
   [--> ((O (λ (x) P) W_1 ...) E K)
        (P (extend E (x) ((δ O ((μ W_1 E) ...)))) K)
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