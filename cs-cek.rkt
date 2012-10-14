#lang racket

;; This file defines the CEK-machine for CS.

(require redex "cs.rkt")

(provide eval-d CS+EK cs-cek)

;; Semantics:
(define-metafunction CS
  eval-d : M -> c
  [(eval-d M)
   ,(let ([S (term (M () stop))])
      (define results (apply-reduction-relation* cs-cek S))
      (define match-reduction-result
        (term-match/single CS+EK [(stop c) (term c)]))
      (unless (= (length results) 1)
        (error 'eval-d "term ~s had multiple reductions: ~s" (term M) results))
      (match-reduction-result (car results)))])

;; Data Specifications:
(define-extended-language CS+EK CS
  (S (M E K) (K V*))
  (E ((x V*) ...))
  (V* c (cl (x ...) M E))
  (K stop 
     (ap (V* ...) (M ...) E K)
     (lt x M E K)
     (if M M E K)
     (pr O (V* ...) (M ...) E K)))

;; Transition Rules:
(define cs-cek
  (reduction-relation
   CS+EK
   #:domain S
   [--> (V E K)
        (K (γ V E))
        "cek1"]
   [--> ((let (x M_1) M_2) E K)
        (M_1 E (lt x M_2 E K))
        "cek2"]
   [--> ((if0 M_1 M_2 M_3) E K)
        (M_1 E (if M_2 M_3 E K))
        "cek3"]
   [--> ((M M_1 ...) E K)
        (M E (ap () (M_1 ...) E K))
        "cek4"]
   [--> ((O M_1 M_2 ...) E K)
        (M_1 E (pr O () (M_2 ...) E K))
        "cek5"]
   
   [--> ((lt x M ((x_1 V*_1) ...) K) V*)
        (M ((x_1 V*_1) ... (x V*)) K)
        "cek6"]
   [--> ((if M_1 M_2 E K) 0)
        (M_1 E K)
        "cek7"]
   [--> ((if M_1 M_2 E K) V*)
        (M_2 E K)
        (side-condition (not (eq? 0 (term V*))))
        "cek8"]
   [--> ((ap (V* ...) (M M_1 ...) E K) V*_1)
        (M E (ap (V* ... V*_1) (M_1 ...) E K))]
   [--> ((ap ((cl (x_1 ...) M_1 E_1) V*_1 ...) () E K) V*_n)
        (M_1 (extend E_1 (x_1 ...) (V*_1 ... V*_n)) K)
        "cek9"]
   [--> ((pr O (V* ...) (M M_1 ...) E K) V*_1)
        (M E (pr O (V* ... V*_1) (M_1 ...) E K))
        "cek10"]
   [--> ((pr O (V* ...) () E K) V*_n)
        (K (δ O (V* ... V*_n)))
        "cek11"]))

;; Converting syntactic values to machine values:
(define-metafunction CS+EK
  γ : V E -> V*
  [(γ c E) c]
  [(γ x E) (lookup E x)]
  [(γ (λ (x ...) M) E) (cl (x ...) M E)])

;; -----------------------------------------------------------------------------

(module+ test
  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))

  (test-equal (term (eval-d ,p1)) 6)
  (test-equal (term (eval-d ,p2)) 1)
  (test-equal (term (eval-d ,p3)) 118))
