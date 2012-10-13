#lang racket

;; This file defines the CEK-machine for Core Scheme.

(require redex "cs.rkt")

(provide eval-d CS+EK CEK)

;; Semantics:
(define (eval-d M)
  (define results
    (apply-reduction-relation* CEK (term (,M () stop))))
  (define match-reduction-result
    (term-match/single CS+EK [(stop c) (term c)]))
  (unless (= (length results) 1)
    (error 'eval-d "term ~s had multiple reductions: ~s" (term M) results))
  (match-reduction-result (car results)))

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
(define CEK
  (reduction-relation
   CS+EK
   #:domain S
   [--> (V E K)
        (K (γ V E))]
   [--> ((let (x M_1) M_2) E K)
        (M_1 E (lt x M_2 E K))]
   [--> ((if0 M_1 M_2 M_3) E K)
        (M_1 E (if M_2 M_3 E K))]
   [--> ((M M_1 ...) E K)
        (M E (ap () (M_1 ...) E K))]
   [--> ((O M_1 M_2 ...) E K)
        (M_1 E (pr O () (M_2 ...) E K))]
   
   [--> ((lt x M ((x_1 V*_1) ...) K) V*)
        (M ((x_1 V*_1) ... (x V*)) K)]
   [--> ((if M_1 M_2 E K) 0)
        (M_1 E K)]
   [--> ((if M_1 M_2 E K) V*)
        (M_2 E K)
        (side-condition (not (eq? 0 (term V*))))]
   [--> ((ap (V* ...) (M M_1 ...) E K) V*_1)
        (M E (ap (V* ... V*_1) (M_1 ...) E K))]
   [--> ((ap ((cl (x_1 ...) M_1 E_1) V*_1 ...) () E K) V*_n)
        (M_1 (extend E_1 (x_1 ...) (V*_1 ... V*_n)) K)]
   [--> ((pr O (V* ...) (M M_1 ...) E K) V*_1)
        (M E (pr O (V* ... V*_1) (M_1 ...) E K))]
   [--> ((pr O (V* ...) () E K) V*_n)
        (K (δ O (V* ... V*_n)))]))

;; Converting syntactic values to machine values:
(define-metafunction CS+EK
  γ : V E -> V*
  [(γ c E) c]
  [(γ x ((x_1 V*_1) ... (x V*) (x_2 V*_2) ...)) V*
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(γ (λ (x ...) M) E) (cl (x ...) M E)])

;; Evaluating primitive operations:
(define-metafunction CS+EK
  δ : O (V* ...) -> V*
  [(δ + (number ...)) ,(apply + (term (number ...)))]
  [(δ - (number ...)) ,(apply - (term (number ...)))]
  [(δ * (number ...)) ,(apply * (term (number ...)))]
  [(δ / (number ...)) ,(apply / (term (number ...)))])

;; Extending environments:
(define-metafunction CS+EK
  extend : E (x ...) (V* ...) -> E
  [(extend ((x_1 V*_1) ...) (x ..._n) (V* ..._n))
   ((x_1 V*_1) ... (x V*) ...)])

;; -----------------------------------------------------------------------------

(module+ test
  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))

  (test-equal (eval-d p1) 6)
  (test-equal (eval-d p2) 1)
  (test-equal (eval-d p3) 118)

  (test-equal (eval-d p1) (eval-d (term ((F ,p1) (λ (x) x)))))
  (test-equal (eval-d p2) (eval-d (term ((F ,p2) (λ (x) x)))))
  (test-equal (eval-d p3) (eval-d (term ((F ,p3) (λ (x) x))))))
