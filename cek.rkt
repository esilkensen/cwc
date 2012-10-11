#lang racket

(require redex)

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

(define-extended-language CS+EK CS
  (E ((x V*) ...))
  (V* c (cl (x ...) M E))
  (K stop 
     (ap (V* ...) (M ...) E K)
     (lt x M E K)
     (if M M E K)
     (pr O (V* ...) (M ...) E K)))

;; -----------------------------------------------------------------------------

(define CEK
  (reduction-relation
   CS+EK
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
   [--> ((ap ((cl (x_1 ...) M_1 E_1) V_1* ...) () E K) V*_n)
        (M_1 (extend E_1 (x_1 ...) (V_1* ... V*_n)) K)]
   [--> ((pr O (V* ...) (M M_1 ...) E K) V*_1)
        (M E (pr O (V* ... V*_1) (M_1 ...) E K))]
   [--> ((pr O (V* ...) () E K) V*_n)
        (K (δ O (V* ... V*_n)))]))

(define-metafunction CS+EK
  γ : V E -> V*
  [(γ c E) c]
  [(γ x ((x_1 V*_1) ... (x V*) (x_2 V*_2) ...)) V*]
  [(γ (λ (x ...) M) E) (cl (x ...) M E)])

(define-metafunction CS+EK
  δ : O (V* ...) -> V*
  [(δ + (number ...)) ,(apply + (term (number ...)))]
  [(δ - (number ...)) ,(apply - (term (number ...)))]
  [(δ * (number ...)) ,(apply * (term (number ...)))]
  [(δ / (number ...)) ,(apply / (term (number ...)))])

(define-metafunction CS+EK
  extend : E (x ...) (V* ...) -> E
  [(extend ((x_1 V*_1) ...) (x ..._n) (V* ..._n))
   ((x_1 V*_1) ... (x V*) ...)])

;; =============================================================================

(define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
(define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
(define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))

(test-->> CEK (term (,p1 () stop)) (term (stop 6)))
(test-->> CEK (term (,p2 () stop)) (term (stop 1)))
(test-->> CEK (term (,p3 () stop)) (term (stop 118)))
