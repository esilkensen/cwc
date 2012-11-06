#lang racket

;; This file defines the CEK-machine for A.

(require redex/reduction-semantics "cs.rkt" "cs-cek.rkt" "anf.rkt")

(provide eval-a A+EK ->a-cek)

;; Semantics:
(define-metafunction A
  eval-a : M -> c
  [(eval-a M)
   (result ,(apply-reduction-relation*
             ->a-cek (term (M () (ar x x () stop)))))])

(define-metafunction A
  result : [(x ((x c)) stop)] -> c
  [(result ((x ((x c)) stop))) c])

;; Data Specifications:
(define-extended-language A+EK A
  (S (M E K))
  (E ((x V*) ...))
  (V* c (cl (x ...) M E))
  (K stop (ar x M E K)))

;; Transition Rules:
(define ->a-cek
  (reduction-relation
   A+EK
   #:domain S
   [--> (V E K)
        (M (extend E_1 (x) ((γ V E))) K_1)
        (where (ar x M E_1 K_1) K)
        "cek1"]
   [--> ((let (x V) M) E K)
        (M (extend E (x) ((γ V E))) K)
        "cek2"]
   [--> ((if0 V M_1 M_2) E K)
        ,(if (eq? (term (γ V E)) 0)
             (term (M_1 E K))
             (term (M_2 E K)))
        "cek3"]
   [--> ((V V_1 ...) E K)
        (M (extend E_1 (x ...) ((γ V_1 E) ...)) K)
        (where (cl (x ...) M E_1) (γ V E))
        "cek4"]
   [--> ((let (x (V V_1 ...)) M) E K)
        (M_1 (extend E_1 (x_1 ...) ((γ V_1 E) ...)) (ar x M E K))
        (where (cl (x_1 ...) M_1 E_1) (γ V E))
        "cek5"]
   [--> ((O V_1 ...) E K)
        (M_1 (extend E_1 (x) ((δ O ((γ V_1 E) ...)))) K_1)
        (where (ar x M_1 E_1 K_1) K)
        "cek6"]
   [--> ((let (x (O V_1 ...)) M) E K)
        (M (extend E (x) ((δ O ((γ V_1 E) ...)))) K)
        "cek7"]))

;; -----------------------------------------------------------------------------

(module+ test
  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))
  
  (test-equal (term (eval-a (cs->anf ,p1))) 6)
  (test-equal (term (eval-a (cs->anf ,p2))) 1)
  (test-equal (term (eval-a (cs->anf ,p3))) 118))