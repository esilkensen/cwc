#lang racket

;; This file defines the abstract syntax of Core Scheme (CS) in A-normal form
;; (A) and a transformation from Continuation-Passing Style (CPS) to A.

(require redex "cps.rkt")

(provide A anf (all-from-out "cps.rkt"))

;; The language A(CS):
(define-extended-language A CPS
  (M V
     (let (x V) M)
     (if0 V M M)
     (V V_1 ...)
     (let (x (V V ...)) M)
     (O V_1 ...)
     (let (x (O V ...)) M))
  (V c x (λ (x ...) M)))

;; Transforming a CPS term to A-normal form:
(define-metafunction A
  anf : W -> M
  [(anf (λ (k) P)) (λ (k) (U P))])

;; The inverse CPS transformation (U):
(define-metafunction A
  U : P -> M
  [(U (k W)) (Ψ W)]
  [(U (let (x W) P)) (let (x (Ψ W)) (U P))]
  [(U (if0 W P_1 P_2)) (if0 (Ψ W) (U P_1) (U P_2))]
  [(U (W k W_1 ...)) ((Ψ W) (Ψ W_1) ...)]
  [(U (W (λ (x) P) W_1 ...)) (let (x ((Ψ W) (Ψ W_1) ...)) (U P))]
  [(U (O k W ...)) (O (Ψ W) ...)]
  [(U (O (λ (x) P) W ...)) (let (x (O (Ψ W) ...)) (U P))])

(define-metafunction A
  Ψ : W -> W
  [(Ψ c) c]
  [(Ψ x) x]
  [(Ψ (λ (k x ...) P)) (λ (x ...) (U M))])
