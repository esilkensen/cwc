#lang racket

;; This file defines the abstract syntax of Core Scheme (CS) in A-normal form
;; (A) and transformations from CS to Continuation-Passing Style (CPS) to A and
;; also from CS to A, directly.

(require redex/reduction-semantics "cs.rkt" "cps.rkt")

(provide A cs->cps->anf cs->anf)

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

;; Transforming a CS term to CPS and then to A-normal form:
(define-metafunction CS
  [(cs->cps->anf M) (anf (cps M))])

;; Transforming a CPS term to A-normal form:
(define-metafunction A
  anf : W -> M
  [(anf (λ (k) P)) (U P)])

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
  [(Ψ (λ (k x ...) P)) (λ (x ...) (U P))])

;; Evaluation Contexts:
(define-extended-language CS+E CS
  (E hole (let (x E) M) (if0 E M M) (F V ... E M ...))
  (F O V))

;; The A-reductions:
(define ->A
  (reduction-relation
   CS+E
   [--> (in-hole E (let (x_1 M_1) M_2))
        (let (x_2 M_1) (cs->anf (in-hole E (subst M_2 x_1 x_2))))
        (where x_2 ,(variable-not-in (term E) (term x_1)))
        (side-condition (term (not-hole E)))
        "A1"]
   [--> (in-hole E (if0 V M_1 M_2))
        (if0 V (cs->anf (in-hole E M_1)) (cs->anf (in-hole E M_2)))
        (side-condition (term (not-hole E)))
        "A2"]
   [--> (in-hole E (F V ...))
        (let (x (F V ...)) (cs->anf (in-hole E x)))
        (where x ,(variable-not-in (term E) (term t1)))
        (side-condition
         (and (term (not-hole E))
              (term (not-let-hole E))))
        "A3"]
   [--> (let (x V) M)
        (let (x V) (cs->anf M))
        (side-condition (term (not-anf M)))]
   [--> (if0 V M_1 M_2)
        (if0 V (cs->anf M_1) (cs->anf M_2))
        (side-condition (or (term (not-anf M_1)) (term (not-anf M_2))))]))

;; Transforming a CS term to A-normal form:
(define-metafunction CS+E
  [(cs->anf M_1)
   (assert M_2)
   (where (M_2) ,(apply-reduction-relation* ->A (term M_1)))])

;; Assert that a term is in A-normal form:
(define-metafunction A
  [(assert M) M])

(define-metafunction A
  [(not-anf M) #f]
  [(not-anf any) #t])

(define-metafunction CS+E
  not-hole : E -> #t or #f
  [(not-hole hole) #f]
  [(not-hole E) #t])

(define-metafunction CS+E
  not-let-hole : E -> #t or #f
  [(not-let-hole (in-hole E (let (x hole) M))) #f]
  [(not-let-hole E) #t])

;; -----------------------------------------------------------------------------

(module+ test
  (require "cs-cek.rkt")

  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))
  (define p4 (term (+ 1 (let (x (+ 1 1)) (- x x)))))

  (for ([p (list p1 p2 p3)])
    (define a1 (term (cs->cps->anf ,p)))
    (define a2 (term (cs->anf ,p)))
    (test-equal (term (eval-d ,p)) (term (eval-d ,a1)))
    (test-equal (term (eval-d ,p)) (term (eval-d ,a2)))
    (test-equal (term (=α ,a1 ,a2)) #t)))
