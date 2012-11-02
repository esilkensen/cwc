#lang racket

;; This file defines the abstract syntax of Core Scheme (CS) in A-normal form
;; (A) and a transformation from Continuation-Passing Style (CPS) to A.

(require redex "cps.rkt")

(provide A anf (all-from-out "cps.rkt"))

;; The language A(CS):
(define-extended-language A CPS
  (N V
     M
     (let (x V) N)
     (if0 V N N)
     (V V_1 ...)
     (let (x (V V ...)) N)
     (O V_1 ...)
     (let (x (O V ...)) N))
  (V c x (λ (x ...) N))
  (c number)
  (O +)
  (ε hole
     (let (x ε) M)
     (let (x V) ε)
     (if0 ε M M)
     (O V ... ε M ...)
     (V V ... ε M ...)))

;; Transforming a CPS term to A-normal form:
(define-metafunction A
  anf : W -> N
  [(anf (λ (k) P)) (λ (k) (U P))])

;; The inverse CPS transformation (U):
(define-metafunction A
  U : P -> N
  [(U (k W)) (Ψ W)]
  [(U (let (x W) P)) (let (x (Ψ W)) (U P))]
  [(U (if0 W P_1 P_2)) (if0 (Ψ W) (U P_1) (U P_2))]
  [(U (W k W_1 ...)) ((Ψ W) (Ψ W_1) ...)]
  [(U (W (λ (x) P) W_1 ...)) (let (x ((Ψ W) (Ψ W_1) ...)) (U P))]
  [(U (O k W ...)) (O (Ψ W) ...)]
  [(U (O (λ (x) P) W ...)) (let (x (O (Ψ W) ...)) (U P))])

;; Transform CPS values to ANF values
(define-metafunction A
  Ψ : W -> W
  [(Ψ c) c]
  [(Ψ x) x]
  [(Ψ (λ (k x ...) P)) (λ (x ...) (U P))])

(define-metafunction A
  a-trans : M ε -> N

  ;; Var
  [(a-trans x ε) (in-hole ε x)]
  ;; A2
  [(a-trans (if0 V M_1 M_2) ε)
   (if0 V (a-trans (in-hole ε M_1) hole) (a-trans (in-hole ε M_2) hole))
   (side-condition (term (empty-context? ε)))]

  [(a-trans (if0 M_0 M_1 M_2) ε)
   (a-trans M_0 (in-hole ε (if0 hole M_1 M_2)))]

  ;; A3 V
  [(a-trans (V V_arg ...) ε)
   (let (x_new (V V_arg ...)) (a-trans (in-hole ε x_new) hole))
   (where x_new ,(variable-not-in (term ε) 'x))
   (side-condition (and
                     (not (term (empty-context? ε)))
                      (not (term (let-context? ε)))
                      (not (term (fv-ε? x_new ε)))))]
  [(a-trans (V V_arg ... M_0 M_rest ...) ε)
   (a-trans M_0 (in-hole ε (V V_arg ... hole M_rest ...)))]

  ;; A3 O
  [(a-trans (O V_arg ...) ε)
   (let (x_new (O V_arg ...)) (a-trans (in-hole ε x_new) hole))
   (where x_new ,(variable-not-in (term ε) 'x))
   (side-condition
     (and (not (term (empty-context? ε)))
          (not (term (let-context? ε)))
          (not (term (fv-ε? x_new ε)))))]

  [(a-trans (O V ... M_0) ε)
   (a-trans M_0 (in-hole ε (O V ... hole)))]
  [(a-trans (O V ... M_0 M_rest ...) ε)
   (a-trans M_0 (in-hole ε (O V ... hole M_rest ...)))]

  ;; A1
  ;; skip over A-bind
  [(a-trans (let (x V) M) ε)
   (a-trans M (in-hole ε (let (x V) hole)))]
  ;; skip over A-bind-prim-op
  [(a-trans (let (x (O V ...)) M) ε)
   (a-trans M (in-hole ε (let (x (O V ...)) hole)))]
  ;; skip over A-bind-call
  [(a-trans (let (x (V V_arg ...)) M) ε)
   (a-trans M (in-hole ε (let (x (V V_arg ...)) hole)))]

  ;; a-trans right-hand-side of bind
  [(a-trans (let (x M_0) M_1) ε)
   (a-trans M_0 (in-hole ε (let (x hole) M_1)))])

;; Let shaped context
(define-metafunction A
  let-context? : ε -> #t or #f
  [(let-context? (let (x ε) M)) #t]
  [(let-context? ε) #f])

;; Is ε an empty context?
(define-metafunction A
  empty-context? : ε -> #t or #f
  [(empty-context? hole) #t]
  [(empty-context? ε) #f])

;; Is x a free variable in context ε?
(define-metafunction A
  fv-ε? : x ε -> #t or #f
  [(fv-ε? x hole) #t]
  [(fv-ε? x (let (x ε) M)) #f]
  [(fv-ε? x (let (x_1 ε) M))
   ,(and (term (fv-ε? x ε))
         (term (fv? x M)))]
  [(fv-ε? x (if0 ε M_l M_r))
   ,(and (term (fv-ε? x ε))
         (term (fv? x M_l))
         (term (fv? x M_r)))]

  [(fv-ε? x (let (x V) ε)) #f]
  [(fv-ε? x (let (x_1 V) ε))
   ,(andmap identity
            (flatten
             `(,(term (fv-ε? x ε))
               ,(term (fv? x V)))))]

  [(fv-ε? x (O V ... ε M ...))
   ,(andmap identity
            (flatten
             `(,(term (fv-ε? x ε))
               ,(term ((fv? x V) ...))
               ,(term ((fv? x M) ...)))))]
  [(fv-ε? x (V V_arg ... ε M ...))
   ,(andmap identity
            (flatten
              `(,(term (fv-ε? x ε))
                ,(term (fv? x V))
                ,(term (fv? x V_arg ...))
                ,(term (fv? x M ...)))))])

;; Is x a free variable in M?
(define-metafunction A
  fv? : x M -> #t or #f
  [(fv? x (let (x V) M)) #f]
  [(fv? x (let (x_1 V) M))
   ,(and (term (fv? x V))
         (term (fv? x M)))]
  [(fv? x (if0 V M_l M_r))
   ,(and (term (fv? x V))
         (term (fv? x M_l))
         (term (fv? x M_r)))]

  ;; λ applications
  [(fv? x (V V_1 ...))
   ,(and (term (fv? x V))
         (andmap (λ (v) (term (fv? x v))) (term (V_1 ...))))]
  [(fv? x (let (x (V V_1 ...)) M)) #f]
  [(fv? x (let (y (V V_1 ...)) M))
   ,(and (term (fv? x V))
         (term (fv? x M))
         (andmap (λ (x) x)
                 (term (fv? x V_1 ...))))]

  ;; operation applications
  [(fv? x (O M_1 ...)) ,(andmap identity (term ((fv? x M_1) ...)))]
  [(fv? x (let (x (O V ...)) M)) #f]
  [(fv? x (let (y (O V ...)) M))
   ,(and (term (fv? x M))
         (andmap (λ (x) x)
                 (term (fv? x V ...))))]

  ;; Values
  [(fv? x x) #t]
  [(fv? x x_1) #f]
  [(fv? x c) #f]
  [(fv? x (λ (x_l ... x x_r ...) M)) #f]
  [(fv? x (λ (x_arg ...) M)) (fv? x M)])

;; Test fv?
(define e1 (term (let (x 1) x)))
(define e2 (term ((λ (x y) x) 1 2)))
(define e3 (term (let (z 1) (((λ (x y) z) 1) 2))))
(define e4 (term (+ (+ 2 2) (let (x (1)) (+ x 1)))))
(define e5 (term (+ (+ 2 2) 3)))
(define e6 (term (+ (+ 2 2) (let (x 1) (+ x 9)))))

(test-equal (term (fv? x ,e1)) #f)
(test-equal (term (fv? x ,e2)) #f)
(test-equal (term (fv? z ,e2)) #f)
(test-equal (term (fv? x ,e5)) #f)
(test-equal (term (fv? z 3)) #f)

(define E0 (term hole))
(define E1 (term (let (x hole) x)))
(define E2 (term (if0 ,E1 ,e1 ,e2)))

(test-equal (term (empty-context? ,E0)) #t)
(test-equal (term (empty-context? ,E2)) #f)

;; Test fv-ε?
(test-equal (term (fv-ε? x ,E1)) #f)
(test-equal (term (fv-ε? x ,E2)) #f)
(test-equal (term (fv-ε? y ,E2)) #f)
(test-equal (term (fv-ε? z ,E2)) #f)

;; In CS language
(for/and ((an-s (list e1 e2 e3 e4 e5)))
  (redex-match? A M an-s))

;; In A Language
(for/and ((an-s (list e1 e2 e3 e4 e5)))
  (redex-match? A N an-s))

;; Closer, but still not right.
(term (a-trans ,e6 hole))
