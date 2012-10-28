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

(define ->a-trans
  (reduction-relation
   A
   #:domain N
   ;; [--> (in-hole ε (O V_arg ...))
        ;; (let (t (O V_arg ...)) (in-hole ε t))
        ;; (side-condition (not (term (empty-context? ε))))
        ;; "A3_O_unrestricted"]
   [--> (in-hole ε (let (x M) M_1))
        (let (x M) (in-hole ε M_1))
        (side-condition (and
                         (not (term (empty-context? ε)))
                         (not (term (fv-ε? x ε)))))
        "A1"]
   [--> (in-hole ε (if0 V M_1 M_2))
        (if0 V (in-hole ε M_1) (in-hole ε M_2))
        (side-condition (term (empty-context? ε)))
        "A2"]
   [--> (in-hole ε (V V_arg ...))
        (let (x_new (V V_arg ...)) (in-hole ε x_new))
        (where x_new ,(variable-not-in (term ε) 'x))
        (side-condition (and
                         (not (term (empty-context? ε)))
                         ;; XXX: ε != ε'[(let (z []) M)]
                         (not (term (let-context? ε)))
                         (not (term (fv-ε? x_new ε)))))
        "A3_V"]
   [--> (in-hole ε (O V_arg ...))
        (let (x_new (O V_arg ...)) (in-hole ε x_new))
        (where x_new ,(variable-not-in (term ε) 'x))
        (side-condition (displayln (term ε)))
        (side-condition (displayln 
                          `(
                           ,(not (term (empty-context? ε)))
                           ;; XXX: ε != ε'[(let (z []) M)]
                           ,(not (term (let-context? ε)))
                           ,(not (term (fv-ε? x_new ε))))))
        (side-condition (and
                         (not (term (empty-context? ε)))
                         ;; XXX: ε != ε'[(let (z []) M)]
                         (not (term (let-context? ε)))
                         (not (term (fv-ε? x_new ε)))))
        "A3_O"]))

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
  [(fv-ε? x (O V ... ε M ...))
   ,(andmap identity
            (flatten
             `(,(term (fv-ε? x ε))
               ,(term ((fv? x V) ...))
               ,(term ((fv? x M) ...)))))
   (side-condition (displayln "in fv-e, second to lsat"))
   ]
  [(fv-ε? x (V V_arg ... ε M ...))
   ,(andmap identity
            (flatten
              `(,(term (fv-ε? x ε))
                ,(term (fv? x V))
                ,(term (fv? x V_arg ...))
                ,(term (fv? x M ...)))))
   (side-condition (displayln "in fv-e, lsat"))
   ])

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
  [(fv? x (O V_1 ...)) ,(andmap identity (term ((fv? x V_1) ...)))]
  [(fv? x (let (x (O V ...)) M)) #f]
  [(fv? x (let (y (O V ...)) M))
   ,(and (term (fv? x M))
         (andmap (λ (x) x)
                 (term (fv? x V ...))))]

  ;; Values
  [(fv? x x) #t]
  [(fv? x x_1) #t]
  [(fv? x c) #t]
  [(fv? x (λ (x_l ... x x_r ...) M)) #f]
  [(fv? x (λ (x_arg ...) M)) (fv? x M)])

;; Test fv?
(define e1 (term (let (x 1) x)))
(define e2 (term ((λ (x y) x) 1 2)))
(define e3 (term (let (z 1) ((λ (x y) z) 1 2))))
(define e4 (term (+ (+ 2 2) (let (x (1)) (+ x 1)))))
(define e5 (term (+ (+ 2 2) 3)))

(test-equal (term (fv? x ,e1)) #f)
(test-equal (term (fv? x ,e2)) #f)
(test-equal (term (fv? z ,e2)) #t)

(define E0 (term hole))
(define E1 (term (let (x hole) x)))
(define E2 (term (if0 ,E1 ,e1 ,e2)))

(test-equal (term (empty-context? ,E0)) #t)
(test-equal (term (empty-context? ,E2)) #f)

;; Test fv-ε?
(test-equal (term (fv-ε? x ,E1)) #f)
(test-equal (term (fv-ε? x ,E2)) #f)
(test-equal (term (fv-ε? y ,E2)) #f)
(test-equal (term (fv-ε? z ,E2)) #t)

;; In CS language
(for/and ((an-s (list e1 e2 e3 e4 e5)))
  (redex-match? A M an-s))

;; In A Language
(for/and ((an-s (list e1 e2 e3 e4 e5)))
  (redex-match? A N an-s))

;; test ->a-trans
(traces ->a-trans e5)
