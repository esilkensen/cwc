#lang racket

;; This file defines the abstract syntax of Core Scheme (CS) and utility
;; metafunctions for operating on its terms.

(require redex)

(provide CS δ extend lookup subst =α deBruijn)

;; Abstract Syntax of Core Scheme
(define-language CS
  (M V
     (let (x M) M)
     (if0 M M M)
     (M M ...)
     (O M ...))
  (V c x (λ (x ...) M))
  (c number)
  (O + - * /)
  ((x k) variable-not-otherwise-mentioned))

;; Evaluating primitive operations:
(define-metafunction CS
  δ : O (number ...) -> number
  [(δ + (number ...)) ,(apply + (term (number ...)))]
  [(δ - (number ...)) ,(apply - (term (number ...)))]
  [(δ * (number ...)) ,(apply * (term (number ...)))]
  [(δ / (number ...)) ,(apply / (term (number ...)))])

;; Extending environments:
(define-metafunction CS
  extend : ((x any) ...) (x ...) (any ...) -> ((x any) ...)
  [(extend ((x_1 any_1) ...) (x ..._n) (any ..._n))
   ((x_1 any_1) ... (x any) ...)])

;; Looking up bindings in environments:
(define-metafunction CS
  lookup : ((x any) ...) x -> any
  [(lookup ((x_1 any_1) ... (x any) (x_2 any_2) ...) x) any
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(lookup ((x_1 any_1) ...) x_2) #f])

;; Capture-avoiding substitution:
(define-metafunction CS
  [(subst (λ (x_1) any_1) x_1 any_2)
   (λ (x_1) any_1)]
  [(subst (λ (x_1) any_1) x_2 any_2)
   (λ (x_3)
     (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2))
                                (term x_1)))]
  [(subst (let (x_1 any_1) any_2) x_1 any_3)
   (let (x_1 (subst any_1 x_2 any_3)) any_2)]
  [(subst (let (x_1 any_1) any_2) x_2 any_3)
   (let (x_3 (subst any_1 x_2 any_3))
     (subst (subst-var any_2 x_1 x_3) x_2 any_3))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2 any_3))
                                (term x_1)))]
  [(subst x_1 x_1 any_1) any_1]
  [(subst (any_2 ...) x_1 any_1)
   ((subst any_2 x_1 any_1) ...)]
  [(subst any_2 x_1 any_1) any_2])

(define-metafunction CS
  [(subst-var (any_1 ...) variable_1 variable_2)
   ((subst-var any_1 variable_1 variable_2) ...)]
  [(subst-var variable_1 variable_1 variable_2) variable_2]
  [(subst-var any_1 variable_1 variable_2) any_1])

;; Alpha equivalence:
(define-metafunction CS
  =α : M M -> #t or #f
  [(=α M_1 M_2)
   ,(equal? (term (deBruijn M_1))
            (term (deBruijn M_2)))])

;; CS with numbers replacing vars & context 'E' mapping vars to numbers;
;; used for deBruijn algorithm;
(define-extended-language CS-D CS
  (N W
     (let (n N) N)
     (if0 N N N)
     (N N ...)
     (O N ...))
  (W c x (λ (n ...) N))
  (E ((x n) ...))
  (n number))

;; deBruijn index global & helpers
(define *ind* 0)
(define (get-ind) *ind*)
(define (reset-ind) (set! *ind* 0))
(define (next-ind) (set! *ind* (+ *ind* 1)) *ind*)

;; Rename variables in M with numbers using deBruijn indice algorithm
(define-metafunction CS-D
  deBruijn : M -> N
  [(deBruijn M)
   ,(begin
      (caching-enabled? #f) ;; pattern matching depends on *ind*
      (reset-ind)
      (term (deBruijn-acc M ())))])

;; deBruijn indice algorithm using a E accumulator mapping variables to numbers 
(define-metafunction CS-D
  deBruijn-acc : M E -> N
  [(deBruijn-acc c E) c]
  [(deBruijn-acc x E)
   ,(or (term (lookup E x)) (term x))]
  [(deBruijn-acc (λ (x ...) M_1) E)
   ,(let ([n_i (map (λ (x_i) (next-ind)) (term (x ...)))])
      (term (λ ,n_i (deBruijn-acc M_1 (extend E (x ...) ,n_i)))))]
  [(deBruijn-acc (let (x M_1) M_2) E)
   ,(let* ([ind (next-ind)]
           [M_3 (term (deBruijn-acc M_1 E))]
           [M_4 (term (deBruijn-acc M_2 (extend E (x) (,ind))))])
      (term (let (,ind ,M_3) ,M_4)))]
  [(deBruijn-acc (if0 M_1 M_2 M_3) E)
   ,(let* ([M_4 (term (deBruijn-acc M_1 E))]
           [M_5 (term (deBruijn-acc M_2 E))]
           [M_6 (term (deBruijn-acc M_3 E))])
      (term (if0 ,M_4 ,M_5 ,M_6)))]
  [(deBruijn-acc (M_1 M_2 ...) E)
   ,(let* ([M_3 (term (deBruijn-acc M_1 E))]
           [M_4 (term ((deBruijn-acc M_2 E) ...))])
      (cons M_3 M_4))]
  [(deBruijn-acc (O M ...) E)
   (O (deBruijn-acc M E) ...)])

;; -----------------------------------------------------------------------------

(module+ test

  (test-equal (term (lookup ((a 0)) a)) (term 0))
  (test-equal (term (lookup ((a 0)) b)) (term #f))

  (test-equal
    (term (extend ((a 0)) (x y z) (1 2 3)))
    (term ((a 0) (x 1) (y 2) (z 3))))

  (test-equal (term (=α x y)) #f)
  (test-equal (term (=α (λ (x) x) (λ (y) y))) #t))
