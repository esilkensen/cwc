#lang racket

;; This file defines a transformation from CS to CPS.

(require redex "cs.rkt")

(provide cps F simp)

(define-metafunction CS
  cps : M -> M
  [(cps M) (simp (F M))])

(define-metafunction CS
  F : M -> M
  [(F V)
   ,(let* ([V (term (Φ V))]
           [k (variable-not-in V 'k)])
      (term (λ (,k) (,k ,V))))]
  [(F (let (x M_1) M_2))
   ,(let* ([M_1 (term (F M_1))]
           [M_2 (term (F M_2))]
           [k (variable-not-in (term (x ,M_1 ,M_2)) 'k)]
           [t (variable-not-in (term (x ,M_1 ,M_2)) 't)])
      (term (λ (,k) (,M_1 (λ (,t) (let (x ,t) (,M_2 ,k)))))))]
  [(F (if0 M_1 M_2 M_3))
   ,(let* ([M_1 (term (F M_1))]
           [M_2 (term (F M_2))]
           [M_3 (term (F M_3))]
           [k (variable-not-in (list M_1 M_2 M_3) 'k)]
           [t (variable-not-in (list M_1 M_2 M_3) 't)])
      (term (λ (,k) (,M_1 (λ (,t) (if0 ,t (,M_2 ,k) (,M_3 ,k)))))))]
  [(F (M M_1 ...))
   ,(let* ([M (term (F M))]
           [MS (term ((F M_1) ...))]
           [k (variable-not-in (cons M MS) 'k)]
           [t (variable-not-in (cons M MS) 't)]
           [ts (variables-not-in
                (append (list M t) MS)
                (map (λ (t) 't) MS))])
      (term (λ (,k)
              (,M (λ (,t)
                    ,(let loop ([ms-it MS] [ts-it ts])
                       (if (null? ms-it)
                           (append (term (,t ,k)) ts)
                           (let ([M_i (car ms-it)] [t_i (car ts-it)])
                             (term (,M_i (λ (,t_i) 
                                           ,(loop (cdr ms-it)
                                                  (cdr ts-it)))))))))))))]
  [(F (O M_1 ...))
   ,(let* ([MS (term ((F M_1) ...))]
           [k (variable-not-in MS 'k)]
           [ts (variables-not-in MS (map (λ (t) 't) MS))])
      (term (λ (,k)
              ,(let loop ([ms-it MS] [ts-it ts])
                 (if (null? ms-it)
                     (term (,k ,(append (term (O)) ts)))
                     (let ([M_i (car ms-it)] [t_i (car ts-it)])
                       (term (,M_i (λ (,t_i) 
                                     ,(loop (cdr ms-it)
                                            (cdr ts-it)))))))))))])

(define-metafunction CS
  Φ : V -> V
  [(Φ c) c]
  [(Φ x) x]
  [(Φ (λ (x ...) M))
   ,(let* ([M (term (F M))]
           [k (variable-not-in (term (x ... ,M)) 'k)])
      (term (λ (,k x ...) (,M ,k))))])

(define-metafunction CS
  simp : M -> M
  [(simp c) c]
  [(simp x) x]
  [(simp (λ (x ...) M))
   (λ (x ...) (simp M))]
  [(simp (let (x M_1) M_2))
   (let (x (simp M_1)) (simp M_2))]
  [(simp (if0 M_1 M_2 M_3))
   (if0 (simp M_1) (simp M_2) (simp M_3))]
  [(simp (M_1 M_2))
   (simp (subst M_3 x M_2))
   (where (λ (x) M_3) (simp M_1))]
  [(simp (M_1 M_2 ...))
   ((simp M_1) (simp M_2) ...)]
  [(simp (O M ...))
   (O (simp M) ...)])

(define-metafunction CS
  [(subst (λ (x_1) any_1) x_1 any_2)
   (λ (x_1) any_1)]
  [(subst (λ (x_1) any_1) x_2 any_2)
   (λ (x_3)
     (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2))
                                (term x_1)))]
  [(subst (let (x_1 any_1) any_2) x_1 any_3)
   (let (x_1 any_1) any_2)]
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

;; -----------------------------------------------------------------------------

(module+ test
  (require "cek.rkt")
  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))
  
  (test-equal (eval-d p1) (eval-d (term ((F ,p1) (λ (x) x)))))
  (test-equal (eval-d p2) (eval-d (term ((F ,p2) (λ (x) x)))))
  (test-equal (eval-d p3) (eval-d (term ((F ,p3) (λ (x) x)))))

  (test-equal (eval-d p1) (eval-d (term ((cps ,p1) (λ (x) x)))))
  (test-equal (eval-d p2) (eval-d (term ((cps ,p2) (λ (x) x)))))
  (test-equal (eval-d p3) (eval-d (term ((cps ,p3) (λ (x) x))))))
