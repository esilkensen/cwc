#lang racket

;; This file defines the abstract syntax of Core Scheme (CS) in
;; Continuation-Passing Style (CPS), and a transformation from CS to CPS.

(require redex "cs.rkt")

(provide CPS cps)

(define-extended-language CPS CS
  (P (k W)
     (let (x W) P)
     (if0 W P P)
     (W k W ...)
     (W (λ (x) P) W ...)
     (O k W ...)
     (O (λ (x) P) W ...))
  (W c x (λ (k x ...) P)))

(define-metafunction CPS
  cps : M -> W
  [(cps M) (simp (F M))])

(define-metafunction CPS
  simp : M -> P or W
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

(define-metafunction CPS
  F : M -> W
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
                     (append (term (O ,k)) ts)
                     (let ([M_i (car ms-it)] [t_i (car ts-it)])
                       (term (,M_i (λ (,t_i) 
                                     ,(loop (cdr ms-it)
                                            (cdr ts-it)))))))))))])

(define-metafunction CPS
  Φ : V -> W
  [(Φ c) c]
  [(Φ x) x]
  [(Φ (λ (x ...) M))
   ,(let* ([M (term (F M))]
           [k (variable-not-in (term (x ... ,M)) 'k)])
      (term (λ (,k x ...) (,M ,k))))])
