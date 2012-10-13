#lang racket

;; This file defines the abstract syntax of Core Scheme (CS) and a
;; transformation from CS to CPS(CS).

(require redex)

(provide CS F)

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
