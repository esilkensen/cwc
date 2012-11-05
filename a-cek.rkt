#lang racket

;; This file defines the CEK-machine for CPS.

(require redex "cs.rkt" "cps.rkt" "anf.rkt" "cs-cek.rkt")

(provide eval-a A+CEK a-cek)

;; Semantics:
(define-metafunction CPS
  eval-a : M -> c
  [(eval-a M)
   ,(let ([S (term (M () stop))])
      (define results (apply-reduction-relation* a-cek S))
      (define match-reduction-result
        (term-match/single A+CEK [(stop c) (term c)]))
      (unless (= (length results) 1)
        (error 'eval-a "term ~s had multiple reductions: ~s" (term M) results))
      (match-reduction-result (car results)))])

;; Data Specifications:
(define-extended-language A+CEK A
  (S (M E K))
  (E ((x V*) ...))
  (V* c (cl (x ...) M E))
  (K stop (ar x M E K)))

;; Transition Rules:
;; TODO: add stopping conditions, debug further
(define a-cek
  (reduction-relation
   A+CEK
   #:domain S
   [--> (V E K)
        (M (extend E_1 (x) ((γ V E))) K_1)
        (where (ar x M E_1 K_1) K)
        "cek1"]
   [--> ((let (x V) M) E K)
        (M (extend E (x) ((γ V E))) K)
        "cek2"]
   [--> ((if0 V M_1 M_2) E K)
        (M_1 E K)
        (where 0 (γ V E))
        "cek3_0"]
   [--> ((if0 V M_1 M_2) E K)
        (M_2 E K)
        (where n (γ V E))
        "cek3_else"]
   [--> ((V V_1 ...) E K)
        (M (extend E_1 (x ...) (V* ...)) K)
        (where (cl (x ...) M E_1) (γ V E))
        (where (V* ...) ((γ V_1 E) ...))
        "cek4"]
   [--> ((let (x (V V_args ...)) M) E K)
        (M_1 (extend E_1 (x_i ...) (V* ...)) (ar x M E K))
        (where (cl x M_1 E_1) (γ V E))
        (where (V* ...) ((γ V_args E) ...))
        (where (x_i ...) ,(build-list (length (term (V* ...))) values))
        "cek5"]
   [--> ((O V_args ...) E K)
        (M_1 (extend E_1 (x_i ...) ((δ O (V* ...)))) K_1)
        (where (ar x M_1 E_1 K_1) K)
        (where (V* ...) ((γ V_args E) ...))
        (where (x_i ...)
               ,(build-list (length (term (V* ...)))
                            (λ (x) (string->symbol (string-append "x" (number->string x))))))
        (side-condition (displayln (term (V* ...))))
        "cek6"]
   [--> ((let (x (O V_args ...)) M) E K)
        (M (extend E (x) ((δ O (V* ...)))) K)
        (where (V* ...) ((γ V_args E) ...))
        ;; (where x_1 ,(variable-not-in (term ((let (x (O V_args ...)) M) E K)) 'x))
        (side-condition (displayln (term (V* ...))))
        "cek7"]))


;; -----------------------------------------------------------------------------

(module+ test
  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))

  (define p4 (term (+ (+ 2 2) 1)))
  (test-equal (term (eval-a (cs->anf ,p4))) 4)
  )

  ;; (test-equal (term (eval-a (cs->anf ,p1))) 6)
  ;; (test-equal (term (eval-a (cs->anf ,p2))) 1)
  ;; (test-equal (term (eval-a (cs->anf ,p3))) 118))
