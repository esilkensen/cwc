;; Phillip Mates, Erik Silkensen
;; mates@ccs.neu.edu, ejs@ccs.neu.edu

#lang racket

;; This module defines the languages, transformations, and abstract machines
;; from The Essence of Compiling with Continuations (Flanagan et al. 1993).
;; It includes the following submodules:
;;   - cs      Core Scheme (CS)
;;   - cs-cek  CEK-machine for CS
;;   - cps     CS in continuation-passing style (CPS)
;;   - cps-ce  CE-machine for CPS
;;   - cps-cek CEK-machine for CPS
;;   - a       CS in A-normal form (A)
;;   - a-cek   CEK-machine for A

(require redex/reduction-semantics)

;; ============================================================================

(module cs racket
  ;; This submodule defines the abstract syntax of Core Scheme (CS) and utility
  ;; metafunctions for operating on its terms.
  
  (provide CS δ extend lookup subst =α)
  
  (require redex/reduction-semantics)
  
  ;; Abstract Syntax of Core Scheme:
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
    [(lookup ((x_1 any_1) ... (x any) (x_2 any_2) ...) x)
     any
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
     ,(equal? (term (remove-names M_1))
              (term (remove-names M_2)))])
  
  ;; Abstract Syntax of CS with names removed:
  (define-extended-language CS-D CS
    (N W
       (let (n N) N)
       (if0 N N N)
       (N N ...)
       (O N ...))
    (W c x (λ (n ...) N))
    (E ((x n) ...))
    (n number))
  
  (define *ind* 0)
  (define (get-ind) *ind*)
  (define (reset-ind) (set! *ind* 0))
  (define (next-ind) (set! *ind* (+ *ind* 1)) *ind*)
  
  ;; Removing names in a term, replacing them with numbers:
  (define-metafunction CS-D
    remove-names : M -> N
    [(remove-names M)
     ,(begin
        (caching-enabled? #f) ;; pattern matching depends on *ind*
        (reset-ind)
        (term (remove-names-aux M ())))])
  
  (define-metafunction CS-D
    remove-names-aux : M E -> N
    [(remove-names-aux c E) c]
    [(remove-names-aux x E)
     ,(or (term (lookup E x)) (term x))]
    [(remove-names-aux (λ (x ...) M_1) E)
     ,(let ([n_i (map (λ (x_i) (next-ind)) (term (x ...)))])
        (term (λ ,n_i (remove-names-aux M_1 (extend E (x ...) ,n_i)))))]
    [(remove-names-aux (let (x M_1) M_2) E)
     ,(let* ([ind (next-ind)]
             [M_3 (term (remove-names-aux M_1 E))]
             [M_4 (term (remove-names-aux M_2 (extend E (x) (,ind))))])
        (term (let (,ind ,M_3) ,M_4)))]
    [(remove-names-aux (if0 M_1 M_2 M_3) E)
     ,(let* ([M_4 (term (remove-names-aux M_1 E))]
             [M_5 (term (remove-names-aux M_2 E))]
             [M_6 (term (remove-names-aux M_3 E))])
        (term (if0 ,M_4 ,M_5 ,M_6)))]
    [(remove-names-aux (M_1 M_2 ...) E)
     ,(let* ([M_3 (term (remove-names-aux M_1 E))]
             [M_4 (term ((remove-names-aux M_2 E) ...))])
        (cons M_3 M_4))]
    [(remove-names-aux (O M ...) E)
     (O (remove-names-aux M E) ...)]))

;; ----------------------------------------------------------------------------

(require 'cs)
(module+ test
  (displayln "Testing module cs...")
  (define p1 (term (+ (+ 2 2) (let (x 1) (+ x x)))))
  (define p2 (term (if0 (let (x 1) (- x x)) 1 2)))
  (define p3 (term (let (f (λ (x y) (* x y y))) (+ (f 2 3) (f 4 5)))))
  (define p4 (term (+ 1 (let (x (+ 1 1)) (- x x)))))
  
  (define r1 6)
  (define r2 1)
  (define r3 118)
  (define r4 1)
  
  (define P (list p1 p2 p3 p4))
  (define R (list r1 r2 r3 r4))
  (for ([p P])
    (test-equal (redex-match? CS M p) #t))
  
  (test-equal (term (lookup ((a 0)) a)) (term 0))
  (test-equal (term (lookup ((a 0)) b)) (term #f))
  
  (test-equal
   (term (extend ((a 0)) (x y z) (1 2 3)))
   (term ((a 0) (x 1) (y 2) (z 3))))
  
  (test-equal (term (=α x y)) #f)
  (test-equal (term (=α (λ (x) x) (λ (y) y))) #t))

;; ============================================================================

(module cs-cek racket
  ;; This submodule defines the CEK-machine for CS.
  
  (provide eval-d CS+EK ->cs-cek γ)
  
  (require redex/reduction-semantics (submod ".." cs))
  
  ;; Semantics:
  (define-metafunction CS
    eval-d : M -> c
    [(eval-d M)
     (result ,(apply-reduction-relation* ->cs-cek (term (M () stop))))])
  
  (define-metafunction CS
    result : [(stop c)] -> c
    [(result ((stop c))) c])
  
  ;; Data Specifications:
  (define-extended-language CS+EK CS
    (S (M E K) (K V*))
    (E ((x V*) ...))
    (V* c (cl (x ...) M E))
    (K stop
       (ap (V* ...) (M ...) E K)
       (lt x M E K)
       (if M M E K)
       (pr O (V* ...) (M ...) E K)))
  
  ;; Transition Rules:
  (define ->cs-cek
    (reduction-relation
     CS+EK
     #:domain S
     [--> (V E K)
          (K (γ V E))
          "cek1"]
     [--> ((let (x M_1) M_2) E K)
          (M_1 E (lt x M_2 E K))
          "cek2"]
     [--> ((if0 M_1 M_2 M_3) E K)
          (M_1 E (if M_2 M_3 E K))
          "cek3"]
     [--> ((M M_1 ...) E K)
          (M E (ap () (M_1 ...) E K))
          "cek4"]
     [--> ((O M_1 M_2 ...) E K)
          (M_1 E (pr O () (M_2 ...) E K))
          "cek5"]
     [--> ((lt x M ((x_1 V*_1) ...) K) V*)
          (M ((x_1 V*_1) ... (x V*)) K)
          "cek6"]
     [--> ((if M_1 M_2 E K) 0)
          (M_1 E K)
          "cek7"]
     [--> ((if M_1 M_2 E K) V*)
          (M_2 E K)
          (side-condition (not (eq? 0 (term V*))))
          "cek8"]
     [--> ((ap (V* ...) (M M_1 ...) E K) V*_1)
          (M E (ap (V* ... V*_1) (M_1 ...) E K))]
     [--> ((ap ((cl (x_1 ...) M_1 E_1) V*_1 ...) () E K) V*_n)
          (M_1 (extend E_1 (x_1 ...) (V*_1 ... V*_n)) K)
          "cek9"]
     [--> ((pr O (V* ...) (M M_1 ...) E K) V*_1)
          (M E (pr O (V* ... V*_1) (M_1 ...) E K))
          "cek10"]
     [--> ((pr O (V* ...) () E K) V*_n)
          (K (δ O (V* ... V*_n)))
          "cek11"]))
  
  ;; Converting syntactic values to machine values:
  (define-metafunction CS+EK
    γ : V E -> V* or #f
    [(γ c E) c]
    [(γ x E) (lookup E x)]
    [(γ (λ (x ...) M) E) (cl (x ...) M E)]))

;; ----------------------------------------------------------------------------

(require 'cs-cek)
(module+ test
  (displayln "Testing module cs-cek...")
  (for ([p P] [r R])
    (test-equal (term (eval-d ,p)) r)))

;; ============================================================================

(module cps racket
  ;; This submodule defines the abstract syntax of Core Scheme (CS) in
  ;; Continuation-Passing Style (CPS) and a transformation from CS to CPS.
  
  (provide CPS cs->cps)
  
  (require redex/reduction-semantics (submod ".." cs))
  
  ;; Abstract Syntax of Core Scheme in Continuation-Passing Style:
  (define-extended-language CPS CS
    (P (k W)
       (let (x W) P)
       (if0 W P P)
       (W k W ...)
       (W (λ (x) P) W ...)
       (O k W ...)
       (O (λ (x) P) W ...))
    (W c x (λ (k x ...) P)))
  
  ;; Transforming a CS term to β-normal form:
  (define-metafunction CPS
    cs->cps : M -> W
    [(cs->cps M) (let-simp (simp (F M)))])
  
  ;; A second simplification phase (β for let):
  (define-metafunction CPS
    [(let-simp c) c]
    [(let-simp x) x]
    [(let-simp (λ (x ...) M))
     (λ (x ...) (let-simp M))]
    [(let-simp (let (x_1 x_2) M))
     (subst M x_1 x_2)]
    [(let-simp (let (x M_1) M_2))
     (let (x (let-simp M_1)) (let-simp M_2))]
    [(let-simp (if0 M_1 M_2 M_3))
     (if0 (let-simp M_1) (let-simp M_2) (let-simp M_3))]
    [(let-simp (M_1 M_2 ...))
     ((let-simp M_1) (let-simp M_2) ...)]
    [(let-simp (O M ...))
     (O (let-simp M) ...)])
  
  ;; The simplification phase (β):
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
  
  ;; The CPS transformation (F):
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
        (term (λ (,k x ...) (,M ,k))))]))  

;; ----------------------------------------------------------------------------

(require 'cps)
(module+ test
  (displayln "Testing module cps...")
  (define e1 (term (+ (+ 2 2) (let (x 1) (f x)))))
  (define e1-simp
    (term (λ (k) (+ (λ (t1) (let (x 1) (f (λ (t2) (+ k t1 t2)) x))) 2 2))))
  (test-equal (term (=α (cs->cps ,e1) ,e1-simp)) #t))

;; ============================================================================

(module cps-ce racket
  ;; This submodule defines the CE-machine for CPS.
  
  (provide eval-n CPS+E ->cps-ce)
  
  (require redex/reduction-semantics (submod ".." cs) (submod ".." cps))
  
  ;; Semantics:
  (define-metafunction CPS
    eval-n : W -> c
    [(eval-n (λ (k) P))
     (result ,(apply-reduction-relation*
               ->cps-ce (term (P ((k (cl x (k x) ((k stop)))))))))])
  
  (define-metafunction CPS
    result : [((k x) ((k stop) (x c)))] -> c
    [(result (((k x) ((k stop) (x c))))) c])
  
  ;; Data Specifications:
  (define-extended-language CPS+E CPS
    (S (P E))
    (E ((x W*) ...))
    (W* c (cl (k x ...) P E) (cl x P E) stop))
  
  ;; Transition Rules:
  (define ->cps-ce
    (reduction-relation
     CPS+E
     #:domain S
     [--> ((k W) E)
          (P (extend E_2 (x) ((μ W E))))
          (where (cl x P E_2) (lookup E k))
          "ce1"]
     [--> ((let (x W) P) E)
          (P (extend E (x) ((μ W E))))
          "ce2"]
     [--> ((if0 W P_1 P_2) E)
          ,(if (eq? (term (μ W E)) 0)
               (term (P_1 E))
               (term (P_2 E)))
          "ce3"]
     [--> ((W k W_1 ...) E)
          (P_1 (extend E_1 (k_1 x_1 ...) ((lookup E k) (μ W_1 E) ...)))
          (where (cl (k_1 x_1 ...) P_1 E_1) (μ W E))
          "ce4"]
     [--> ((W (λ (x) P) W_1 ...) E)
          (P_1 (extend E_1 (k_1 x_1 ...) ((cl x P E) (μ W_1 E) ...)))
          (where (cl (k_1 x_1 ...) P_1 E_1) (μ W E))
          "ce5"]
     [--> ((O k W_1 ...) E)
          (P_1 (extend E_1 (x) ((δ O ((μ W_1 E) ...)))))
          (where (cl x P_1 E_1) (lookup E k))
          "ce6"]
     [--> ((O (λ (x) P) W_1 ...) E)
          (P (extend E (x) ((δ O ((μ W_1 E) ...)))))
          "ce7"]))
  
  ;; Converting values to machine values:
  (define-metafunction CPS+E
    μ : W E -> W* or #f
    [(μ c E) c]
    [(μ x E) (lookup E x)]
    [(μ (λ (k x ...) P) E) (cl (k x ...) P E)]))

;; ----------------------------------------------------------------------------

(require 'cps-ce)
(module+ test
  (displayln "Testing module cps-ce...")
  (for ([p P] [r R])
    (test-equal (term (eval-n (cs->cps ,p))) r)))

;; ============================================================================

(module cps-cek racket
  ;; This submodule defines the CEK-machine for CPS.
  
  (provide eval-c CPS+EK ->cps-cek)
  
  (require redex/reduction-semantics (submod ".." cs) (submod ".." cps))
  
  ;; Semantics:
  (define-metafunction CPS
    eval-c : W -> c
    [(eval-c (λ (k) P))
     (result ,(apply-reduction-relation*
               ->cps-cek (term (P () (ar x (k x) () stop)))))])
  
  (define-metafunction CPS
    result : [((k x) ((x c)) stop)] -> c
    [(result (((k x) ((x c)) stop))) c])
  
  ;; Data Specifications:
  (define-extended-language CPS+EK CPS
    (S (P E K))
    (E ((x W*) ...))
    (W* c (cl (k x ...) P E))
    (K stop (ar x P E K)))
  
  ;; Transition Rules:
  (define ->cps-cek
    (reduction-relation
     CPS+EK
     #:domain S
     [--> ((k W) E (ar x P E_1 K_1))
          (P (extend E_1 (x) ((μ W E))) K_1)
          "cek1"]
     [--> ((let (x W) P) E K)
          (P (extend E (x) ((μ W E))) K)
          "cek2"]
     [--> ((if0 W P_1 P_2) E K)
          ,(if (eq? (term (μ W E)) 0)
               (term (P_1 E K))
               (term (P_2 E K)))
          "cek3"]
     [--> ((W k W_1 ...) E K)
          (P (extend E_1 (x_1 ...) ((μ W_1 E) ...)) K)
          (where (cl (k_1 x_1 ...) P E_1) (μ W E))
          "cek4"]
     [--> ((W (λ (x) P) W_1 ...) E K)
          (P_1 (extend E_1 (x_1 ...) ((μ W_1 E) ...)) (ar x P E K))
          (where (cl (k_1 x_1 ...) P_1 E_1) (μ W E))
          "cek5"]
     [--> ((O k W_1 ...) E (ar x P_1 E_1 K_1))
          (P_1 (extend E_1 (x) ((δ O ((μ W_1 E) ...)))) K_1)
          "cek6"]
     [--> ((O (λ (x) P) W_1 ...) E K)
          (P (extend E (x) ((δ O ((μ W_1 E) ...)))) K)
          "cek7"]))
  
  ;; Converting values to machine values:
  (define-metafunction CPS+EK
    μ : W E -> W* or #f
    [(μ c E) c]
    [(μ x E) (lookup E x)]
    [(μ (λ (k x ...) P) E) (cl (k x ...) P E)]))

;; ----------------------------------------------------------------------------

(require 'cps-cek)
(module+ test
  (displayln "Testing module cps-cek...")
  (for ([p P] [r R])
    (test-equal (term (eval-c (cs->cps ,p))) r)))

;; ============================================================================

(module a racket
  ;; This submodule defines the abstract syntax of Core Scheme (CS) in A-normal
  ;; form (A) and transformations from CS to Continuation-Passing Style (CPS)
  ;; to A and also from CS to A, directly.
  
  (provide A cs->cps->anf cs->anf)
  
  (require redex/reduction-semantics (submod ".." cs) (submod ".." cps))
  
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
    [(cs->cps->anf M) (cps->anf (cs->cps M))])
  
  ;; Transforming a CPS term to A-normal form:
  (define-metafunction A
    cps->anf : W -> M
    [(cps->anf (λ (k) P)) (U P)])
  
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
    ;; context for terms yet to be turned into ANF
    (E hole (let (x E) M) (if0 E M M) (F V ... E M ...))
    ;; context for terms already in ANF
    (Q hole (let (x V) Q) (let (x (F V ...)) Q) (if0 V Q M) (if0 V M Q))
    (F O V))
  
  ;; The A-reductions:
  (define ->A
    (reduction-relation
     CS+E
     [==> (in-hole E (let (x_1 M_1) M_2))
          (let (x_2 M_1) (in-hole E (subst M_2 x_1 x_2)))
          (where x_2 ,(variable-not-in (term E) (term x_1)))
          (side-condition (term (not-hole E)))
          "A1"]
     [==> (in-hole E (if0 V M_1 M_2))
          (if0 V (in-hole E M_1) (in-hole E M_2))
          (side-condition (term (not-hole E)))
          "A2"]
     [==> (in-hole E (F V ...))
          (let (x (F V ...)) (in-hole E x))
          (where x ,(variable-not-in (term E) (term t1)))
          (side-condition
           (and (term (not-hole E))
                (term (not-let-hole E))))
          "A3"]
     with
     [(--> (in-hole Q M_1) (in-hole Q M_2))
      (==> M_1 M_2)]))
  
  ;; Transforming a CS term to A-normal form:
  (define-metafunction CS+E
    [(cs->anf M_1)
     (assert M_2)
     (where (M_2) ,(apply-reduction-relation* ->A (term M_1)))])
  
  ;; Assert that a term is in A-normal form:
  (define-metafunction A
    [(assert M) M])
  
  (define-metafunction CS+E
    not-hole : E -> #t or #f
    [(not-hole hole) #f]
    [(not-hole E) #t])
  
  (define-metafunction CS+E
    not-let-hole : E -> #t or #f
    [(not-let-hole (in-hole E (let (x hole) M))) #f]
    [(not-let-hole E) #t]))

;; ----------------------------------------------------------------------------

(require 'a)
(module+ test
  (displayln "Testing module a...")
  (for ([p P])
    (define a1 (term (cs->cps->anf ,p)))
    (define a2 (term (cs->anf ,p)))
    (test-equal (term (eval-d ,p)) (term (eval-d ,a1)))
    (test-equal (term (eval-d ,p)) (term (eval-d ,a2)))
    (test-equal (term (=α ,a1 ,a2)) #t)))

;; ============================================================================

(module a-cek racket
  ;; This submodule defines the CEK-machine for A.
  
  (provide eval-a A+EK ->a-cek)
  
  (require redex/reduction-semantics
           (submod ".." cs) (submod ".." cs-cek) (submod ".." a))
  
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
          "cek7"])))

;; ----------------------------------------------------------------------------

(require 'a-cek)
(module+ test
  (displayln "Testing module a-cek...")
  (for ([p P] [r R])
    (test-equal (term (eval-a (cs->anf ,p))) r)))

;; ============================================================================

(module+ test (test-results))