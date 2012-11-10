#lang racket

(define (make-latex filename)
  (define (latex-char char)
    (define greek
      #hash((#\λ . "lambda") (#\α . "alpha") (#\β . "beta") (#\δ . "delta")
            (#\γ . "gamma") (#\μ . "mu") (#\Φ . "Phi") (#\Ψ . "Psi")))
    (if (hash-has-key? greek char)
        (format "\\(\\~a\\)" (hash-ref greek char))
        char))
  (unless (directory-exists? "appendix")
    (make-directory "appendix"))
  (let-values ([(base name must-be-dir?)
                (split-path (string->path filename))]
               [(dest) "appendix/~a"])
    (with-output-to-file (format dest (path-replace-suffix name ".tex"))
      (λ ()
        (with-input-from-file filename
          (λ ()
            (printf "\\begin{alltt}\n")
            (do ([c (read-char) (read-char)])
                ((eof-object? c) #t)
              (printf "~a" (latex-char c)))
            (printf "\\end{alltt}\n"))))
      #:exists 'replace)))

(let ([argv (current-command-line-arguments)])
  (if (zero? (vector-length argv))
      (printf "usage: ~a [<source-file>] ...~n"
              (find-system-path 'run-file))
      (for ([arg argv])
        (make-latex arg))))
