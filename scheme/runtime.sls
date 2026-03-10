#!r6rs
(library (runtime)
  (export
    show
    print-endline
    bool-xor
    text-fold-right
    )
  (import (chezscheme))

  (define (show x)
    (format "~a" x))

  (define (print-endline x)
    (display x)
    (newline))

  (define (bool-xor a b)
    (if a (not b) b))

  (define text-fold-right
      (lambda (f z s)
          (do ([i (- (string-length s) 1) (- i 1)]
               [xs z ((f (string-ref s i)) xs)]
              )
            ((< i 0) xs))))

  (define text-fold-left
      (lambda (f z s)
          (let ([length (string-length s)])
          (do ([i 0 (+ i 1)]
               [xs z ((f xs) (string-ref s i))]
              )
            ((= i length) xs)))))
)
