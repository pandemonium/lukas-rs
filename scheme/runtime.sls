#!r6rs
(library (runtime)
  (export show print-endline bool-xor)
  (import (chezscheme))

  (define (show x)
    (format "~a" x))

  (define (print-endline x)
    (display x)
    (newline))

  (define (bool-xor a b)
    (if a (not b) b))
)
