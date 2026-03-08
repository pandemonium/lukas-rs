#!r6rs
(library (runtime)
  (export show print-endline)
  (import (chezscheme))

  (define (show x)
    (format "~a" x))

  (define (print-endline x)
    (display x)
    (newline)))
