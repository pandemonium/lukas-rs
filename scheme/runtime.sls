#!r6rs
(library (runtime)
  (export
    show
    print-endline
    bool-xor
    marm-and
    marm-or
    marm-xor
    marm-not
    char-of-byte
    int-of-float
    text-fold-right
    )
  (import (chezscheme))

  ;; Match the C runtime's `show`: a Marmelade Bool is a Scheme boolean, which
  ;; `~a` would render as #t/#f -- render it as true/false instead. Other scalars
  ;; already agree under ~a.
  (define (show x)
    (if (boolean? x)
        (if x "true" "false")
        (format "~a" x)))

  (define (print-endline x)
    (display x)
    (newline))

  (define (bool-xor a b)
    (if a (not b) b))

  ;; `and`/`or`/`xor` are overloaded: logical on Bool, bitwise on Int. The C backend
  ;; monomorphises on the static type; here (types are erased) we dispatch at run time
  ;; on the operand, which is a Scheme boolean for Bool and a fixnum for Int.
  (define (marm-and a b)
    (if (boolean? a) (and a b) (bitwise-and a b)))
  (define (marm-or a b)
    (if (boolean? a) (or a b) (bitwise-ior a b)))
  (define (marm-xor a b)
    (if (boolean? a) (bool-xor a b) (bitwise-xor a b)))
  (define (marm-not a)
    (if (boolean? a) (not a) (bitwise-not a)))

  ;; `Char.of_byte`: total Int -> Char, masking to the low byte so every input is a
  ;; valid Scheme char (a Marmelade Char is a Scheme char).
  (define (char-of-byte n)
    (integer->char (bitwise-and n 255)))

  ;; Float -> Int narrows by discarding the fractional part toward zero.
  (define (int-of-float n)
    (inexact->exact (truncate n)))

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
