;; Foreign implementations for the `foreign` declarations in Root.lady.
;; Each definition is named <Module>-<symbol>, matching the emitted call site.
;; Marmelade functions are curried, so a multi-argument foreign function is a
;; nest of one-argument lambdas.
;;
;; `Rational` is a foreign *type*: it has no Scheme definition of its own. Its
;; values are ordinary Chez exact rationals, produced and consumed below.

(define Root-make_rational
  (lambda (numer)
    (lambda (denom)
      (/ numer denom))))

(define Root-add_rational
  (lambda (a)
    (lambda (b)
      (+ a b))))

(define Root-show_rational
  (lambda (r)
    (number->string r)))
