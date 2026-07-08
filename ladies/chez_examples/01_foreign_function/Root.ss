;; Foreign implementation for the `foreign` declarations in Root.lady.
;; Each definition is named <Module>-<symbol>, matching the emitted call site.
(define Root-sqrt_int
  (lambda (n)
    (exact (floor (sqrt n)))))
