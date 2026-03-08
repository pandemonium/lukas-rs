(import (chezscheme))

(suppress-greeting #t)

(scheme-start
  (lambda args
    (Root-start 40) ; compute random seed and pass instead.
    (exit)))
