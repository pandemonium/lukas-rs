(import (chezscheme))

(define (square x) (* x x))

(display (square 5))
(newline)

(flush-output-port (current-output-port))
(exit 0)

(define (union-tag co-product)
    (vector-ref co-product 0)
    )

(cond
    [(eq? (union-tag scrutinee) 'Some) (let [x0 (vector-ref scrutinee 1)] x0)]
    [(eq? (union-tag scrutinee) 'None) "hi" ]
)
