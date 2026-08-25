(define (stdlib-print_endline s)
  (display s)
  (newline))

(define (show v)
  (cond
    [(string? v) v]
    [else
     (call-with-string-output-port
       (lambda (p) (write v p)))]))