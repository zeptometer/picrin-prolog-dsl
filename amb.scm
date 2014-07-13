(define-library (picrin amb)
  (import (scheme base))

  (define path '())

  (define (amb l)
    (call/cc (lambda (k)
               (set! path (append (map (lambda (v) (lambda () (k v))) l) path))
               (if (null? path)
                   (error "no more backtrack!")
                   (let ((head (car path))
                         (tail (cdr path)))
                     (set! path tail)
                     (head))))))

  (define (fail) (amb '()))

  (export amb fail))
