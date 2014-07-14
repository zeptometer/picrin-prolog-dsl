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

  ;; amb with lazy evaluation
  (define-syntax do-amb
    (syntax-rules ()
      ((do-amb expr ...)
       ((amb (list (lambda () expr) ...))))))

  (define (save-backtrack) path)
  (define (restore-backtrack p) (set! path p))
  (define (clear-backtrack) (set! path '()))

  (export amb fail
	  do-amb
	  save-backtrack
	  restore-backtrack
	  clear-backtrack))
