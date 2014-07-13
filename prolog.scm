(import (picrin amb))
(import (srfi 1))

(define (binding x bind)
  (define (recbind x bind)
    (let ((y (assq x bind)))
      (and y (or (recbind y bind) y))))
  
  (let ((v (recbind x bind)))
    (and v (cdr v))))

(define (match l r bind)
  (cond ((or (eqv? l r) (eq? l '_) (eq? r '_)) (values bind #t))
        ((binding l bind) => (lambda (nl) (match nl r bind)))
        ((binding r bind) => (lambda (nr) (match l nr bind)))
        ((var? l) (values `((,l ,r) ,@bind)))
        ((var? r) (values `((,r ,l) ,@bind)))
        ((and (pair? l) (pair? r)
              (not (eq (car l) 'quote))
              (not (eq (car r) 'quote)))
         (let-values (((bind success) (match (car l) (car r) bind)))
           (if success
               (match (cdr l) (cdr r) bind)
               (values 'fail #f))))
        (else (values 'fail #f))))

(define rules '())

(define-record-type uniqueobj
  (genvar)
  var?)

(define (collect-vars rule)
  (define (recur rule)
    (cond ((pair? rule) (if (eq (car rule) 'quote)
                            '()
                            (append (collect-vars (car rule))
                                    (collect-vars (cdr rule)))))
          ((symbol? rule) rule)
          (else '())))
  (delete-duplicates (recur rule)))

(define (change-vars rule)
  (let ((table (map (lambda (v) `(,v ,(genvar)))
                    (collect-vars rule))))
    (define (recur rule)
      (cond ((pair? rule) (if (eq (car rule) 'quote)
                              rule
                              (recur rule)))
            ((symbol? rule) (assoc rule table))
            (else rule)))))

(define (implies r query bind)
  (let* ((r* (change-vars r))
         (pattern (car r*))
         (resolve (cdr r*)))
    (let-values (((newbind success) (match pattern query)))
      (if success
          (prove-query resove newbind)
          (fail)))))

(define (prove-query query bind)
  (if (pair? query)
      (case (car query)
        ((and) (prove-and (cdr query) bind))
        ((or)  (prove-or  (cdr query) bind))
        ((not) (prove-not (cdr query) bind))
        (else (prove-simple query bind)))
      (prove-simple query bind)))

(define (prove-and queries bind)
  (fold prove-simple queries))

(define (prove-or queries bind)
  (prove-simple (amb queries) bind))

(define (prove-not query bind)
  (let ((checkpoint (save-backtrack)))
    (clear-backtrack)
    (amb (let-values (((newbind success) (match query bind)))
           (when success
             (restore-backtrack checkpoint)
             (fail)))
         (begin (restore-backtrack checkpoint)
                bind)))

(define (prove-simple query bind)
  (let ((r (amb rules)))
    (implies r query bind)))


(define-syntax push-last ()
  (syntax-rules
      ((push-last sym val)
       (set! sym (append sym (list val))))))


(define-syntax <-
  (syntax-rules
   ((<- pattern) (push-last rules (cons pattern '())))
   ((<- pattern rule) (push-last rules (cons pattern rule)))
   ((<- pattern rule ...) (push-last rules (cons pattern (and rule ...))))))

(define (change-vars* rule table)
  (define (recur rule)
    (cond ((pair? rule) (if (eq (car rule) 'quote)
                            rule
                            (recur rule)))
          ((symbol? rule) (assoc rule table))
          (else rule))))

(define (fullbind x bind)
  (let ((y (assq x bind)))
    (and y (or (fullbind (cdr y) bind) (cdr y)))))

(define-syntax bind-query ()
  (ir-macro-transformer
   (let ((query (cadr form))
         (body  (cddr form))
         (vars  (collect-vars query)))
     (lambda (form r compare)
       `(begin (init-backtrack)
               (let* ((vars  (collect-vars query))
                      (table (map (lambda (v) (list v (genvar)))
                                  vars)))
                 (let-values ((bind success)
                              (prove-query (chage-vars* query table) '()))
                   (let ,(map (lambda (v) `(,v (fullbind (assoc ',v table) bind)))
                              vars)
                     ,@body))))))))
