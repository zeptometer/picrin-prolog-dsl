(define-library (prolog core)
  (import (scheme base))
  (import (scheme cxr))
  (import (picrin amb))
  (import (srfi 1))

  ;;; matching
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

  ;;; prolog core
  ;; rules :: (((var-symbol ...) pattern rule) ...)
  (define rules '())

  ;; prolog variable
  (define-record-type variable
    (genvar)
    var?)

  ;; extract var-symbols from rule
  (define (collect-vars rule)
    (define (recur rule)
      (cond ((pair? rule) (if (eq (car rule) 'quote)
                              '()
                              (append (collect-vars (car rule))
                                      (collect-vars (cdr rule)))))
            ((symbol? rule) rule)
            (else '())))
    (delete-duplicates (recur rule)))

  ;; replace var-symbol with var
  (define (change-vars rule table)
    (define (recur rule)
      (cond ((pair? rule)
             (cond ((eq (car rule 'quote)) (cdr rule))
                   ((eq (car rule 'quasiquote)) (cdr rule))
                   ((eq (car rule 'unquote)) rule))

             (if (eq (car rule) 'quote)
                 rule
                 (recur rule)))
            ((symbol? rule) (assoc rule table))
            (else rule))))

  ;;; implication logic
  (define (implies r query bind)
    (let* ((table   (map (lambda (v) (list v (genvar))) (car r)))
           (pattern (change-vars (cadr r)  table))
           (rule    (change-vars (caddr r) table)))
      (let-values (((newbind success) (match pattern query)))
        (if success
            (prove-query rule newbind)
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
    (fold prove-simple queries bind))

  (define (prove-or queries bind)
    (prove-simple (amb queries) bind))

  (define-syntax do-amb
    (syntax-rules ()
      ((do-amb expr ...)
       ((amb (list (lambda () expr) ...))))))

  (define (prove-not query bind)
    (let ((checkpoint (save-backtrack)))
      (clear-backtrack)
      (do-amb (let-values (((newbind success) (match query bind)))
                (when success
                      (restore-backtrack checkpoint)
                      (fail)))
              (begin (restore-backtrack checkpoint)
                     bind))))

  (define (prove-simple query bind)
    (let ((r (amb rules)))
      (implies r query bind)))

  ;;; prolog interface
  (define-syntax push-last ()
    (syntax-rules
        ((push-last sym val)
         (set! sym (append sym (list val))))))

  (define-syntax <-
    (syntax-rules ()
      ((<- pattern)          (push-last rules `(,(collect-vars 'pattern) pattern ())))
      ((<- pattern rule)     (push-last rules `(,(collect-vars 'pattern) pattern rule)))
      ((<- pattern rule ...) (push-last rules `(,(collect-vars 'pattern) pattern (and rule ...))))))

  (define (fullbind x bind)
    (let ((y (assq x bind)))
      (and y (or (fullbind (cdr y) bind) (cdr y)))))

  (define-syntax with-query
    (ir-macro-transformer
     (let* ((query (cadr form))
            (body  (cddr form))
            (vars  (collect-vars query))
            (table (map (lambda (v) (list v (genvar))))))
       (lambda (form r compare)
         `(begin (init-backtrack)
                 (let-values ((bind success)
                              (prove-query `,(chage-vars* query table) '()))
                   (let ,(map (lambda (v) `(,v (fullbind ,(assoc v table) bind)))
                              vars)
                     ,@body)))))))
  
  (export <- with-query))
