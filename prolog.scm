(import (scheme base))
(import (scheme cxr))
(import (picrin macro))
(import (picrin amb))
(import (srfi 1))

;; prolog variable
(define-record-type variable
  (genvar)
  var?)

  ;;; matching
(define (binding x bind)
  (define (recbind x bind)
    (let ((y (assq x bind)))
      (and y (or (recbind (cadr y) bind) (cadr y)))))
  
  (recbind x bind))

(define (match l r bind)
  (write 'match) (display " ") (write l) (display " ") (write r) (newline)
  (cond ((or (eqv? l r) (eq? l '_) (eq? r '_)) (values bind #t))
	((binding l bind) => (lambda (nl) (match nl r bind)))
	((binding r bind) => (lambda (nr) (match l nr bind)))
	((var? l) (newline) (values `((,l ,r) ,@bind) #t))
	((var? r) (newline) (values `((,r ,l) ,@bind) #t))
	((and (pair? l) (pair? r))
	 (let-values (((bind success) (match (car l) (car r) bind)))
	   (if success
	       (match (cdr l) (cdr r) bind)
	       (values 'fail #f))))
	(else (values 'fail #f))))

  ;;; prolog core
;; rules :: (((var-symbol ...) pattern rule) ...)
(define rules '())

(import (scheme write))
;; extract var-symbols from rule
(define (collect-vars rule)
  (define (recur rule)
    (cond ((pair? rule) (if (eq? (car rule) 'quote)
			    '()
			    (append (recur (car rule))
				    (recur (cdr rule)))))
	  ((symbol? rule) (list rule))
	  (else '())))

  (delete-duplicates (recur (cdr rule))))

;; replace var-symbol with var
(define (change-vars rule table)
  (cond ((pair? rule)
	 (cond ((eq? (car rule) 'quote) (cadr rule))
	       ((eq? (car rule) 'quasiquote) (cadr rule))
	       ((eq? (car rule) 'unquote) rule)
	       (else (cons (change-vars (car rule) table)
			   (change-vars (cdr rule) table)))))
	((symbol? rule) (let ((v (assoc rule table)))
			  (if v (cadr v) rule)))
	(else rule)))

  ;;; implication logic
(define (prove-query query bind)
  (letrec ((implies (lambda (r query bind)
		      (let* ((table   (map (lambda (v) (list v (genvar))) (car r)))
			     (pattern (change-vars (cadr r)  table))
			     (rule    (change-vars (caddr r) table)))
			(let-values (((newbind success) (match pattern query bind)))
			  (display "bind ") (write newbind) (newline)
			  (if success
			      (prove-query rule newbind)
			      (fail))))))
	   (prove-and (lambda (query bind)
			(fold prove-query bind query)))
	   (prove-or (lambda (queries bind)
		       (prove-query (amb queries) bind)))
	   (prove-not (lambda (query bind)
			(let ((checkpoint (save-backtrack)))
			  (clear-backtrack)
			  (do-amb (let-values (((newbind success) (prove-query query bind)))
				    (when success
					  (restore-backtrack checkpoint)
					  (fail)))
				  (begin (restore-backtrack checkpoint)
					 bind)))))
	   (prove-simple (lambda (query bind)
			   (let ((r (amb rules)))
			     (implies r query bind)))))

    (cond ((pair? query) (case (car query)
			   ((and) (prove-and (cdr query) bind))
			   ((or)  (prove-or  (cdr query) bind))
			   ((not) (prove-not (cdr query) bind))
			   (else  (prove-simple query bind))))
	  (else (prove-simple query bind)))))

  ;;; prolog interface
(define-syntax push-last
  (syntax-rules ()
      ((push-last sym val)
       (set! sym (append sym (list val))))))

(define-syntax <-
  (er-macro-transformer
   (lambda (form r compare)
     (let ((pattern (cadr form))
	   (resolve (cddr form)))
       `(,(r 'push-last) ,(r 'rules)
	 '(,(collect-vars pattern)
	   ,pattern
	   (and ,@resolve)))))))

(define (fullbind x bind)
  (cond ((var? x) (let ((y (binding x bind)))
		    (if y (fullbind y bind) (gensym))))
	((pair? x) (cons (fullbind (car x) bind)
			 (fullbind (cdr x) bind)))
	(else x)))

(define (tee hoge)
  (write hoge) (newline)
  hoge)

(define-syntax with-query
  (er-macro-transformer 
   (lambda (form r compare)
     (let* ((query (cadr form))
	    (body  (cddr form))
	    (vars  (collect-vars query))
	    (table (map (lambda (v) (list v (genvar))) vars))
	    (_begin (r 'begin))
	    (_clear-backtrack (r 'clear-backtrack))
	    (_let (r 'let))
	    (_fullbind (r 'fullbind)))
       `(,_begin (,_clear-backtrack)
		 (,_let ((bind
			  (prove-query (,'quasiquote ,(change-vars query table)) '())))
			(,_let ,(map (lambda (p) `(,(car p) (,_fullbind ',(cadr p) bind)))
				     table)
			       ,@body)))))))


;; (begin@3 (clear-backtrack@2255)
;; 	 (let@278 ((bind (prove-query `(parent #3=#(#0=(record-marker) #2=#(#0# #1=#(#0# #1# record-type% (name field-tags)) variable ())) #4=#(#0# #2#)) '())))
;; 		  (let@278 ((x (fullbind@2354 '#3# bind))
;; 			    (y (fullbind@2354 '#4# bind)))
;; 			   (display x) (display y) (newline))))
