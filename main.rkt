#lang racket

;; Project 3: Metacircular interpreter for Scheme
;; CIS352 -- Spring '25

(provide interp-ce)

; Your task is to write a CE interpreter for a substantial subset of Scheme/Racket.
; A CE interpreter is meta-circular to a large degree (e.g., a conditional in the target
; language (scheme-ir?) can be implemented using a conditional in the host language (Racket),
; recursive evaluation of a sub-expression can be implemented as a recursive call to the
; interpreter, however, it's characterized by creating an explicit closure value for lambdas
; that saves its static environment (the environment when it's defined). For example, a CE
; interpreter for the lambda calculus may be defined:
(define (interp-ce-lambda exp [env (hash)])
  (match exp
         [`(lambda (,x) ,body)
          ; Return a closure that pairs the code and current (definition) environment
          `(closure (lambda (,x) ,body) ,env)]
         [`(,efun ,earg)
          ; Evaluate both sub-expressions
          (define vfun (interp-ce-lambda efun env))
          (define varg (interp-ce-lambda earg env))
          ; the applied function must be a closure
          (match-define `(closure (lambda (,x) ,body) ,env+) vfun)
          ; we extend the *closure's environment* and interp the body
          (interp-ce-lambda body (hash-set env+ x varg))]
         [(? symbol? x)
          ; Look up a variable in the current environment
          (hash-ref env x)]))

; Following is a predicate for the target language you must support. You must support any
; syntax allowed by scheme-ir that runs without error in Racket, returning a correct value..
(define (scheme-ir? exp)
  ; You should support a few built-in functions bound to the following variables at the top-level
  (define (prim? s) (member s '(+ - * = equal? list cons car cdr null?)))
  (match exp
         [`(lambda ,(? (listof symbol?)) ,(? scheme-ir?)) #t] ; fixed arguments lambda
         [`(lambda ,(? symbol?) ,(? scheme-ir?)) #t] ; variable argument lambda
         [`(if ,(? scheme-ir?) ,(? scheme-ir?) ,(? scheme-ir?)) #t]
         [`(let ([,(? symbol?) ,(? scheme-ir?)] ...) ,(? scheme-ir?)) #t]
         [`(let* ([,(? symbol?) ,(? scheme-ir?)] ...) ,(? scheme-ir?)) #t]
         [`(and ,(? scheme-ir?) ...) #t]
         [`(or ,(? scheme-ir?) ...) #t]
         [`(apply ,(? scheme-ir?) ,(? scheme-ir?)) #t]
         [(? (listof scheme-ir?)) #t]
         [(? prim?) #t]
         [(? symbol?) #t]
         [(? number?) #t]
         [(? boolean?) #t]
         [''() #t]
         [_ #f]))


; Interp-ce must correctly interpret any valid scheme-ir program and yield the same value
; as DrRacket, except for closures which must be represented as `(closure ,lambda ,environment).
; (+ 1 2) can return 3 and (cons 1 (cons 2 '())) can yield '(1 2). For programs that result in a
; runtime error, you should return `(error ,message)---giving some reasonable string error message.
; Handling errors and some trickier cases will give bonus points.
(define (interp-ce exp)
  (define starting-env
    (hash
     'and    `(closure (lambda l (apply-prim and l))    ,(hash))
     '+      `(closure (lambda l (apply-prim + l))      ,(hash))
     '-      `(closure (lambda l (apply-prim - l))      ,(hash))
     '*      `(closure (lambda l (apply-prim * l))      ,(hash))
     '=      `(closure (lambda l (apply-prim = l))      ,(hash))
     'equal? `(closure (lambda l (apply-prim equal? l)) ,(hash))
     'list   `(closure (lambda l (apply-prim list l))   ,(hash))
     'cons   `(closure (lambda l (apply-prim cons l))   ,(hash))
     'car    `(closure (lambda l (apply-prim car l))    ,(hash))
     'cdr    `(closure (lambda l (apply-prim cdr l))    ,(hash))
     'null?  `(closure (lambda l (apply-prim null? l))  ,(hash))))

  ;; Extend an environment with a list of parameters and corresponding arguments.
  (define (extend-env env params args)
    (if (not (= (length params) (length args)))
        (error "Arity mismatch in function application")
        (extend-env-helper env params args)))

  (define (extend-env-helper env params args)
    (if (null? params)
        env
        (extend-env-helper (hash-set env (first params) (first args))
                           (rest params)
                           (rest args))))

  (define (apply-closure f arg-vals)
    (match f
      [`(closure (lambda ,params ,body) ,env)
       (if (list? params)
           (interp body (extend-env env params arg-vals))
           (interp body (hash-set env params arg-vals)))]
      [else (error "Attempting to call non-function" f)]))

  (define (interp e env)
    (match e
      ;; Variable lookup.
      [(? symbol? x)
       (hash-ref env x (λ ()
                         (error (string-append "Unbound variable: ~a" (symbol->string x)))))]

      [`(define ,name ,value)
       (let* ([dummy (error "Uninitialized recursive binding")]
              [new-env (hash-set env name dummy)]
              [rec-val (interp value new-env)])
         (hash-set new-env name rec-val)
         rec-val)]

      ;; Lambda abstraction.
      [`(lambda ,params ,body) `(closure ,e ,env)]

      ;; Built-in primitive application.
      [`(apply-prim ,p ,lst)
       (apply (eval p (make-base-namespace))
              (interp lst env))]

      ;; Numbers and booleans evaluate to themselves.
      [(? number?) e]
      [(? boolean?) e]

      ;; Quoted expressions.
      [`(quote ,q) q]
      [''() '()]

      ;; if expressions.
      [`(if ,cond ,then ,else)
       (if (interp cond env)
           (interp then env)
           (interp else env))]

      ;; and expressions.
      [`(and) #t]
      [`(and ,e0 ,es ...)
       (if (interp e0 env)
           (interp `(and ,@es) env)
           #f)]

      ;; or expressions.
      [`(or) #f]
      [`(or ,e0 ,es ...)
       (let ([v (interp e0 env)])
         (if v v (interp `(or ,@es) env)))]

      ;; let: desugar to lambda application.
      [`(let ,bindings ,body)
       (interp `((lambda ,(map first bindings) ,body)
                  ,@(map second bindings))
               env)]

      ;; let*: sequential binding.
      [`(let* ,bindings ,body)
       (interp
        (if (null? bindings)
            body
            (let loop ([bs bindings])
              (if (null? (cdr bs))
                  `(let ((,(caar bs) ,(cadar bs)))
                     ,body)
                  `(let ((,(caar bs) ,(cadar bs)))
                     ,(loop (cdr bs))))))
        env)]

      ;; map expressions.
      [`(map ,fun ,lst)
       (let* ([f (interp fun env)]
              [lst-val (interp lst env)])
         (if (list? lst-val)
             (let loop ([lst lst-val] [result '()])
               (if (null? lst)
                   (reverse result)
                   (loop (rest lst)
                         (cons (apply-closure f (list (first lst))) result))))
             (error "map: second argument is not a list")))]

      ;; apply expression: supports builtin apply.
      [`(apply ,fun ,args ... ,lst)
       (let* ([f (interp fun env)]
              [fixed-args (map (λ (arg) (interp arg env)) args)]
              [list-args (interp lst env)]
              [all-args (append fixed-args list-args)])
         (match f
           [`(closure (lambda ,params ,body) ,env+)
            (if (list? params)
                (interp body (extend-env env+ params all-args))
                (interp body (hash-set env+ params all-args)))]
           [else (error "Attempting to call non-function" f)]))]

      ;; Function application.
      [`(,fun ,args ...)
       (let ([f (interp fun env)]
             [arg-vals (map (λ (arg) (interp arg env)) args)])
         (apply-closure f arg-vals))]

      [else (error "Unknown expression type" e)]))

  (interp exp starting-env))
