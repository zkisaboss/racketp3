#lang racket

(provide interp-ce)

(define (interp-ce exp)
  (define (interp env exp)
    (match exp
      ;; Numbers and booleans evaluate to themselves.
      [(? number?) exp]
      [(? boolean?) exp]

      ;; Desugar let into a lambda application.
      [`(let ([,xs ,rhss] ...) ,body)
       (interp env
               (append (list (list 'lambda xs body))
                       (map (lambda (rhs) (interp env rhs)) rhss)))]

      ;; Lambda expressions.
      [`(lambda ,params ,body)
       `(closure (lambda ,params ,body) ,env)]

      ;; Variables: look them up in the environment.
      [(? symbol? x)
       (hash-ref env x (lambda ()
                         `(error ,(string-append "Unbound variable: " (symbol->string x)))))]

      ;; if expressions: evaluate the condition then branch accordingly.
      [`(if ,ge ,te ,fe)
       (if (interp env ge) (interp env te)
           (interp env fe))]

      ;; Primitive operations clause (unused in my code).
      [`(apply-prim ,op ,x)
       (let ([op-proc (eval op)]
             [arg-val (interp env x)])
         (op-proc arg-val))]

      ;; Function application for known binary primitives.
      [`(,op ,e0 ,e1)
       ((match op
          ['+ +]
          ['- -]
          ['* *]
          [else (error "Unknown operator" op)])
        (interp env e0)
        (interp env e1))]

      [`(,ef ,ea)
       (define clo-for-ef (interp env ef))
       (match clo-for-ef
         [`(closure (lambda (,x) ,e-b) ,env+)
          (let ([v (interp env ea)])
            (interp (hash-set env+ x v) e-b))])]))

  (define starting-env (hash))
  (interp starting-env exp))
