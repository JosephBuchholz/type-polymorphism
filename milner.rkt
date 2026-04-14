#lang racket

;; See Milner's paper: https://doi.org/10.1016/0022-0000(78)90014-4

;; Examples:
;; Let polymorphism example. Final type should be something like this: ((Bool -> t) t)
#;(W-alg '(let ([I (λ (x) x)])                                    
            (λ (y) ((I y) (I #t)))))

;; Lambda calculus program with let polymorphism:
;; #t | #f
;; x
;; (e e)
;; (λ (x) e)
;; (let ([x e]) b)

;; Program with types:
;; [#t : Bool]
;; [x : t]
;; [([e : t] [e : t]) : t]
;; [(λ (x : t) [e : t]) : t]
;; [(let ([[x : t] [e : t]]) [b : t]) : t]

(struct base-type
  [name]
  #:transparent)

;; A Type is either a base-type or a type variable or a (Type -> Type)

;; A representation of a prefix
(struct binding
  [form      ;; λ, fix, or let
   type
   type-env] ;; A type env local to this binding (i.e. keeps
             ;; track of all bindings above this binding: this
             ;; is for determining whether a variable is generic
             ;; or not)
  #:transparent)

;; TypedProgram -> Type
(define (get-type typed-exp)
  (match typed-exp
    [`(,x : ,t)
      t]
    [_ (error 'get-type-missing-case)]))

;; A Substitution is a (HashOf Type Type)

;; Substitution Type -> Type
(define (apply-sub S type)
  (match type
    [(or (? symbol? x) (? base-type? x))
      (if (hash-has-key? S x)
        (hash-ref S x)
        x)]
    [`(,x -> ,y)
      `(,(apply-sub S x) -> ,(apply-sub S y))]))

;; Substitution (HashOf Var Binding) -> (HashOf Var Binding)
(define (apply-sub/type-env S type-env)
  (for/hash ([(var bind) type-env])
    (values var (apply-sub/binding S bind))))

;; Substitution Binding -> Binding
(define (apply-sub/binding S bind)
  (define new-type (apply-sub S (binding-type bind)))
  (binding (binding-form bind) new-type (binding-type-env bind)))

;; Substitution TypedProgram -> TypedProgram
(define (apply-sub/exp S exp)
  (match exp
    [`(,x : ,t)
      `(,(apply-sub/exp S x) : ,(apply-sub S t))]
    [(? boolean? x)
      x]
    [(? symbol? x)
      x]
    [`(,d ,e)
      `(,(apply-sub/exp S d) ,(apply-sub/exp S e))]
    [`(λ (,x : ,t) ,body)
      `(λ (,x : ,(apply-sub S t))
        ,(apply-sub/exp S body))]
    [`(let ([,x : ,t] ,d) ,body)
      `(let ([[,x : ,(apply-sub S t)] ,(apply-sub/exp S d)])
        ,(apply-sub/exp S body))]
    [_ (error 'apply-sub/exp-missing-case)]))

;; Substitution Substitution -> Substitution
;; Compute substitution that is equivalent to applying R and then S
(define (apply-sub/sub S R)
  (define mod-R
    (for/hash ([(k v) R])
      (values k (apply-sub S v))))
  
  (for/fold ([SR mod-R])
            ([(k v) S])
    (if (hash-has-key? mod-R k)
      SR
      (hash-set SR k v))))

;; Type (HashOf Var Type) -> (SetOf TypeVar)
(define (get-generic-type-vars type type-env)
  (match type
    [`(,t1 -> ,t2)
      (set-union
        (get-generic-type-vars t1 type-env)
        (get-generic-type-vars t2 type-env))]
    [t1
      (define type-env-types
        (map
          (lambda (x)
            (binding-type x))
          (hash-values type-env)))
      
      (if (member type type-env-types)
        (set)
        (set t1))]))

;; Basically a gensym maker (makes outputs easier to read).
(define (make-var-generator [base 't])
  (define counter 0)
  (define base-string (symbol->string base))
  (lambda ([_ base])
    (define counter-string (number->string counter))
    (set! counter (+ counter 1))
    (string->symbol (string-append base-string
                                   counter-string))))

;; Program [(HashOf Var Binding)] -> TypedProgram
(define (W-alg f [type-env (hash)] [sym-gen (make-var-generator)])
  (define (W f type-env)
    (match f
      [(? boolean? b)
        `(,(hash) (,b : ,(base-type 'Bool)))]
      [(? symbol? x)
        (define res (hash-ref type-env x))
        (match res
          [(binding (or 'λ 'fix) type te)
            (define T (hash))
            (define f^ `(,x : ,type))

            `(,T ,f^)]
          [(binding 'let type te)
            (define generics (get-generic-type-vars type te))

            (define new-vars-sub
              (for/hash ([generic generics])
                (values generic (sym-gen))))

            (define generic-instance
              (apply-sub new-vars-sub type))

            (define T (hash))
            (define f^ `(,x : ,generic-instance))

            `(,T ,f^)])]
      [`(,d ,e)
        (match-define `(,R ,d^) (W d type-env))
        (match-define `(,S ,e^) (W e (apply-sub/type-env R type-env)))
        (define d^-type (get-type d^))
        (define e^-type (get-type e^))
        (define new-beta (sym-gen))
        
        (define U (U-alg (apply-sub S d^-type) `(,e^-type -> ,new-beta)))

        (define T (apply-sub/sub U (apply-sub/sub S R)))
        (define new-f `[(,(apply-sub/exp S d^) ,e^) : ,new-beta])
        (define f^ (apply-sub/exp U new-f))

        `(,T ,f^)]
      [`(λ (,x) ,d)
        (define type-beta (sym-gen))
        (match-define `(,R ,d^) (W d (hash-set type-env x (binding 'λ type-beta type-env))))
        (define R-beta (apply-sub R type-beta))
        (define d^-type (get-type d^))

        (define T R)
        (define f^
          `[(λ (,x : ,R-beta)
            ,d^) : (,R-beta -> ,d^-type)])
        
        `(,T ,f^)]
      [`(let ([,x ,d]) ,e)
        (match-define `(,R ,d^) (W d type-env))
        (define d^-type (get-type d^))
        (define R-type-env (apply-sub/type-env R type-env))
        (match-define `(,S ,e^) (W e (hash-set R-type-env x (binding 'let d^-type R-type-env))))
        
        (define e^-type (get-type e^))
        (define final-d (apply-sub/exp S d^))
        (define x-type (apply-sub S d^-type))

        (define T (apply-sub/sub S R))
        (define f^
          `[(let ([[,x : ,x-type] ,final-d])
              ,e^) : ,e^-type])
        
        `(,T ,f^)]))

  (W f type-env))

;; Type Type -> (or Substitution #f)
;; Robinson's unification algorithm
(define (U-alg e1 e2)
  ;; Returns disagreement if disagreement found
  ;; Returns false if disagreement not found
  (define (find-disagreement e1 e2)
    (match* (e1 e2)
      [(`(,t1 -> ,t2) `(,t3 -> ,t4))
        (define res (find-disagreement t1 t3))
        (if res
            res
            (find-disagreement t2 t4))]
      [(t1 t2)
        (if (equal? t1 t2)
          #f
          (list t1 t2))]))

  (define (occur V U)
    (match U
      [`(,t1 -> ,t2)
        (or (occur V t1) (occur V t2))]
      [t1
        (equal? V t1)]))

  (define (recur sub)
    (define e1^ (apply-sub sub e1))
    (define e2^ (apply-sub sub e2))
    (if (equal? e1^ e2^)
      sub ;; All good!
      
      (let ([disagreement (find-disagreement e1^ e2^)])
        (when (not disagreement) (error 'faulty-unification))

        (define V
          (if (symbol? (first disagreement))
            (first disagreement)
            (second disagreement)))
        (define U
          (if (equal? V (first disagreement))
            (second disagreement)
            (first disagreement)))
        
        (if (not (or (symbol? V) (base-type? V)))
          #f
          
          (if (occur V U)
            #f
            
            (recur (apply-sub/sub (hash V U) sub)))))))
  
  (recur (hash)))

;; Helper to pretty print the infered type for f.
(define (display-final-type! f)
  (define res (W-alg f))
  
  (define (pretty type)
    (match type
      [(? base-type? t)
        (base-type-name t)]
      [(? symbol? t)
        t]
      [`(,t1 -> ,t2)
        `(,(pretty t1) -> ,(pretty t2))]))
  
  (displayln (pretty (get-type (second res)))))

;; Some unit tests
(module+ test
  (require rackunit)
  
  ;; U-alg tests
  (define (test-U-sub U e1 e2)
    (define e1^ (apply-sub U e1))
    (define e2^ (apply-sub U e2))
    (displayln e1^)
    (displayln e2^)

    (equal? e1^ e2^))

  (check-equal?
    (U-alg 'x '(y -> y))
    (hash 'x '(y -> y)))

  (define e1 '(x -> (x -> x)))
  (define e2 '((y -> y) -> ((y -> y) -> (z -> z))))

  (check-equal?
    (test-U-sub (U-alg e1 e2) e1 e2)
    #t) 

  ;; W-alg tests
  (check-equal?
    (W-alg '(λ (x) (λ (y) y)))
    `(,(hash)
      ((lambda (x : t0)
        ((lambda (y : t1)
          (y : t1)) : (t1 -> t1)))
      : (t0 -> (t1 -> t1)))))
  
  (check-equal?
    (W-alg '(λ (x) (λ (y) (y x))))
    `(,(hash 't1 '(t0 -> t2))
      ((lambda (x : t0)
        ((lambda (y : (t0 -> t2)) (((y : (t0 -> t2)) (x : t0)) : t2))
         :
         ((t0 -> t2) -> t2)))
       :
       (t0 -> ((t0 -> t2) -> t2))))))