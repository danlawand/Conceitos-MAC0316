#lang plai-typed


; Basic expressions
(define-type ExprC
  [numC  (n : number)]
  [idC   (s : symbol)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [methodC (nome : symbol) (par : symbol) (exp : ExprC)]
  [ifC   (c : ExprC) (y : ExprC) (n : ExprC)]
  [seqC  (e1 : ExprC) (e2 : ExprC)]
  [setC  (var : symbol) (arg : ExprC)]
  [letC  (name : symbol) (arg : ExprC) (body : ExprC)]
  [classC  (pai : symbol) (var : symbol) (m1 : ExprC) (m2 : ExprC)]
  [newC (nome : symbol) (valor : ExprC)]
  )


; Sugared expressions
(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [methodS (nome : symbol) (par : symbol) (exp : ExprS)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [seqS    (e1 : ExprS) (e2 : ExprS)]
  [setS    (var : symbol) (arg : ExprS)]
  [letS    (name : symbol) (arg : ExprS) (body : ExprS)]
  [classS  (pai : symbol) (var : symbol) (m1 : ExprS) (m2 : ExprS)]
  [newS    (nome : symbol) (valor : ExprS)]
  )


; Removing the sugar
(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)         (numC n)]
    [idS     (s)         (idC s)]
    [methodS (n p e)     (methodC n p (desugar e))]
    [plusS   (l r)       (plusC (desugar l) (desugar r))]
    [multS   (l r)       (multC (desugar l) (desugar r))]
    [bminusS (l r)       (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)         (multC (numC -1) (desugar e))]
    [ifS     (c s n)     (ifC (desugar c) (desugar s) (desugar n))]
    [seqS    (e1 e2)     (seqC (desugar e1) (desugar e2))]
    [setS    (var expr)  (setC  var (desugar expr))]
    [letS    (n a b)     (letC n (desugar a) (desugar b))]
    [classS  (p v m1 m2) (classC p v (desugar m1) (desugar m2))]
    [newS    (n v)       (newC n (desugar v))]
    ))


; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  [methodV (nome : symbol)(par : symbol) (exp : ExprC)]
  [classV (pai : symbol) (var : symbol) (m1 : Value) (m2 : Value)]
  [objectV (classe : Value) (env : Env)]
  )


; Bindings associate symbol with location
(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])

; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)
(define global-env (extend-env (bind 'Object (box (classV 'Object 'alan (numV 0) (numV 0)))) mt-env))

; Find the name of a variable
(define (lookup [for : symbol] [env : Env]) : (boxof Value)
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string for) " was not found"))] ; variable is undefined
            [else (cond
                  [(symbol=? for (bind-name (first env)))   ; found it!
                                 (bind-val (first env))]
                  [else (lookup for (rest env))])]))        ; check in the rest


; Auxiliary operators
(define (num+ [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "One of the arguments is not a number")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "One of the arguments is not a number")]))

; Interpreter
(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
    ; Numbers just evaluta to their equivalent Value
    [numC (n) (numV n)]

    ; IDs are retrieved from the Env and unboxed
    [idC (n) (unbox (lookup n env))]

    [methodC (nome a b) (methodV nome a b)]


    ; Sum two numbers using auxiliary function
    [plusC (l r) (num+ (interp l env) (interp r env))]

    ; Multiplies two numbers using auxiliary function
    [multC (l r) (num* (interp l env) (interp r env))]

    ; Conditional operator
    [ifC (c s n) (if (zero? (numV-n (interp c env))) (interp n env) (interp s env))]

    ; Sequence of operations
    [seqC (b1 b2) (begin (interp b1 env) (interp b2 env))] ; No side effect between expressions!

    ; Attribution of variables
    [setC (var val) (let ([b (lookup var env)])
                      (begin (set-box! b (interp val env)) (unbox b)))]

    ; Declaration of variable
    [letC (name arg body)
          (let* ([new-bind (bind name (box (interp arg env)))]
                 [new-env (extend-env new-bind env)])
            (interp body new-env))]

    [classC (pai var m1 m2)
            (classV pai var (interp m1 env) (interp m2 env))]

    [newC (nome valor)
          (objectV (unbox (lookup nome env)) env)]
    ))


; Parser
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(seq) (seqS (parse (second sl)) (parse (third sl)))]
         [(:=) (setS (s-exp->symbol (second sl)) (parse (third sl)))]
         [(let) (letS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                      (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                      (parse (third sl)))]
         [(method) (methodS (s-exp->symbol (second sl))
                            (s-exp->symbol (third sl))
                            (parse (fourth sl)))]
         [(class) (classS (s-exp->symbol (second sl))
                         (s-exp->symbol (third sl))
                         (parse (fourth sl))
                         (parse (fourth (rest sl)))
                         )]
         [(new) (newS (s-exp->symbol (second sl))
                      (parse (third sl)))]
         
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) global-env))


