#lang plai-typed
; este interpretador aumenta o closureTyped para incluir
; cons, car, cdr, valor nulo (descrito como  ())
; e display
; display imprime o valor passado seguido de um ";". Nao mudamos de linha 

; Basic expressions
(define-type ExprC
  [numC  (n : number)]
  [idC   (s : symbol)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [lamC  (arg : symbol) (body : ExprC)]
  [appC  (fun : ExprC) (arg : ExprC)]
  [ifC   (c : ExprC) (y : ExprC) (n : ExprC)]
  [seqC  (e1 : ExprC) (e2 : ExprC)]
  [letC  (name : symbol) (arg : ExprC) (body : ExprC)]
  [let*C  (name1 : symbol) (arg1 : ExprC) (name2 : symbol) (arg2 : ExprC) (body : ExprC)]
  [letrecC (f : symbol) (e : ExprC) (expr : ExprC)]
  [consC (car : ExprC) (cdr : ExprC)]
  [carC  (cell : ExprC) ]
  [cdrC (cell : ExprC)]
  [displayC (exp : ExprC)]
  [quoteC  (sym : symbol)]
  [equalC (a : ExprC) (b : ExprC)]
  [nullC  ]
  )


; Sugared expressions
(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [lamS    (arg : symbol) (body : ExprS)]
  [appS    (fun : ExprS) (arg : ExprS)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [seqS    (e1 : ExprS) (e2 : ExprS)]
  [letS    (name : symbol) (arg : ExprS) (body : ExprS)]
  [let*S   (name1 : symbol) (arg1 : ExprS) (name2 : symbol) (arg2 : ExprS) (body : ExprS)]
  [letrecS (f : symbol) (e : ExprS) (expr : ExprS)]
  [consS (car : ExprS) (cdr : ExprS)]
  [carS (cell : ExprS) ]
  [cdrS (cell : ExprS)]
  [displayS (exp : ExprS)]
  [quoteS  (sym : symbol)]
  [equalS (a : ExprS) (b : ExprS)]
  [nullS ]
 )


; Removing the sugar
(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)        (numC n)]
    [idS     (s)        (idC s)]
    [lamS    (a b)      (lamC a (desugar b))]
    [appS    (fun arg)  (appC (desugar fun) (desugar arg))]
    [plusS   (l r)      (plusC (desugar l) (desugar r))]
    [multS   (l r)      (multC (desugar l) (desugar r))]
    [bminusS (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)        (multC (numC -1) (desugar e))]
    [ifS     (c s n)    (ifC (desugar c) (desugar s) (desugar n))]
    [seqS    (e1 e2)    (seqC (desugar e1) (desugar e2))]
    [letS    (n a b)    (letC n (desugar a) (desugar b))]
    [let*S   (n a m b c)  (let*C n (desugar a) m (desugar b) (desugar c))]
    [letrecS (f e expr) (letrecC f (desugar e) (desugar expr))]
    [consS   (car cdr) (consC (desugar car) (desugar cdr))]
    [carS    (exp)     (carC (desugar  exp)) ]
    [cdrS    (exp)     (cdrC (desugar  exp)) ]
    [displayS (exp)    (displayC (desugar exp))]
    [quoteS (sym) (quoteC sym)]
    [equalS (a b) (equalC (desugar a) (desugar b))]
    [nullS  () (nullC)]
    ))


; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  [nullV ]
  [quoteV (symb : symbol)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [cellV (first : Value) (second : Value)]
  [suspV (body : ExprC) (env : Env)]
  )

(define (strict [v : Value]) : Value
  (type-case Value v
    [numV (n) v]
    [nullV () v]
    [quoteV (s) v]
    [closV (a b e) v]
    [cellV (f s) v]
    [suspV (b e) (strict (interp b e))]
    ))


; Bindings associate symbol with location
(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])

; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


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

    ; Lambdas evaluate to closures, which save the environment
    [lamC (a b) (closV a b env)]

    ; Application of function
    [appC (f a)
          (let ([f-value (strict(interp f env))])
            (interp (closV-body f-value)
                    (extend-env
                        (bind (closV-arg f-value) (box (suspV a env)))
                        (closV-env f-value)
                    )))]

    
    ; Sum two numbers using auxiliary function
    [plusC (l r) (num+ (strict (interp l env))
                   (strict (interp r env)))]
    
    ; Multiplies two numbers using auxiliary function
    [multC (l r) (num* (strict (interp l env))
                   (strict (interp r env)))]
    
    ; Conditional operator
    [ifC (c s n) (if (zero? (numV-n (strict (interp c env)))) (strict (interp n env)) (strict (interp s env)))]


    ; Sequence of operations
    [seqC (b1 b2) (begin (interp b1 env) (interp b2 env))] ; No side effect between expressions!

    
    ; Declaration of variable
    [letC (name arg body)
          (let* ([new-bind (bind name (box (suspV arg env)))]
                 [new-env (extend-env new-bind env)])
            (interp body new-env))]
    
    [let*C (name1 arg1 name2 arg2 body)
           (let* ([new-bind (bind name1 (box (suspV arg1 env)))]
                  [new-env (extend-env new-bind env)]
                  [new-bind1 (bind name2 (box (suspV arg2 new-env)))]
                  [new-env1 (extend-env new-bind1 new-env)]
                  )
               (interp body new-env1))]

    [letrecC (f e expr)
             (let* ( [new-bind (bind f (box (interp (quoteC 'al) env)))]
                     [new-env (extend-env new-bind env)])
                     (let ([b (lookup f new-env)])(begin (set-box! b (suspV e new-env)) (interp expr new-env))))]
    
    ; Cell operations
    [consC (car cdr)
           (cellV (suspV car env) (suspV cdr env))]
    [carC  (exp) (cellV-first (strict (interp exp env)))]
    [cdrC  (exp) (cellV-second (strict (interp exp env)))]
    
    ;Display values
    [displayC (exp) (let ((value (interp exp env)))
                      (begin (print-value value)
                             (display "\n") ; one value per line in our version of display
                             value))]
    ;Symbol
    [quoteC (sym) (quoteV sym)]

    ;Equal
    [equalC (a b) (if (equal? (strict (interp a env)) (strict (interp b env)))
                       (numV 1)
                       (numV 0))]
    
    ;Null
    [nullC  () (nullV)]
    
    ))


; Parser
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (if (empty? sl)
           (nullS)
           (case (s-exp->symbol (first sl))
             [(+) (plusS (parse (second sl)) (parse (third sl)))]
             [(*) (multS (parse (second sl)) (parse (third sl)))]
             [(-) (bminusS (parse (second sl)) (parse (third sl)))]
             [(~) (uminusS (parse (second sl)))]
             [(lambda) (lamS (s-exp->symbol (second sl)) (parse (third sl)))] ; definição
             [(call) (appS (parse (second sl)) (parse (third sl)))]
             [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
             [(seq) (seqS (parse (second sl)) (parse (third sl)))]
             [(let) (letS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                          (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                          (parse (third sl)))]

             [(let*) (let*S (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                        (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                        (s-exp->symbol (first (s-exp->list (second (s-exp->list (second sl))))))
                        (parse (second (s-exp->list (second (s-exp->list (second sl))))))
                        (parse (third sl)))]
             [(letrec) (letrecS (s-exp->symbol(first (s-exp->list (first (s-exp->list (second sl))))))
                            (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                            (parse (third sl)))]
             
             [(cons) (consS (parse (second sl)) (parse (third sl)))]
             [(car) (carS (parse (second sl)))]
             [(cdr) (cdrS (parse (second sl)))]
             [(display)(displayS (parse (second sl)))]
             [(quote) (quoteS (s-exp->symbol (second sl)))]
             [(equal?) (equalS (parse (second sl)) (parse(third sl)))]
             [else (error 'parse "invalid list input")])))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) mt-env))

; Printing
(define (print-value [value : Value ] ) : void
                      
                      (type-case Value value
                        [numV  (n) (display n)]
                        [quoteV (symb) (display symb)]
                        [closV (arg body env)
                               (begin (display "<<")
                                      (display "lambda(")
                                      (display arg)
                                      (display ")")
                                      (print-exp body)
                                      (display ";")
                                      (print-environment env)
                                      (display ">>"))]
                        
                        [cellV (first second)
                               (begin (display "(")
                                      (print-list value)
                                      (display ")")
                                      )
                               ]
                        [nullV ()
                               (display '())]
                        [suspV (b e)
                               (begin (display "<|")
                                      (print-exp b)
                                      (display ",")
                                      (print-environment e)
                                      (display "|>"))]
                        ))




(define (print-list cell) : void
  (begin 
         (print-value (cellV-first cell))
         (display " ")
         (let ([rest (cellV-second cell)])
           (type-case Value rest 
             [nullV () (display "") ]; null at the end of the list is not printed
             [cellV (first second) (print-list rest)]
             [else (begin (display ".")
                        (print-value rest))]))
         )
  )
(define (print-exp [exp : ExprC]) : void
  (type-case ExprC exp
    [plusC (a b) (begin (display "(")
                        (display "+ ")
                        (print-exp a)
                        (display " ")
                        (print-exp b)
                        (display ")"))]
    [multC (a b) (begin (display "(")
                        (display "* ")
                        (print-exp a)
                        (display " ")
                        (print-exp b)
                        (display ")"))]
    [lamC (param body) (begin (display "(")
                        (display "lambda ")
                        (display param)
                        (display " ")
                        (print-exp body)
                        (display ")"))]
    [numC  (n) (display n)]
    [idC   (id)(display id)]
    [appC  (fun arg) (begin (display "(")
                            (print-exp fun)
                            (display " ")
                            (print-exp arg)
                            (display ")"))]
    [ifC   (c y n)
           (begin (display "(if ")
                  (print-exp c)
                  (display " ")
                  (print-exp y)
                  (display " ")
                  (print-exp n)
                  (display ")"))]
    [seqC  (e1 e2 )
                      (begin (display "(seq ")
                             (print-exp e1)
                             (display " ")
                             (print-exp e2)
                             (display ")"))]


    [letC  (name arg body) 
           (begin (display "(let (( ")
                  (display name)
                  (display " ")
                  (print-exp arg)
                  (display "))")
                  (print-exp body))]
    
    [let*C (name1 arg1 name2 arg2 body)
           (begin (display "(let* (( ")
                  (display name1)
                  (display " ")
                  (print-exp arg1)
                  (display ") (")
                  (display name2)
                  (display " ")
                  (print-exp arg2)
                  (display "))")
                  (print-exp body))]

     [letrecC (f e expr)
           (begin (display "(letrec ( ")
                  (display f)
                  (display " ")
                  (print-exp e)
                  (display "))")
                  (print-exp expr))]
    
    [consC (car cdr)
           (begin (display "(cons ")
                  (print-exp car)
                  (display " ")
                  (print-exp cdr)
                  (display ")"))]
    [carC  (cell)
           (begin (display "(car ")
                  (print-exp cell)
                  (display ")"))]
    [cdrC  (cell)
           (begin (display "(cdr ")
                  (print-exp cell)
                  (display ")"))]
    [displayC  (expr)
               (begin (display "(display ")
                      (print-exp expr)
                      (display ")"))]
    
    [quoteC  (sym)
             (begin (display "(quote ")
                      (display sym)
                      (display ")"))]

    [equalC (a b) (begin (display "(equal ")
                  (print-exp a)
                  (display " ")
                  (print-exp b)
                  (display ")"))]

    
   
    [nullC  () (display "()")]
  ))

(define (print-environment [environment : Env])
  (begin 
    (display "{")
    (print-binding-list environment)
    (display "}")
  )
  )
(define (print-binding-list binding-list)
  (if (empty? binding-list)
      (display ""); nothing to be printed
      (begin 
        (display (bind-name (first binding-list)))
        (display "->")
        (print-value (unbox (bind-val (first binding-list))))
        (display ";")
        (print-binding-list (rest binding-list))
        )
      )
  )
 
   

; Exemplos

; o proximo é uma lista que nao termina em celular "null"
(interpS '(display (cons 1 (cons (quote a) (cons 5 6)))))
;agora uma lista "normal" onde o cdr da ultima celular é nulo
(interpS '(display (cons 1 (cons 2 (cons 3 ())))))
(interpS '(display (lambda x (+ x 2))))
(interpS '(display (call (lambda y (lambda x (+ x y))) 5)))
; display de closV
(interpS '(display (call (lambda y (lambda x (+ x y))) 5)))



; testando let
(test (interpS '(let ([x 10]) (+ x x)))
      (numV 20))

; testando let*
(test (interpS '(let* ([x 10]  [y 20]) (+ x y)))
      (numV 30))

; testando letrec
(test (interpS '(letrec ([fac (lambda n (if n (* n (call fac (- n 1))) 1))])
                  (call fac 5)))
      (numV 120))


(test (interpS '(equal? 1 2))
      (numV 0))

(test (interpS '(equal? 1 1))
      (numV 1))

