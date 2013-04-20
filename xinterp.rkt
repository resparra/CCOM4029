#lang plai-typed
;; Author : RAFAEL ESPARRA RIVERA 

(define-type Binding
  [binding (name : symbol) (named-expr : CFWAE)])

(define-type CFWAE
  [num (n : number)]
  [binop (op : symbol) (lhs : CFWAE) (rhs : CFWAE)]
  [with (lob : (listof Binding)) (body : CFWAE)]
  [id (name : symbol)]
  [if0 (c : CFWAE) (t : CFWAE) (e : CFWAE)]
  [fun (args : (listof symbol)) (body : CFWAE)]
  [app (f : CFWAE) (args : (listof CFWAE))])

(define-type Env
  [mtEnv]
  [anEnv (name : symbol) (value : CFWAE-Value) (env : Env)])

(define-type CFWAE-Value
  [numV (n : number)]
  [closureV (params : (listof symbol))
            (body : CFWAE)
            (env : Env)])

(define (one-binding sexp)
  (let ([sl (s-exp->list sexp)])
  (binding (s-exp->symbol(first sl)) (parse (second sl)))))

(define (all-binding [lsexp : (listof s-expression)])
  (if (empty? lsexp) empty
  (cons(one-binding (first lsexp)) (all-binding (rest lsexp)))))

(define (app-list [lsexp : (listof s-expression)])
  (if (empty? lsexp) empty
   (cons (parse (first lsexp))(app-list (rest lsexp)))))


(define (parse-all-symbols [ls : (listof s-expression)]) : (listof symbol)
  (if (empty? ls) empty 
      (cons (s-exp->symbol(first ls)) (parse-all-symbols (rest ls)))))

;;Crear el new env:
(define (one-env [old-env : Env] [new-env : Env]) : Env
  (if (mtEnv? old-env) new-env
      (anEnv 
       (anEnv-name old-env) 
       (anEnv-value old-env) 
       (one-env (anEnv-env old-env) new-env))))

;;addEnv
(define (app-binding [lob : (listof Binding)] [env : Env]) : Env
  (if (empty? lob) (mtEnv) 
      (anEnv 
       (binding-name (first lob)) 
       (interp-env (binding-named-expr (first lob)) env) 
       (app-binding (rest lob) env))))


(define (lookup id env)
  (type-case Env env
    [mtEnv () (error 'lookup "Undefine id")]
    [anEnv (name value env)
           (if (symbol=? id name)
               value
               (lookup id env))]))

(define (list-binding ls1 ls2)
  (if(empty? ls1) empty
  (cons (binding (first ls1)(first ls2))(list-binding (rest ls1) (rest ls2)))))



;; parse : expression -> CFWAE
; This procedure parses an expression into a CFWAE
(define (parse [sexp : s-expression]) : CFWAE
  (cond
    [(s-exp-number? sexp) (num (s-exp->number sexp))]
    [(s-exp-symbol? sexp) (id (s-exp->symbol sexp))]
    [(s-exp-list? sexp)
     (let ([sl (s-exp->list sexp)])
       (case (s-exp->symbol (first sl))
         [(+ - * /) (binop (s-exp->symbol (first sl)) (parse (second sl)) (parse (third sl)))]
         [(if0) (if (= 4 (length sl))(if0 (parse (second sl))(parse (third sl))(parse (fourth sl)))
                    (error 'parse "if0 expression should have a test expression, a then branch and a else branch"))]
         [(fun) (fun (parse-all-symbols(s-exp->list(second sl))) (parse(third sl)))]
         [(app) (app (parse (second sl)) (app-list (s-exp->list(third sl))) )]
         [(with) (with (all-binding (s-exp->list(second sl)))(parse (third sl)))]
         [else (app (parse (first sl)) (app-list (rest sl)) )]))]))

;; interp : CFWAE -> CFWAE-Value
;; This procedure evaluates a CFWAE expression, producing a CFWAE-Value.
(define (interp [expr : CFWAE]) : CFWAE-Value
  (interp-env expr (mtEnv)))

(define (interp-env [expr : CFWAE] [env : Env])
  (type-case CFWAE expr
    [num (n) (numV n)]
    [id (s) (lookup s env)]
    [binop (op l r)
           (local ([define l-num (numV-n (interp-env l env))]
                   [define r-num (numV-n (interp-env r env))])
             (numV (case op 
                     [(+) (+ l-num r-num)]
                     [(-) (- l-num r-num)]
                     [(*) (* l-num r-num)]
                     [(/) (if (equal? 0 r-num)(error 'interp "divide by 0")(/ l-num r-num))])))]
    [if0 (c t f) (local [(define test (interp-env c env))]
                   (if (equal? (numV 0) test) (interp-env t env) (interp-env f env)))]
    [fun (args body) (closureV args body env)]
    [with (lb body) (interp-env body (app-binding lb (one-env env (mtEnv))))]
    [app (f ls) (interp-env (closureV-body (interp-env f env)) 
                            (one-env (app-binding (list-binding (closureV-params (interp-env f env)) ls ) (closureV-env (interp-env f env)))
                                      env ))]
    ;[else (error 'interp-env "invalid list input")]
    ))
(define (run sexp)
  (interp (parse sexp)))

;;;; testing
;(test (parse '3) (num 3))
;(test (parse '(+ 1 2)) (binop '+ (num 1) (num 2)))
;(test (parse '(+ 1 (* 2 3))) (binop '+ (num 1) (binop '* (num 2) (num 3))))
