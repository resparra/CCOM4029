#lang plai-typed

(require "typed-lang.rkt")

(define (make-ids (n : number)) : (listof symbol)
  (build-list n (lambda (n) (string->symbol (string-append "var-" (to-string n))))))

;; cascade-lets will build up the nested lets, and use body as the
;; eventual body, preserving order of evaluation of the expressions
(define (cascade-lets (ids : (listof symbol))
                      (exprs : (listof ExprC))
                      (body : ExprC)) : ExprC
  (cond [(empty? ids) body]
        [(cons? ids)
         (LetC (first ids) (first exprs) (cascade-lets (rest ids) (rest exprs) body))]))

;; check-type builds an expression that checks the type of the expression
;; given as an argument
(define (check-type (expr : ExprC) (type : string)) : ExprC
  (Prim2C '== (Prim1C 'tagof expr) (StrC type)))

;; and builds up an and expression from its two pieces
(define (and (expr1 : ExprC) (expr2 : ExprC)) : ExprC
  (IfC expr1 expr2 (FalseC)))

;; all builds up a series of ands over the expression arguments
(define (all (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (exp result) (and exp result)) (TrueC) exprs))

;; map-subtract builds an expression that maps 'num- over a list of expressions
(define (map-primop (op : symbol) (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C op result expr)) (first exprs) (rest exprs)))


(define (desugar-primop (op : symbol) (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
         (cascade-lets
          ids (map desugar args)
          (case op
            ('+ (IfC
                 (all (map (lambda (e) (check-type e "number")) id-exps))
                 (map-primop 'num+ id-exps)
                 (IfC (all (map (lambda (e) (check-type e "string")) id-exps))
                      (map-primop 'string+ id-exps)
                      (ErrorC (StrC "Bad arguments to +")))))
            ('- (IfC
                 (all (map (lambda (e) (check-type e "number")) id-exps))
                 (map-primop 'num- id-exps)
                 (ErrorC (StrC "Bad arguments to -"))))))))

(define (pre-add (id : symbol) (amount : ExprC))
  (SeqC (Set!C id (Prim2C 'num+ amount (IdC id))) (IdC id)))

(define (post-add (id : symbol) (amount : ExprC))
  (LetC 'prev (IdC id)
        (SeqC (Set!C id (Prim2C 'num+ amount (IdC id)))
              (IdC 'prev))))

(define (binary-primop (op : symbol) (args : (listof ExprP))) : ExprC
  (cond
   [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
   [(= 2 (length args)) (Prim2C op (desugar (first args)) (desugar (second args)))]
   [else (ErrorC (StrC "Bad primop"))]))

(define (desugar (exprP : ExprP)) : ExprC
  (type-case ExprP exprP
    [NumP (n) (NumC n)]
    [TrueP () (TrueC)]
    [FalseP () (FalseC)]
    [StrP (s) (StrC s)]
    [IdP (name) (IdC name)]
    [FuncP (args body) (FuncC args (desugar body))]
    [AppP (func args) (AppC (desugar func) (map desugar args))]
    [DefvarP (id bind body) (LetC id (desugar bind) (desugar body))]
    [DeffunP (name ids funbody body)
      (LetC name (FuncC ids (ErrorC (StrC "Dummy fun")))
            (SeqC
             (Set!C name (FuncC ids (desugar funbody)))
             (desugar body)))]

    [PrimAssignP (op lhs val)
                 (type-case LHS lhs
                   [IdLHS (id)
                          (desugar (AssignP lhs (PrimP op (list (IdP id) val))))]
                   [DotLHS (obj field)
                           (desugar (DefvarP 'obj-var obj
                                      (AssignP (DotLHS (IdP 'obj-var) field)
                                               (PrimP op (list
                                                          (DotP (IdP 'obj-var) field)
                                                          val)))))]
                   [BracketLHS (obj field)
                               (desugar (DefvarP 'obj-var obj
                                          (DefvarP 'field-var field
                                            (AssignP (BracketLHS (IdP 'obj-var) (IdP 'field-var))
                                                     (PrimP op (list
                                                                (BracketP (IdP 'obj-var) (IdP 'field-var))
                                                                val))))))])]
    [AssignP (lhs val)
             (type-case LHS lhs
               [IdLHS (id) (Set!C id (desugar val))]
               [DotLHS (obj field)
                       (SetFieldC (desugar obj)
                                  (StrC (symbol->string field))
                                  (desugar val))]
               [BracketLHS (obj field)
                           (SetFieldC (desugar obj)
                                      (desugar field)
                                      (desugar val))])]

    [ObjectP (fields) (ObjectC (map (lambda (f) (fieldC (fieldP-name f) (desugar (fieldP-value f))))
                                    fields))]

    [DotP (obj field) (GetFieldC (desugar obj) (StrC (symbol->string field)))]
    [BracketP (obj field) (GetFieldC (desugar obj) (desugar field))]
    [DotMethodP (obj field args) (desugar (DefvarP 'self obj
                                            (AppP (DotP (IdP 'self) field)
                                                  (cons (IdP 'self) args))))]
    [BrackMethodP (obj field args) (desugar (DefvarP 'self obj
                                              (AppP (BracketP (IdP 'self) field)
                                                    (cons (IdP 'self) args))))]

    [PreIncP (id) (pre-add id (NumC 1))]
    [PostIncP (id) (post-add id (NumC 1))]
    [PreDecP (id) (pre-add id (NumC -1))]
    [PostDecP (id) (post-add id (NumC -1))]

    [SeqP (es)
          (cond
            [(= 0 (length es)) (ErrorC (StrC "sequence with nothing in it"))]
            [(= 1 (length es)) (desugar (first es))]
            [else (SeqC (desugar (first es))
                        (desugar (SeqP (rest es))))])]

    [IfP (p c a) (IfC (desugar p) (desugar c) (desugar a))]
    [PrimP (op args)
        (case op
          ['print (cond
                   [(= 0 (length args)) (ErrorC (StrC "Empty list for print"))]
                   [(= 1 (length args)) (Prim1C 'print (desugar (first args)))]
                   [else (desugar (SeqP (list (PrimP 'print (list (first args)))
                                              (PrimP 'print (rest args)))))])]

          ['< (binary-primop op args)]
          ['> (binary-primop op args)]
          ['== (binary-primop op args)]

          [else (cond
                [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
                [(< 0 (length args)) (desugar-primop op args)])])]

    [WhileP (test body)
          ;; dummy-fun will tell us it was called if we do so accidentally
          (local ([define dummy-fun (FuncC (list) (ErrorC (StrC "Dummy function")))])
          (IfC (desugar test)

               ;; while-var will hold the actual function once we tie
               ;; everything together
               (LetC 'while-var dummy-fun
                 (LetC 'while-func

                   ;; this function does the real work - it runs the body of
                   ;; the while loop, then re-runs it if the test is false, and
                   ;; stops if its true
                   (FuncC (list)
                     (LetC 'temp-var
                       (desugar body)
                       (IfC (desugar test)
                            (AppC (IdC 'while-var) (list))
                            (IdC 'temp-var))))

                   ;; The Set!C here makes sure that 'while-var will resolve
                   ;; to the right value later, and the AppC kicks things off
                   (SeqC (Set!C 'while-var (IdC 'while-func))
                         (AppC (IdC 'while-var) (list)))))

               (FalseC)))]

    [ForP (init test update body)
          (local ([define dummy-fun (FuncC (list) (ErrorC (StrC "Dummy function")))])
          (LetC 'for-v (desugar init)
            (IfC (desugar test)
                 (LetC 'for-func-var dummy-fun
                   (LetC 'for-func
                     (FuncC (list)
                       (LetC 'for-v3 (desugar body)
                         (SeqC
                          (desugar update)
                          (IfC (desugar test)
                               (AppC (IdC 'for-func-var) (list))
                               (IdC 'for-v3)))))
                     (SeqC (Set!C 'for-func-var (IdC 'for-func))
                           (AppC (IdC 'for-func-var) (list)))))
                 (IdC 'for-v))))]))

;;    [else (ErrorC (StrC (string-append "Haven't desugared a case yet:\n"
;;                                       (to-string exprP))))]))