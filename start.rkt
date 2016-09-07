#lang play

#|
<expr> ::= <num>
         | <bool>
         | <id>
         | <string>
         | {if <expr> <expr> <expr>}
         | {fun {<id>*}}  <expr>}
         | {<expr> <expr>*}
         | {local {<def>*} <expr>}

<def>  ::= {define <id> <expr>}
         | {defclass <id> <id>*}
         | {defins <id> <expr> [<id> <expr>]*}
         | {defclass+ins <id> [<id>*] [<id> <expr>] [<id> <expr>]}


|#
; expresiones
(deftype Expr
  (num n)
  (bool b)
  (str s)
  (ifc c t f)
  (id s)
  (app fun-expr arg-expr-list)
  (prim p) 
  (fun id body)
  (lcal defs body))

; definiciones
(deftype Def
  (dfine name val-expr)) ; define

; definiciones de clase e instancias
(deftype Def-class
  (defclass name fun-list) ;define una clase
  (defins clname bool-expr fun-defs)) ;define una instancia


; definición de la estructura clase + lista de instancias
(deftype Class-ins
  (defclass+ins name fun-names def-ins))

; definición de instancia
(deftype instance-fun
  (insfun id fun))


;; parse :: s-expr -> Expr
; parsea una s-expr en una Expr
(define (parse s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? boolean?) (bool s-expr)]
    [(? string?) (str s-expr)]
    [(list 'local defs body)
     (lcal (map parse-def defs) (parse body))] 
    [(? (λ (x)(assq x *primitives*))) (prim (λ (args) (apply (cadr (assq s-expr *primitives*)) args)))]
    [(? symbol?)  (id s-expr)]    
    [(list 'if c t f) (ifc (parse c) (parse t) (parse f))]
    [(list 'fun xs b) (fun xs (parse b))]
    [(list 'with (list (list x e) ...) b)
     (app (fun x (parse b)) (map parse e))]
    [(list f args ...)
     (app (parse f) (map parse args))]
    ))

; parameter para identificar computación insegura
(define untrusted-status (make-parameter "trusted"))

; untrustex-ctx? :: -> untrusted-status
; cambia el valor del parameter
(define (untrusted-ctx?)
  (eq? (untrusted-status) "untrusted"))

; untrusted :: Fun x env -> Bool
; toma una funcion y la evalua con el parametro untrusted-status en modo "untrusted"
(define (untrusted func env)
  (parameterize ([untrusted-status "untrusted"])
    (interp (first func) env)))
       
; parse-def :: s-expr -> Def
; parsea una s-expr en una estructura de definición
(define (parse-def s-expr)  
  (match s-expr
    [(list 'define id val-expr) (dfine id (parse val-expr))]
    [(list 'define-class id fun ...) (defclass id (map parse fun))]
    [(list 'define-instance class bool fun ...) (defins class (parse bool) (map parse-ins fun))]))

; parse-ins :: s-expr -> Ins
; parsea una instancia
(define (parse-ins s-expr)
  (match s-expr
    [(list id body) (insfun id (parse body))]))
 
; append-instance :: Def-class x Def-class -> defclass+ins
; toma una defclass+ins y le agrega una instancia a su lista de instancias
(define (append-instance cls inst)
                 (match cls
                   [(defclass+ins name fun-list def-ins)
                    (match inst
                      [(defins clname boo instances)
                       (match instances
                         [(list (insfun id-in body) ...) (defclass+ins name fun-list (append def-ins (list inst)))])])]))

; get-method :: inst x string -> fun
; devuelve el método name perteneciente a la instancia ins
(define (get-method inst name)
  (match inst
    [(defins clname bool-expr fun-defs) (let [(lista (filter (λ(x)
                                                              (is-method x name)) fun-defs))]
                                          (if (eq? lista '()) '()
                                              (match (first lista)
                                                [(insfun id (fun ids body))
                                                 (λ(arg-vals)
                                                 (interp body (extend-env ids arg-vals (mtEnv))))]
                                                [(insfun id procedure)
                                                 (match procedure
                                                   [(prim proc)
                                                    (curry proc)])])))]
    ['() '()]
    [(list (defins clname bool-expr fun-defs)) (let [(lista (filter (λ(x)
                                                                      (is-method x name)) fun-defs))]
                                                 (if (eq? lista '()) '() (first lista)))]))


; is-method :: fun x name -> bool
; entrega true si name y el nombre del método son iguales
(define (is-method fun name)
  (match fun
    [(insfun fname body)
     (match name
       [(id nombre) (eq? nombre fname)]
       [else (eq? name fname)])]
    [(list (insfun name2 body) ...) (if (eq? name name2) #t #f)]))

; method-in? :: string x defclass -> bool
; chequea si un metodo está incluido en una defclass
(define (method-in? fun-name classins)
  (match classins
    [(defclass+ins name fun-names def-ins)
     (member fun-name fun-names)]
    [else #f]))
     

; get-instance :: name x val x env -> instance
; entrega la instancia activa de la clase para el valor val
(define (get-instance cname val env)
  (match (env-lookup cname env)
    [(defclass+ins name fun-names instances)
     (let [(var (filter (λ(y)
                      (not (false? y)))
                    (map (λ(x)
                           (match x
                             [(defins fun-name bool-fun funs)
                              (if ((interp bool-fun env) (list val)) x #f)])) instances)))]
       (if (not (eq? var '()))
           (last var)
           '()))]))

;; interp :: Expr Env -> number/procedure/Struct
; convierte una expr en un valor usando un enviroment
(define (interp expr env)
  (match expr
    ; literals
    [(num n) n]
    [(bool b) b]
    [(str s) s]
    ; conditional
    [(ifc c t f)
     (if (interp c env)
         (interp t env)
         (interp f env))]
    ; untrusted
    [(id 'untrusted-ctx?)
     (untrusted-ctx?)]
    [(app (id 'untrusted) fun)
     (untrusted fun env)]
    ; identifier
    [(id x)
     (match (with-handlers
                 ([exn:fail? (λ(exn)
                               (id x))])
               (env-lookup x env))
       [(defclass+ins name fun-names instances)
              (error "error: free identifier" x)]
       [(id y) (id y)]
       [else (env-lookup x env)])]
    ; function (notice the meta interpretation)
    [(fun ids body)
     (λ (arg-vals)
       (interp body (extend-env ids arg-vals env)))]
    ; application
    [(app fun-expr arg-expr-list)
     (if (eq? arg-expr-list '()) ;WITH
         ((interp fun-expr env)
           (map (λ (a) (interp a env)) arg-expr-list))
         (let ([function (fun-lookup fun-expr (interp (first arg-expr-list) env) env)]) ;FUN-LOOKUP
           (if (not (eq? '() function)) ;CHECK IF FUN EXISTS
               (function (map (λ (a) (interp a env)) arg-expr-list)) ; failing here for not finding it
               ((interp fun-expr env)
                (map (λ (a)
                       (match a
                         [(lcal defs body)
                          (def new-env (extend-env '() '() (mtEnv))) ;empty-env, tal vez es un caso muy puntual
                          (for-each (λ (d)
                                      (interp-def d new-env)) defs)
                          (interp body new-env)]
                         [else (interp a env)])) arg-expr-list)))))]
    ;primitive
    [(prim p) p]
    ; local definitions
    [(lcal defs body)
     (def new-env (extend-env '() '() env))            
     (for-each (λ (d) (interp-def d new-env)) defs)
     (interp body new-env)]))

; interp-def :: Def Env -> Void
; lleva las estructuras de definición al ambiente
(define (interp-def d env)
  (match d
    [(dfine id val-expr)
     (update-env! id (interp val-expr env) env)]
    [(defclass+ins name fun-list instances)
     (update-env! name d env)
     (display "defclass+ins in enviroment! ")]
    [(defins class bool-fun funs)
     (for-each (λ(d)
                 (interp-funsin d env)) funs)]
    ))

; interp-funsin :: Def Env -> Void
; agrega una insfun directamente al ambiente, se usa cuando se encuentra un local dentro de otro con
; sobreescritura de instancias
(define (interp-funsin d env)
  (match d
    [(insfun name fun)
     (update-env! name (interp fun env) env)]))

; check :: (parse Prog) -> (parse Prog)
; comprueba que un programa esté bien escrito chequeando que todas las instancias implementen los
; métodos de la lista de métodos de su clase correspondiente, entregando un error si no se encuentra
; uno de los metodos.
(define (check prog)
  (let ([check-aux (λ(fun-list instance)
                     (map (λ(x)
                            (match x
                              [(id name)
                               (let [(C (get-method instance name))]
                                 (if (eq? C '())
                                     (error "error: Bad instance declaration")
                                     #t))]
                              [else #t])) fun-list))])
    (match prog
      [(lcal list body)
       (let ([var (map (λ(x)
                         (match x
                           [(defclass+ins id fun-list instances)
                            (map (λ (y)
                                   (check-aux fun-list y)) instances)]
                           [else #t])) list)])
         prog)]
      [else prog])))

; create-class :: defclass x Listof(defclass or defins) -> defclass+ins
; toma una defclass y una lista que incluye instancias o defclass, luego hace append-instance de todas
; las instancias que correspondan a la clase entregada
(define (create-class class defs)
  (match class
    [(defclass id funs)
     (let ([clase (defclass+ins id funs '())])
       (foldl (λ(x y)
                (match x
                  [(defins id2 bool-fun funs-dec)
                   (if (eq? id id2)
                       (append-instance y x)
                       y)]
                  [else y])) clase defs))]))

;; run :: s-expr -> number
; toma un programa, lo parsea, chequea que esté bien escrito, lo interpreta y entrega un valor
(define (run prog)
  (let ([3-defins (λ(s-expr)
                   (match s-expr
                     [(lcal defs body)
                      (match defs
                        [(list (defclass id funs) ins ...)
                         (lcal (filter (λ(z)
                                         (not (eq? z '()))) (map (λ(x)
                                                                   (match x
                                                                     [(defclass id funs)
                                                                      (create-class x (cdr (member x defs)))]
                                                                     [else '()])) defs)) body)]
                        [else s-expr])]
                     [else s-expr]))])
    (interp (check (3-defins (parse prog))) empty-env)))


#|-----------------------------
Environment abstract data type
empty-env   :: Env
env-lookup  :: Sym Env -> Val 
extend-env  :: List[Sym] List[Val] Env -> Env
update-env! :: Sym Val Env -> Void
|#

;Estructura que define un ambiente
(deftype Env
  (mtEnv)
  (aEnv bindings rest)) ; bindings is a list of pairs (id . val)

(def empty-env  (mtEnv))

; env-lookup :: id env -> Val
; busca el par (id . expr) en el ambiente y retorna la expr
(define (env-lookup search env)
  (match env
    [(mtEnv) (error 'env-lookup "no binding for identifier: ~a" search)]
    [(aEnv bindings rest)
     (match bindings
       [else
        (def binding (assoc search bindings))
        (if binding
            (cdr binding)
            (env-lookup search rest))])]))

; fun-lookup :: id x val x env -> Fun
; busca una funcion dentro de un enviroment, en caso de no encontrarla dentro de las defclass+ins,
; se procede a buscar una función normal con env-lookup
(define (fun-lookup search val env)
  (match env
    [(mtEnv) '()]
    [(aEnv bindings rest)
     (match bindings
       [else
        (def binding (fun-assoc2 search val bindings env))
        (if (not (eq? binding '()))
            binding
            (fun-lookup search val rest))])]))

; fun-assoc2 :: id x (listOf (id . insfun)) -> insfun
; clase auxiliar para fun-lookup, busca una función dentro de los bindings pasando por todos los defclass+ins.
(define (fun-assoc2 search val bindings env)
  (if (not (eq? bindings '()))
      (match (first bindings)
        [(cons id (defclass+ins name fun-names def-ins))
         (if (contains? search fun-names)
             (get-method (get-instance name val env) search) ; env = (aEnv bindings (mtEnv))
             (let ([funlist (fun-in-list search fun-names env)]);trozo agregado
               (if (not (eq? funlist '()))
                   ;buscar en INSTANCE
                   (let  ([getmethod (get-method (get-instance name val env) search)])
                     (if (eq? getmethod '())
                         funlist
                         getmethod)) ;termina trozo agregado, aqui agregar if
                   (fun-assoc2 search val (rest bindings) env))))]
        ['() '()]
        [else (fun-assoc2 search val (rest bindings) env)])
      '()))

; fun-in-list :: id x (listOf id, fun) env) -> fun
; busca una definición de función en una lista de funciones
(define (fun-in-list search funlist env)
  (if (eq? funlist '())
      '()
      (match (first funlist)
        [(app (id name) fun-def)
         (match search
           [(id sear)
            (if (eq? sear name)
                (match (first fun-def)
                  [(fun args body)
                   (λ(arg-vals)
                     (interp body (extend-env args arg-vals env)))])
                (fun-in-list search (rest funlist) env))]
           [else '()])]
         [else (fun-in-list search (rest funlist) env)])))


; contains? :: val x (ListOf(val) -> bool
; chequea si i está contenido en la lista l
(define (contains? i l)
  (if (empty? l) #f
      (or (equal? (first l) i) (contains? i (rest l)))))

;; extend-env  :: List[Sym] List[Val] Env -> Env
; extiende el ambiente agregando la lista de ids y vals
(define (extend-env ids vals env)
  (aEnv (map cons ids vals) ; zip to get list of pairs (id . val)
        env))

;;update-env! :: Sym Val Env -> Void
;; imperative update of env, adding/overring the binding for id.
(define (update-env! id val env)
  (set-aEnv-bindings! env (cons (cons id val) (aEnv-bindings env))))

;;;;;;;

;;; primitives
; http://pleiad.cl/teaching/primitivas
(define *primitives*
  `((+               ,+)
    (-               ,-)
    (*               ,*)
    (%               ,(λ args (apply modulo args)))
    (odd?            odd?)
    (even?           ,even?)
    (/               ,/)
    (=               ,=)
    (<               ,<)
    (<=              ,<=)
    (>               ,>)
    (>=              ,>=)
    (zero?           ,zero?)
    (equal?          ,equal?)
    (number?         ,number?)
    (bool?           ,boolean?)
    (string?         ,string?)
    (not             ,not)
    (and             ,(λ args 
                        (foldl (λ (x y) (and x y))
                               #t args)))
    (or              ,(λ args 
                        (foldl (λ (x y) (or x y))
                               #f args)))
    (string-append   ,string-append)
    (string-length   ,string-length)
    (number->string  ,number->string)
    (string<?        ,string<?)
    ))
