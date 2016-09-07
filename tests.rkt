#lang play

(require "start.rkt")
;; Test sub-module.
;; See http://blog.racket-lang.org/2012/06/submodules.html

;this tests should never fail; these are tests for MiniScheme+ 
  (test (run '{+ 1 1}) 2)
  
  (test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)  
  
  (test (run '{< 1 2}) #t)
  
  (test (run '{local {{define x 1}}
                x}) 1)
  
  (test (run '{local {{define x 2}
                      {define y {local {{define x 1}} x}}}
                {+ x x}}) 4)
  
    (test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)
  
  (test (run '{with {{x 1} {y 2} {z 3}} {+ x y z}}) 6)
  
  (test (run '{with {} {{fun {} 42}}}) 42)

#|
Some tarea 3's tests

|#

;parse-def class
(test (parse-def '(define-class C foo ))
      (defclass 'C (list (id 'foo))))
(test (parse-def '(define-class C foo bar))
      (defclass 'C (list (id 'foo) (id 'bar))))

;parse-def instance
(test (is-method (insfun 'foo (parse '(fun (x) (+ x 1)))) 'foo) #t)
(test (is-method (insfun 'foo (parse '(fun (x) (+ x 1)))) 'bar) #f)

;parameter
(test (untrusted-status) "trusted")
(test (untrusted-ctx?) #f)

;create-class
;muestra como se crea una defclas+ins a partir de una definición de clase y una definición de instancia
(create-class (parse-def '(define-class Show show))
                      (list (parse-def '(define-instance Show number? [show 1]))))

;append-instance
;elegí mostrar el resultado ya que las funciones hacen que los test no queden iguales
(append-instance (create-class (parse-def '(define-class Show show asd)) (list (parse-def '(define-instance Show number?
       [show number->string])) (parse-def '(define-instance Show bool? [asd "hola"])))) (parse-def '(define-instance Show bool? [asd2 (fun (x) (and #t))])))

;get-method
(test ((get-method (parse-def '(define-instance C number?
                                [foo (fun (x) (+ x 1))]
                                [bar (fun (x) (- x 1))])) 'bar) (list 2)) 1) 
(test ((get-method (parse-def '(define-instance C number?
                                [foo (fun (x) (+ x 1))]
                                [bar (fun (x) (- x 1))])) 'foo) (list 4)) 5)
(test ((get-method (parse-def '(define-instance Size number?
                                [size (fun (x) x)])) 'size) (list 10)) 10)

; test get-method en una clase
(test ((match (extend-env (list 'Size) (list (defclass+ins 'Size (list (id 'foo) (id 'bar)) (parse-def '(define-instance C number?
                                                                                                         [foo (fun (x) (+ x 1))]
                                                                                                         [bar (fun (x) (- x 1))])))) (mtEnv))
        [(aEnv bindings rest)
         (match bindings
           [(list (cons id-class (defclass+ins name fun-names def-ins))) (get-method def-ins 'foo)])]) (list 3)) 4)

; test get-method y get-instance
(test ((get-method (get-instance 'Show 1 (extend-env (list 'Show) (list (create-class (parse-def '(define-class Size size))
               (list (parse-def '(define-instance Size number?
                 [size (fun (x) x)]))))) empty-env)) 'size) (list 3)) 3)

(test ((get-method (get-instance 'Show "hola" (extend-env (list 'Show) (list (create-class (parse-def '(define-class Size size))
               (list (parse-def '(define-instance Size number?
                 [size (fun (x) x)]))
                     (parse-def '(define-instance Size string?
                                   [size (fun (x) (string-length x))]))))) empty-env)) 'size) (list "hola")) 4)

; test fun-lookup
(test ((fun-lookup (parse 'size) "hola" (extend-env (list 'Size) (list (create-class (parse-def '(define-class Size size))
                                                                               (list (parse-def '(define-instance Size number?
                                                                                                   [size (fun (x) x)]))
                                                                                     (parse-def '(define-instance Size string?
                                                                                                   [size (fun (x) (string-length x))]))))) empty-env)) (list "hola")) 4)

(test ((fun-lookup (parse 'size) 4 (extend-env (list 'Size) (list (create-class (parse-def '(define-class Size size))
                                                                          (list (parse-def '(define-instance Size number?
                                                                                              [size (fun (x) x)]))
                                                                                (parse-def '(define-instance Size string?
                                                                                              [size (fun (x) (string-length x))]))))) empty-env)) (list 4)) 4)

;test define
(test (run '{local {{define x bool?}} 
           {x 1}}) #f)

;test create-class
(create-class (parse-def '(define-class Size size))
  (list
  (parse-def '(define-instance Size number?
                 [size (fun (x) x)]))
  (parse-def '(define-instance Size string?
                 [size string-length]))))

;test run
(test (run '(local
    ((define-class Size size)
     (define-instance Size number?
       [size (fun (x) x)])
     (define-instance Size string?
       [size string-length])) (+ 1 2))) 3)

;test run, usar funciones de una instancia
(test (run '(local
              ((define-class Size size)
               (define-instance Size number?
                 [size (fun (x) x)]))
              (+ (size 10) (size 5))))
      15)

;test run, usando strings
(test (run '(local
              ((define-class Size size)
               (define-instance Size string?
                 [size string-length]))
              (size "hola"))) 4)

;test run con 2 funciones
(test (run '(local
              ((define-class Size size)
               (define-instance Size number?
                 [size (fun (x) x)])
               (define-instance Size string?
                 [size string-length]))
              (size "hola"))) 4)

;test run usando strings
(test (run '(local
              ((define-class Size size)
               (define-instance Size string?
                 [size string-length]))
              (+ (size "hola") (size "chao")))) 8)

;test con 3 tipos distintos para la misma clase
(test
 (run '(local
         ((define-class Show show)
          (define-instance Show number?
            [show number->string])
          (define-instance Show string?
            [show (fun (x) x)])
          (define-instance Show bool?
            [show (fun (x) (if x "true" "false"))]))
         (string-append (show #t) " "
                        (show 1) " "
                        (show "hola"))))
 "true 1 hola")

;test run, usar funciones de distintas instancias con el mismo nombre
(test (run '(local
              ((define-class Size size)
               (define-instance Size number?
                 [size (fun (x) x)])
               (define-instance Size string?
                 [size string-length]))
              (+ (size 10) (size "hola"))))
      14)

; test usando una función como bool-fun, chequeando que 200 entre en ella y 100 no.
(test (run '(local((define-class Show show)
              (define-instance Show number?
                [show number->string])
              (define-instance Show string?
                [show (fun (x) x)])
              (define-instance Show bool?
                [show (fun (x) (if x "true" "false"))])
              (define-class Size size)
              (define-instance Size number?
                [size (fun (x) x)])
              (define-instance Size string?
                [size string-length])
              (define-instance Show (fun (v) (> v 100))
                [show (fun (x) "big data!!")]))
         (string-append (show 200) (show 100))))
      (string-append "big data!!" "100"))
      
; test usando una bool-fun que utiliza funciones previamente definidas.
(test 
 (run '(local((define-class Show show)
              (define-instance Show number?
                [show number->string])
              (define-instance Show string?
                [show (fun (x) x)])
              (define-instance Show bool?
                [show (fun (x) (if x "true" "false"))])
              (define-class Size size)
              (define-instance Size number?
                [size (fun (x) x)])
              (define-instance Size string?
                [size string-length])
              (define-instance Show (fun (v) (> (size v) 100))
                [show (fun (x) "big data!!")]))
         (string-append (show 200) (show "this is a very long string that should be longer than a hundred characters, so it should be a bit longer still"))))
 "big data!!big data!!")

; chequeo para instancias que no implementan todos los métodos (no implementan "greater?")
(test/exn (run '(local ((define-class Comp 
                      same? 
                      smaller?
                      greater?) 
                    (define-instance Comp number?
                      [same? equal?]
                      [smaller? <])
                    (define-instance Comp string?
                      [same? equal?]
                      [smaller? string<?]))
              (and (greater? "hola" "Hola")
                   (same? "hola" "hola")
                   (greater? 10 2))))
      "error: Bad instance declaration")



; clases no son de primera clase
(test/exn (run '(local
              ((define-class Show show)
               (define-instance Show number?
                 [show number->string]))
              ((fun (x) x) Show)))
      "error: free identifier Show")

; alcance de metodos
(test (run '(local ((define-class Size size)
                    (define-instance Size number?
                      [size (fun (x) x)]))
              (+ (size 5) 
                 (local ((define size (fun (x) 1)))
                   (size 5)))))
      6)

; sobre-escribir instancias localmente
(test 
 (run '(local ((define-class C foo bar)
               (define-instance C number?
                 [foo (fun (x) (+ x 1))]
                 [bar (fun (x) (- x 1))]))
         (+ (foo 3)
            (bar 4)
            (local ((define-instance C number?
                      [foo (fun (x) (* x 2))]
                      [bar (fun (x) (- x 2))]))
              (+ (foo 3)
                 (bar 4)))
            (foo 3))))
 19)

;metodos por defecto
(test (run '(local ((define-class Comp 
                      same? 
                      smaller?
                      [greater? (fun (a b) (and (not (smaller? a b))
                                                (not (same? a b))))]) 
                    (define-instance Comp number?
                      [same? equal?]
                      [smaller? <])
                    (define-instance Comp string?
                      [same? equal?]
                      [smaller? string<?]))
              (and (greater? "hola" "Hola")
                   (same? "hola" "hola")
                   (greater? 10 2))))
      #t)

; metodos por defecto sobreescribiendo un método
(test (run '(local ((define-class Comp 
                      same? 
                      smaller?
                      [greater? (fun (a b) (and (not (smaller? a b))
                                                (not (same? a b))))]) 
                    (define-instance Comp number?
                      [same? equal?]
                      [smaller? <])
                    (define-instance Comp string?
                      [same? equal?]
                      [smaller? string<?]
                      [greater? (fun (a b) "hola")]))
              (greater? "hola" "Hola")))
      "hola")

;software adaptable al contexto
(test 
(run '(local ((define-class Server service1 service2)
(define-instance Server (fun (x) #t)
  [service1 (fun (x) "serv1: full quality")]
  [service2 (fun (x) "serv2: ok")])
(define-instance Server (fun (x) untrusted-ctx?)
  [service1 (fun (x) "serv1: low quality")]
  [service2 (fun (x) "serv2: denied")]))
     (untrusted (service2 2)))) 
"serv2: denied")

;software adaptable al contexto
(test 
(run '(local ((define-class Server service1 service2)
(define-instance Server (fun (x) #t)
  [service1 (fun (x) "serv1: full quality")]
  [service2 (fun (x) "serv2: ok")])
(define-instance Server (fun (x) untrusted-ctx?)
  [service1 (fun (x) "serv1: low quality")]
  [service2 (fun (x) "serv2: denied")]))
     (service2 2))) 
"serv2: ok")

; metodos de primera clase
#|(test  (run '(local ((define-class Show show)
                     (define-instance Show number?
                       [show number->string]))
               ((fun (x) (x 4)) show)))
       "4"  )|#