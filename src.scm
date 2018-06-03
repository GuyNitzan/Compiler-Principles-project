;((((((lambda (x1 x2 x3) (lambda (y1 y2) (lambda (z1) (lambda (w1) (lambda (t1 t2 t3)  t1)   ) ))) 1 2 3)4 5)6) 7)8 9 10)
;((((((lambda (x1 x2 x3) (lambda (y1 y2) (lambda (z1) (lambda (w1) (lambda (t1 t2 t3)  y2)   ) ))) 1 2 3)4 5)6) 7)8 9 10)
; ((((((lambda (x1 x2 x3) (lambda (y1 y2) (lambda (z1) (lambda (w1) (lambda (t1 t2 t3)  z1)   ) ))) 1 2 3)4 5)6) 7)8 9 10)
;((((((lambda (x1 x2 x3) (lambda (y1 y2) (lambda (z1) (lambda (w1) (lambda (t1 t2 t3)  w1)   ) ))) 1 2 3)4 5)6) 7)8 9 10)
;((((((lambda (x1 x2 x3) (lambda (y1 y2) (lambda (z1) (lambda (w1) (lambda (t1 t2 t3)  t1)   ) ))) 1 2 3)4 5)6) 7)8 9 10)
; ((((((lambda (x1 x2 x3) (lambda (y1 y2) (lambda (z1) (lambda (w1) (lambda (t1 t2 t3)  t2)   ) ))) 1 2 3)4 5)6) 7)8 9 10)
; ((((((lambda (x1 x2 x3) (lambda (y1 y2) (lambda (z1) (lambda (w1) (lambda (t1 t2 t3)  t3)   ) ))) 1 2 3)4 5)6) 7)8 9 10)
;
;(char->integer #\x79)
;(char->integer #\x80)
;(((lambda (y) (lambda (z) (set! y 1) y) ) 5) 4)
;((((lambda (z) (lambda (y) (lambda (x) (set! x 3) (set! y 5) (if x y x)))) 2) 3) 4)

;((lambda (x) x) 9)

;(zero? 0)
;(zero? 5)
;(string-length "\n")

;(boolean? ((lambda () (boolean? #t))))

;(define d (cons 1 2))

;(define d (cons 1 2))

;(define x 1)
;; 'x
;; (define a (string->symbol "x"));bucket exists
;; 'y
;; (define b (string->symbol "y"));bucket doesn't exist
;; b
;; (eq? b 'y)
;; (boolean? #t)
;; (boolean? #f)
;; (boolean? 1234)
;; (boolean? 'a)
;; (symbol? 'b)
;; (procedure? procedure?)
;; (eq? (car '(a b c)) 'a)
;; (= (car (cons 1 2)) 1)
;; (integer? 1234)
;; (char? #\a)
;; (null? '())
;; (string? "abc")
;; (symbol? 'lambda)
;; (vector? '#(1 2 3))
;; (vector? 1234)
;; (string? '#(a b c))
;; (string? 1234)
;; (= 3 (vector-length '#(a #t ())))
;; (pair? '(a . b))
;; (pair? '())
;; (zero? 0)
;; (zero? 234)
;; (* 1/3 3/5 5/7)
;; (+ 1/2 1/3)
;; (make-vector 5)
;; (vector-length (make-vector 5))
;; (= 5 (vector-length (make-vector 5)))
;; (let ((n 10000))
;;    (= n 10000))
;(append-2 '(1 2) '(1))

;(append '(1 2) '(1))
;#(1 2)
;(define koko '#(1 2 3 #t #f #\a #\b #\x53 5/7 -7))
;; koko
;; (vector-set! koko 0 3)
;; koko
;; (vector-set! koko 1 #\y)
;; koko
;; (vector-set! koko 1 #t)
;; koko
;; (vector-set! koko 1 #f)
;; koko
;; 
;; (vector-set! koko 0 #\a)
;; koko
;; (vector-set! koko 6 #\a)
;; koko
;; (vector-set! koko 7 2/3)
;; koko
;; (vector-set! '#(1 2 3) 0 #\a)
;; (vector-set! '#(1 2 3) 1 #\t)
;; koko
;; (define vectorer koko)
;; vectorer
;; (vector-set! vectorer 3 #\3)
;; vectorer
;; (define checker (lambda (x y z) (vector-set! x y z)))
;; (checker vectorer 1 #\1)
;; vectorer
;(apply + '())	

;(define map (lambda (func lst) (if (null? lst) lst (cons (func (car lst)) (map func (cdr lst))))))
;(map boolean? '(0 2 0))


;(fold-left (lambda (x y) (cons y x)) '() '((1) (2 3)))

;(cons 1 2)
;(numerator 4/5)
;(denominator 4/5)
;(denominator 8)
;(define map (lambda (func lst) (if (null? lst) lst (cons (func (car lst)) (map func (cdr lst))))))


;(vector-ref #(1 2 3 4) 2) 
;(append '(1) '(2))
;(lambda(x) (map boolean? '(1 2)))

;(string->symbol "a")
;(define a "aaaaaaaa")
;(string-set! a 0 #\c)
;'x
;(define fold-left (lambda (func acc lst) (if (null? lst) acc (fold-left func (func acc (car lst)) (cdr lst)))))
;(fold-left boolean? #f '(#t #t))


;(define my-boolean? (lambda (vr) (if (boolean? vr) #t #f)))
;(my-boolean? 5)

;;(define x (lambda (y) y))
;(- 1/2 1/2) ;---


;(* 2/1 1/2)

;(+ 1/2 3/2)

;(x 5)

;(- 1 2)

;(boolean? 5)

;(car '(1 2 3))
;(car (cdr '(1 2 3)))
;(cdr '(1 2 3))
;(cons 1 2)
;(cons (cons 1 2) 3)

;(define my-list (lambda x x))
;(my-list 1 2)

;(symbol->string 'vnjks_b)
;(define list (lambda x x))
;(list 1)
;(define map (lambda (func lst) (if (null? lst) lst (cons (func (car lst)) (map func (cdr lst))))))
;(map boolean? '(1 2))
;(apply + 1 2)
;(vector-set '#(1 2) 1)
;(< 1 1/2)
;#\c
;(string-ref "abbcd" 2)
;#(1 2)

;(define map (lambda (func lst) (if (null? lst) lst (cons (func (car lst)) (map func (cdr lst))))))
;(map boolean? '(1 2) '(6))

;(define a (lambda (c) (lambda () (boolean? 1))))
;((a 5))
;(eq? 5 5)
;(eq? 'a 'a)
;(eq? 'b 'a)

;(remainder 2 5)
;(remainder 5 2)
;(remainder -2 -5)
;(remainder -2 5)
;(remainder 2 -5)
;(eq? 4\5 3\4)
; test 178

;; (define (expmod a b m) 
;;   (cond ((= b 0) 1)
;; 	((= (remainder b 2) 0) (remainder (expmod (remainder (* a a) m) (/ b 2) m) m))
;; 	(else (remainder (* a (expmod a (- b 1) m)) m))))
;;    
;; (expmod 5 13 1)



;;; file 09

(define with (lambda (s f) (apply f s)))

(define crazy-ack
  (letrec ((ack3
   (lambda (a b c)
     (cond
      ((and (zero? a) (zero? b)) (+ c 1))
      ((and (zero? a) (zero? c)) (ack-x 0 (- b 1) 1))
      ((zero? a) (ack-z 0 (- b 1) (ack-y 0 b (- c 1))))
      ((and (zero? b) (zero? c)) (ack-x (- a 1) 1 0))
      ((zero? b) (ack-z (- a 1) 1 (ack-y a 0 (- c 1))))
      ((zero? c) (ack-x (- a 1) b (ack-y a (- b 1) 1)))
      (else (ack-z (- a 1) b (ack-y a (- b 1) (ack-x a b (- c 1))))))))
  (ack-x
   (lambda (a . bcs)
     (with bcs
(lambda (b c)
 (ack3 a b c)))))
  (ack-y
   (lambda (a b . cs)
     (with cs
(lambda (c)
 (ack3 a b c)))))
  (ack-z
   (lambda abcs
     (with abcs
(lambda (a b c)
 (ack3 a b c))))))
    (lambda ()
      (and (= 7 (ack3 0 2 2))
  ;(= 61 (ack3 0 3 3))
 ; (= 316 (ack3 1 1 5))
  #;(= 636 (ack3 2 0 1))
  ))))

(crazy-ack)

;(map (lambda (x) x) '(-1 -2 -3/5))          ; (-1 . (-2 . (-3/5 . ())))

;; (define maor '#(7 9 4/5 99 "maor" #\b #\newline))
;; 
;; ((lambda (x) (x x 1000))
;;  (lambda (x n)
;;    (if (zero? n) #t
;;        (x x (- n 1)))))

