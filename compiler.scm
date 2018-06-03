(load "project/sexpr-parser.scm")
(load "project/tag-parser.scm")
(load "project/semantic-analyzer.scm")

(define my-map"(define map
  ((lambda (y) 
     ((lambda (map1) 
	((lambda (maplist) 
	   (lambda (f . s) 
	     (maplist f s))) 
	 (y (lambda (maplist) 
	      (lambda (f s) 
		(if (null? (car s)) '() 
		    (cons (apply f (map1 car s)) 
			  (maplist f (map1 cdr s))))))))) 
      (y (lambda (map1) 
	   (lambda (f s) 
	     (if (null? s) '() 
		 (cons (f (car s)) 
		       (map1 f (cdr s))))))))) 
   (lambda (f) 
     ((lambda (x) 
	(f (lambda (y z)
	     ((x x) y z))))
      (lambda (x) 
	(f (lambda (y z)
	     ((x x) y z))))))))\n")

(define my-list "(define list (lambda x x))\n")
(define my-fold-left "(define fold-left (lambda (func acc lst) (if (null? lst) acc (fold-left func (func acc (car lst)) (cdr lst)))))\n")
(define my-append-2 "(define append-2 (lambda (ls1 ls2) (if (null? ls1) ls2 (cons (car ls1) (append-2 (cdr ls1) ls2)))))\n")
(define my-append "(define append (lambda x (fold-left append-2 '() x)))\n")


(define pipeline
  (lambda(s)
    ((star <sexpr>) s
     (lambda(m r)
      (map (lambda (e)
             (annotate-tc
              (pe->lex-pe
               (box-set
                (remove-applic-lambda-nil
                 (parse e))))))
           m))
     (lambda (f) 'fail))))


(define file->list
  (lambda (in-file)
    (let ((in-port (open-input-file in-file)))
      (letrec ((run
                (lambda ()
                  (let((ch (read-char in-port)))
                    (if (eof-object? ch)
                        (begin
                          (close-input-port in-port)
                          '())
                        (cons ch (run)))))))
(run)))))



(define update-list
  (lambda (lst)
    (string->list (string-append my-map my-list my-fold-left my-append-2 my-append (list->string lst) 
                                 ))))



(define compile-scheme-file
  (lambda (src trgt)
    (let* ((pes (pipeline (update-list (file->list src))))
            (ct (add-const (construct-ct pes) 0))
            (ft (add-Lglob (construct-ft pes (last-in-tbl ct)) 0))
            (prologue  (list->string (file->list "project/scheme.s")))
            )
       (string->file
        trgt
	(string-append
         prologue
         (const-label-creation ct ct)
         (fv-label ft)
         (code-gen-symbol-table ct 0 (str-amount ct))
         "\nsection .text \nmain:\n push rbp\n"
         (code-gen-apply ft ct)
         (code-gen-< ft ct)
         (code-gen-= ft ct)
         (code-gen-> ft ct)
         (code-gen-plus ft ct)
         (code-gen-div ft ct)
         (code-gen-multi ft ct)
         (code-gen-minus ft ct)
         (code-gen-boolean? ft ct)
         (code-gen-car ft ct)
         (code-gen-cdr ft ct)
         (code-gen-char->integer ft ct)
         (code-gen-char? ft ct)
         (code-gen-cons ft ct)
         (code-gen-denominator ft ct)
         (code-gen-eq? ft ct)
         (code-gen-integer? ft ct)
         (code-gen-integer->char ft ct)
         (code-gen-make-string ft ct)
         (code-gen-make-vector ft ct)
         (code-gen-not ft ct)         
         (code-gen-null? ft ct)       
         (code-gen-number? ft ct)
         (code-gen-numerator ft ct)
         (code-gen-pair? ft ct)
         (code-gen-procedure? ft ct)
         (code-gen-rational? ft ct)
         (code-gen-remainder ft ct)
         (code-gen-string-length ft ct)
         (code-gen-string-ref ft ct)
         (code-gen-string-set! ft ct)
         (code-gen-string->symbol ft ct)        
         (code-gen-string? ft ct)
         (code-gen-symbol? ft ct)
         (code-gen-symbol->string ft ct)        
         (code-gen-vector ft ct)
         (code-gen-vector-length ft ct)        
         (code-gen-vector-ref ft ct)
         (code-gen-vector-set! ft ct)       
         (code-gen-vector? ft ct)
         (code-gen-zero? ft ct)
         (fold-left (lambda (str pe) (string-append str (code-gen pe ft ct  0) "push qword[rax] \ncall write_sob_if_not_void \nadd rsp, 1*8 \n")) "" pes)
         "ret\n"
       ))
       )))


(define string->file
  (lambda (target assm-str)
     (begin 
     (delete-file target)
        (let* ((target-port (open-output-file target)))
            (begin (for-each (lambda(ch) (write-char ch target-port)) (string->list assm-str)) 
        (close-output-port target-port))))))


(define construct-ct
  (lambda (pe)
    (let ((ct `((1 ,(void) T_VOID) (2 () (T_NIL)) (3 ,#f (T_BOOL 0)) (5 ,#t (T_BOOL 1))))
          (cl (dup-remove (cl-expands (const-in-exp pe) '()) '())))
      (letrec ((helper 
                (lambda (tbl lst memo)
                  (if (null? lst) tbl
                      (let ((current (car lst)))
                        (if (or (null? current) (boolean? current) (eq? current (void))) (helper tbl (cdr lst) memo)
                        (if (integer? current) (helper (append tbl `((,memo ,current (T_INTEGER ,current)))) (cdr lst) (+ 2 memo))
			(if (char? current) (helper (append tbl `((,memo ,current (T_CHAR ,(char->integer current))))) (cdr lst) (+ 2 memo))
                        (if (number? current) (helper (append tbl `((,memo ,current (T_FRACTION ,(search-in (numerator current) tbl) ,(search-in (denominator current) tbl))))) (cdr lst) (+ 3 memo))
                        (if (string? current) (helper (append tbl `((,memo ,current (T_STRING ,(length(string->list current)) ,@(map char->integer (string->list current)))))) (cdr lst) (+ 2 (length(string->list current)) memo))
                        (if (symbol? current) 
                            (let ((look-up-res (search-in (symbol->string current) tbl)))
				(if (> look-up-res -1)
                                    (helper (append tbl `((,memo ,current (T_SYMBOL ,look-up-res)))) (cdr lst) (+ 2 memo))
                                    (helper (append tbl `((,memo ,(symbol->string current) (T_STRING ,(length(string->list (symbol->string current))) ,@(map char->integer (string->list (symbol->string current))))))
					`((,(+ 2 (length(string->list (symbol->string current))) memo) ,current (T_SYMBOL ,memo)))) 
					(cdr lst) (+ 4 (length(string->list (symbol->string current))) memo))))
                        (if (vector? current) (helper (append tbl `((,memo ,current (T_VECTOR  ,(length (vector->list current)) ,@(map (lambda (x) (search-in x tbl)) (vector->list current)))))) (cdr lst) (+ 2 (length (vector->list current)) memo))
                            (helper (append tbl `((,memo ,current (T_PAIR  ,(search-in (car current) tbl) ,(search-in (cdr current) tbl))))) (cdr lst) (+ 3 memo))))))))))))))
        
			(helper ct cl 7)))))


(define const-in-exp
  (lambda (exp-lst)

    (fold-left 
     (lambda (acc exp) 

	(if (and (list? exp) (not (null? exp)))
            (if (eq? (car exp) 'const)
                (if (rational? (cadr exp)) (append acc (list (numerator (cadr exp))) (list (denominator (cadr exp))) (list (cadr exp))) 
                    (append acc (list (cadr exp))))  
                
		(append acc (const-in-exp exp)))
      acc))
      '() exp-lst)))


(define cl-expands
  (lambda (lst res)
    (if (null? lst)
	res
	(if (and (number? (car lst)) (not (integer? (car lst))))
            (cl-expands (cdr lst) (append res (list (numerator (car lst))) (list (denominator (car lst))) (list (car lst))))
            (if (pair? (car lst))
            (cl-expands (cdr lst) (append res (inner-const (car lst) '()) (list (car lst)))) 
            (if (vector? (car lst))
                (cl-expands (cdr lst) (append res (cl-expands (vector->list (car lst)) '()) (list (car lst))))
		(cl-expands (cdr lst) (append res (list (car lst))))))))))




(define inner-const
  (lambda (lst res)
    (if (null? lst)
        res
        (if (and (number? (car lst)) (not (integer? (car lst))))
        (inner-const (cdr lst) (append res (list (numerator (car lst))) (list (denominator (car lst))) (list (car lst))))
        (if (not (pair? (cdr lst)))
            (if (not (pair? (car lst)))
		(if (vector? (car lst))
                    (append res (cl-expands (vector->list (car lst)) '()) (list (car lst)) (list (cdr lst)))
                    (append res (list (car lst)) (list (cdr lst))))
		(append res (inner-const (car lst) '()) (list (car lst)) (list (cdr lst))))
            (if (not (pair? (car lst)))
		(if (vector? (car lst))
                    (append res (cl-expands (vector->list (car lst)) '()) (list (car lst)) (inner-const (cdr lst) '()) (list (cdr lst)))
                    (append res (list (car lst)) (inner-const (cdr lst) '()) (list (cdr lst))))
		(append res  (inner-const (car lst) '()) (list (car lst)) (inner-const (cdr lst) '()) (list (cdr lst)))))))))





(define dup-remove
  (lambda (lst res)
    (if (null? lst)
	res
	(if (member (car lst) res)
            (dup-remove (cdr lst) res)
            (dup-remove (cdr lst) (append res (list (car lst))))))))



(define search-in
  (lambda (element table)
    (if (null? table)
        -1
	(if (equal? (cadar table) element)
            (caar table)
            (search-in element (cdr table))))))

(define search-in-fvar
  (lambda (element table)
    (if (null? table)
        -1
	(if (equal? (caddar table) element)
            (caar table)
            (search-in-fvar element (cdr table))))))


(define add-Lglob
  (lambda (table i)
    (if (null? table)
         '()
         `((,(string-append "Lglob" (number->string i)) ,@(car table)) ,@(add-Lglob (cdr table) (+ 1 i)))
         )))


(define fv-label
  (lambda (table)
    (if (null? table)
        ""
        (string-append (caar table) ":\n\t dq SOB_UNDEFINED\n" (fv-label (cdr table))))))
      


(define last-in-tbl
  (lambda (memory)
    (let ((temp (reverse memory)))
	(+ (cadar temp) (length (cadddr (car temp)))))))



(define construct-ft
  (lambda (p-exp memo)
    (let ((flst (dup-remove (find-free p-exp) '(/ > < = eq? map fold-left list append append-2 string->symbol apply string-set! string-ref vector-set! vector-ref vector boolean? cdr car null? integer->char vector-length string-length char? string? vector? symbol? pair? integer? procedure? cons char->integer numerator denominator number? rational? zero? not remainder set-car! set-cdr! make-vector make-string symbol->string + - *))))
	(letrec ((helper (lambda (lst indx)
                           (if (null? lst)
                               '()
                               (cons (list indx (car lst)) (helper (cdr lst) (+ 1 indx)))))))
          (helper flst memo)))))


(define find-free
  (lambda (exps)
    (fold-left 
	(lambda (acc exp) 
          (if (and (list? exp) (not (null? exp)))
              (if (eq? (car exp) 'fvar)
		(append acc (list (cadr exp)))
		(append acc (find-free exp)))
              acc))
        '() exps)))

(define add-const
  (lambda (table i)
    (if (null? table)
         '()
         `((,(string-append "const" (number->string i)) ,@(car table)) ,@(add-const (cdr table) (+ 1 i)))
         )))


(define const-label-creation
  (lambda (new-tbl old-tbl)

    (if (not (null? new-tbl))
       (cond
         ((equal? (cadddr (car new-tbl)) 'T_VOID)
          (string-append (caar new-tbl) ":\n\t dq MAKE_LITERAL(" (symbol->string (cadddr (car new-tbl))) ", 0)\n" (const-label-creation (cdr new-tbl) old-tbl)))
         ((equal? (caaddr (cdar new-tbl)) 'T_NIL)
          (string-append (caar new-tbl) ":\n\t dq MAKE_LITERAL(" (symbol->string (caaddr (cdar new-tbl))) ", 0)\n" (const-label-creation (cdr new-tbl) old-tbl)))
         ((or (equal? (caaddr (cdar new-tbl)) 'T_BOOL) (equal? (caaddr (cdar new-tbl)) 'T_INTEGER) (equal? (caaddr (cdar new-tbl)) 'T_CHAR))
          (string-append (caar new-tbl) ":\n\t dq MAKE_LITERAL(" (symbol->string (caaddr (cdar new-tbl))) "," (number->string (cadadr (cddar new-tbl))) ")\n" (const-label-creation (cdr new-tbl) old-tbl)))
         ((equal? (caaddr (cdar new-tbl)) 'T_PAIR)
          (string-append (caar new-tbl) ":\n\t dq MAKE_LITERAL_PAIR(" (find-label (cadar (cdddar new-tbl)) old-tbl) ", " (find-label (caddar (cdddar new-tbl)) old-tbl) ")\n" (const-label-creation (cdr new-tbl) old-tbl)))
         ((equal? (caaddr (cdar new-tbl)) 'T_STRING)
          (string-append (caar new-tbl) ":\n\t MAKE_LITERAL_STRING " (make-str (caddar new-tbl) "\"" #f) "\n" (const-label-creation (cdr new-tbl) old-tbl)))
         ((equal? (caaddr (cdar new-tbl)) 'T_VECTOR)
          (if (= (cadadr (cddar new-tbl)) 0)
          (string-append (caar new-tbl) ":\n\t dq MAKE_LITERAL(T_VECTOR, 0)\n" (const-label-creation (cdr new-tbl) old-tbl))
          (string-append (caar new-tbl) ":\n\t MAKE_LITERAL_VECTOR " (find-label-vector (cddar (cdddar new-tbl)) old-tbl) "\n" (const-label-creation (cdr new-tbl) old-tbl))))
         ((equal? (caaddr (cdar new-tbl)) 'T_FRACTION)
          (string-append (caar new-tbl) ":\n\t dq MAKE_LITERAL_FRACTION(" (find-label (cadadr (cddar new-tbl)) old-tbl) "," (find-label (caddar (cdddar new-tbl)) old-tbl) ")\n" (const-label-creation (cdr new-tbl) old-tbl))) 
         ((equal? (caaddr (cdar new-tbl)) 'T_SYMBOL)
          (string-append (caar new-tbl) ":\n\t dq MAKE_LITERAL_SYMBOL(" (find-label (cadar (cdddar new-tbl)) old-tbl)")\n" (const-label-creation (cdr new-tbl) old-tbl)))
         (else
             ""))
       "")))


(define find-label
  (lambda (address tbl)
    (if (null? tbl) ""
	(if (equal? address (cadar tbl))
            (caar tbl)
            (find-label address (cdr tbl))))))


(define find-label2
  (lambda (value tbl)
    (if (null? tbl) ""
	(if (equal? value (caddar tbl))
            (caar tbl)
            (find-label2 value (cdr tbl))))))


(define find-label-vector
  (lambda (lst tbl)
    (if (equal? (length lst) 1)
	(find-label (car lst) tbl)
        (string-append (find-label (car lst) tbl) ", " (find-label-vector (cdr lst) tbl)))))


(define make-str
  (lambda (str acc flag)
    (if (= (string-length str) 0) 
      (if flag
          acc
          (string-append acc "\""))
      (cond ((eq? (string-ref str 0) #\nul)
                  (make-str (substring str 1 (string-length str)) (if flag (string-append acc ", CHAR_NUL")
                                                                                       (string-append acc "\""  ", CHAR_NUL")) #t))
            ((eq? (string-ref str 0) #\tab)
                  (make-str (substring str 1 (string-length str)) (if flag (string-append acc ", CHAR_TAB")
                                                                                       (string-append acc "\""  ", CHAR_TAB")) #t))
            ((eq? (string-ref str 0) #\newline)
                  (make-str (substring str 1 (string-length str)) (if flag (string-append acc ", CHAR_NEWLINE")
                                                                                       (string-append acc "\""  ", CHAR_NEWLINE")) #t))
            ((eq? (string-ref str 0) #\page)
                  (make-str (substring str 1 (string-length str)) (if flag (string-append acc ", CHAR_PAGE")
                                                                                       (string-append acc "\""  ", CHAR_PAGE")) #t))
            ((eq? (string-ref str 0) #\return)
                  (make-str (substring str 1 (string-length str)) (if flag (string-append acc ", CHAR_RETURN")
                                                                                       (string-append acc "\""  ", CHAR_RETURN")) #t))
            ((eq? (string-ref str 0) #\space)
                  (make-str (substring str 1 (string-length str)) (if flag (string-append acc ", CHAR_SPACE")
                                                                                       (string-append acc "\""  ", CHAR_SPACE")) #t))

          (else (make-str (substring str 1 (string-length str)) (if flag (string-append acc ", \""(substring str 0 1))
                                                                                     (string-append acc (substring str 0 1))) #f))))


    ))
           


(define code-gen-symbol-table 
        (lambda (ct i rest)
            (if (= rest 0) (if (= i 0) (string-append "symbol_start: \n\t dq const1\n") (string-append "symbol_start: \n\t dq symbol0\n"))
                (if (list? (car (cdddar ct)))
                    (if (not (equal? (caar (cdddar ct)) 'T_SYMBOL))
                        (code-gen-symbol-table (cdr ct) i rest)
                        (if (= rest 1)
                            (string-append "symbol" (number->string i) ": \n\t dq MAKE_LITERAL_PAIR(" (caar ct)   ", const1)\n" (code-gen-symbol-table (cdr ct) (+ i 1) (- rest 1)))
                            (string-append "symbol" (number->string i) ": \n\t dq MAKE_LITERAL_PAIR(" (caar ct)   ", symbol"(number->string (+ i 1)) ")\n"
                                           (code-gen-symbol-table (cdr ct) (+ i 1) (- rest 1)))))
                    (code-gen-symbol-table (cdr ct) i rest)))))





(define str-amount
  (lambda (ct)
    (if (null? ct) 0
        (if (list? (car (cdddar ct)))            
            (if (equal? (caar (cdddar ct)) 'T_SYMBOL)
                (+ 1 (str-amount (cdr ct)))
                (str-amount (cdr ct)))
            (str-amount (cdr ct))))))


(define code-gen
  (lambda (pes ft ct major)
    (cond
      ((equal? (car pes) 'const)
       (code-gen-const pes ct  major))
      ((equal? (car pes) 'if3)
       (code-gen-if pes ft ct  major))
      ((equal? (car pes) 'or)
       (code-gen-or pes ft ct  major))
      ((equal? (car pes) 'seq)
       (code-gen-seq (cadr pes) ft ct major))
      ((equal? (car pes) 'define)
       (code-gen-define pes ft ct major))
      ((equal? (car pes) 'lambda-simple)
       (code-gen-lambda-simple pes ft ct major))
      ((equal? (car pes) 'lambda-opt)
       (code-gen-lambda-opt pes ft ct major))
      ((equal? (car pes) 'applic)
       (code-gen-applic pes ft ct major))
      ((equal? (car pes) 'tc-applic)
      (code-gen-tc-applic pes ft ct major))   
      ((equal? (car pes) 'pvar)
       (code-gen-pvar pes ft ct ))
      ((and (equal? (car pes) 'set) (list? (cadr pes)) (equal? (caadr pes) 'pvar))
       (code-gen-set-pvar pes ft ct (caddr (cadr pes))))
      ((equal? (car pes) 'bvar)
       (code-gen-bvar pes ft ct (caddr pes)(cadddr pes)))
      ((and (equal? (car pes) 'set) (list? (cadr pes)) (equal? (caadr pes) 'bvar))
       (code-gen-set-bvar pes ft ct ))
      ((equal? (car pes) 'fvar)
       (code-gen-fvar pes ft ct))
      ((and (equal? (car pes) 'set) (list? (cadr pes)) (equal? (caadr pes) 'fvar))
       (code-gen-set-fvar pes ft ct major))
      ((equal? (car pes) 'box)
       (code-gen-box pes ft ct major))
      ((equal? (car pes) 'box-get)
        (code-gen-box-get pes ft ct major))
      ((equal? (car pes) 'box-set)
        (code-gen-box-set pes ft ct major))  
      (else
       ""))))
        
       
(define code-gen-const
  (lambda (pes ct major)
    (string-append "mov rax, " (find-label2 (cadr pes) ct) "\n" )))

(define code-gen-if
  (lambda (pes ft ct major)
    (let ((else_label (label-if-else))
          (exit_label (label-ex)))
      (string-append (code-gen (cadr pes) ft ct  major) "cmp rax , const2 \nje " else_label "\n"
                     (code-gen (caddr pes) ft ct  major) "jmp " exit_label "\n" else_label
                     ":\n" (code-gen (cadddr pes) ft ct  major) exit_label ":\n"))))



(define code-gen-or
  (lambda (pes ft ct major)
    (let ((exit_label (label-or-exit)))
      (letrec ((helper (lambda (ex ftab ctab maj)
                         (if (null? ex) (string-append exit_label ":\n")
                             (string-append (code-gen (car ex) ftab ctab maj)
                                            (if (> (length ex) 1) (string-append "cmp rax, const2 ;\njne " exit_label "\n") "")
                                            (helper (cdr ex) ftab ctab maj))))))
        (helper (cadr pes) ft ct major)
        ))))


(define code-gen-seq
  (lambda (exp ft ct major)
    (if (null? exp)
        ""
        (string-append (code-gen (car exp) ft ct major) (code-gen-seq (cdr exp) ft ct major)))))




(define code-gen-define
  (lambda (exp ft ct major)
    (string-append
     (code-gen (caddr exp) ft ct major)
     "mov [" (search-in-fvar (cadadr exp) ft) "], rax\n"
     "mov rax, const0\n"
     )))


(define code-gen-lambda-general
  (lambda (body name ft ct)
    (let* ((clos_body (label-body))
           (clos_exit (label-closes-exit))
           )
      (string-append 
       "mov rdi, 16\n"         
       "call malloc\n"     
       "mov rbx, 0\n"
       "MAKE_LITERAL_CLOSURE rax, rbx, " clos_body "\n" 
       "jmp " clos_exit "\n"
       clos_body ":\n"
       "push rbp\n"
       "mov rbp, rsp\n"
       body"\n"
       "leave\n"
       "ret\n"
       clos_exit ":\n"
       "mov [" (search-in-fvar name ft) "], rax\n\n"
       )
                                 )))



(define code-gen-lambda-simple
  (lambda (pes ft ct major)
      (let* ((args (cadr pes))
             (body (caddr pes))
             (args-len (length args))
             (for1 (label-for-loop))
             (for2 (label-for-loop))
             (exit1 (label-for-exit))
             (exit2 (label-for-exit))
             (clos_body (label-body))
             (clos_exit (label-closes-exit)))
        (string-append

         "mymalloc 2\n"
         "push rax\n"
         (if (= major 0) "mov rbx, 1\n"
             (string-append
              "mov rdi, " (number->string (+ 1 major)) "\n"
              "mymalloc rdi\n"
              "mov rbx, rax\n"
              ))
         (if (= major 0) ""
             (string-append
              "mov rax, [rbp + 3*8]\n"
              "push rax\n"
              "mov rdi, rax\n"
              "mymalloc rdi\n"
              "mov r13, rax\n"
              "mov r11, 0\n"
              "pop rdi\n"
              for1 ":\n"                     
              "cmp r11 ,rdi\n"
              "jge " exit1 "\n"
              "mov rax,r11\n"
              "mov r15, 8\n"
              "mul r15\n"
              "mov rdx, [rbp + 8*(r11+4)]\n"
              "mov qword [r13 + r11*8], rdx \n"
              "add r11, 1\n"
              "jmp " for1 "\n"
              exit1 ":\n"
              "mov qword[rbx], r13\n"
              ))
         (if (< major 2) ""
             (string-append
              "mov r11, 0\n"
              "mov r12, 1\n"
              for2 ":\n"        
              "cmp r11, " (number->string major) "\n"
              "jge " exit2 "\n"
              "mov rax, [rbp + 8*2]\n"
              "mov r14, qword[rax + r11*8]\n"
              "mov [rbx + r12*8], r14\n"
              "add r11, 1\n"
              "add r12, 1\n"
              "jmp " for2 "\n"
              exit2 ":\n"
              ))
         "pop rax\n"
         "MAKE_LITERAL_CLOSURE rax, rbx, " clos_body "\n" 
         "jmp " clos_exit "\n"
         clos_body ":\n"
         "push rbp\n"
         "mov rbp, rsp\n"
         (code-gen body ft ct (+ major 1))"\n"
         "pop rbp\n"
         "ret\n"
         clos_exit ":\n"
         
         ))))

         
(define code-gen-lambda-opt
  (lambda(exp ft ct major)
    (let* ((_lambda_opt_for1 (label-for-loop))
           (_lambda_opt_for2 (label-for-loop))
           (_lambda_opt_body (label-body))
           (_lambda_opt_exit (label-closes-exit))
            (_lambda_opt_loop (label-for-loop))
            (_lambda_opt_fix-stack1 (label-stack))
            (_lambda_opt_fix-stack2 (label-stack))
            (empty_list_params (label-pram-empty-lst))
            (_lambda_opt_continue_ (label-continue))
            (_lambda_opt_continue2_ (label-continue))
           (body (cadddr exp)))

      (string-append
      _lambda_opt_continue_ ":\n\t"
      "mymalloc 2\n\t"
      "push rax\n\t"
      (if (= 0 major) "mov rbx,0\n\t"
      (string-append
      "mov rdi," (number->string (+ 1 major)) "\n\t"
      "mymalloc rdi\n\t"
      "mov rbx, rax\n\t"))
      
      (if (= 0 major) ""
      (string-append
      "mov rdi, [rbp+3*8]\n\t" 
      "mymalloc rdi\n\t"
        
      "mov r8, rax\n\t"))
      

      (if (= 0 major) ""
      (string-append
      "mov r10,0\n"
      _lambda_opt_for1":\n\t"
      "mov r11,qword[rbp+8*(r10 + 4)]\n\t"
      "mov [r8+r10*8],r11\n\t"
      "inc r10\n\t"
      "cmp r10,rdi\n\t"
      "jl "_lambda_opt_for1"\n\t"
      "mov qword [rbx],r8\n\t")) 

      (if (> 2 major) ""
      (string-append
      "mov r9,1\n\t"
      "mov r10,0\n"            
      _lambda_opt_for2":\n\t"
      "mov rsi, qword[rbp+8*2]\n\t"    
      "mov rsi,[rsi+r10*8]\n\t"    
      "mov [rbx+r9*8],rsi\n\t"     
      "add r10, 1\n\t"
      "add r9, 1\n\t"
      "cmp r9," (number->string major) "\n\t"
      "jl "_lambda_opt_for2"\n\t"))

      "mov r12, "(number->string (length (cadr exp))) "\n\t"
      "pop rax\n\t"
      "MAKE_LITERAL_CLOSURE rax, rbx, "_lambda_opt_body"\n\t"
      "jmp "_lambda_opt_exit"\n"
      _lambda_opt_body":\n\t"
      "push rbp\n\t"
      "mov rbp,rsp\n\t"
      
      "mov r14, [rbp +3*8]\n\t"    
      "mov r13, r14\n\t"            
      "add r13, 3\n\t"
      "shl r13, 3\n\t"            
      "mov r12, rbp\n\t"        
      "add r12, r13\n\t"           
      "sub r14, "(number->string (length (cadr exp)))"\n\t"     
      "cmp r14,0\n\t"
      "je "empty_list_params "\n\t"
      "mov r15 , 0\n\t"
      "mov r13 , [const1]\n"
      _lambda_opt_loop ":\n\t"

      "mymalloc 2\n\t"
      "mov r11, [r12]\n\t"
      "mov r11, [r11]\n\t"
      "mov qword[rax] , r11\n\t"
      "mov qword[rax+8] , r13\n\t"
      "mov r8, rax\n\t"
      "add rax, 8\n\t"
      "mov r13, rax\n\t"

      "MAKE_LITERAL_PAIR2 r8, r13\n\t"
      "mov r13, r8\n\t"
      "add r15, 1\n\t"
      "sub r12, 8\n\t"
      "cmp r15,r14\n\t"
      "jl "_lambda_opt_loop "\n\t"

      "mymalloc 1\n\t"

      "mov qword [rax], r13\n\t"
      "add r12 , 8\n\t" 
      "mov qword [r12], rax \n\t"
      "mov r9 , 1\n\t"
      "add r9 , "(number->string (length (cadr exp))) "\n\t" 
      "mov r14, r12\n\t"
      "mov r12, [rbp+ 3*8]\n\t"
      "mov qword [rbp +3*8] , r9 \n\t"
      "mov r15, r12\n\t" 
      "add r15, 3\n\t"
      "shl r15, 3\n\t"
      "add r15, rbp\n\t"
      "mov r13 , r14\n\t"
      "sub r13 , rbp\n\t"
      "shr r13 , 3\n\t"
      "add r13, 1\n"

      _lambda_opt_fix-stack1":\n\t"
      "mov r11,[r14]\n\t"           
      "mov qword [r15], r11\n\t"
      "sub r14,8\n\t"
      "sub r15,8\n\t"
      "sub r13,1\n\t"
      "cmp r13,0\n\t"
      "ja "_lambda_opt_fix-stack1"\n\t" 

      "sub r15, r14\n\t" 
      "add rsp , r15\n\t"
      "add rbp , r15\n\t"
      "jmp "_lambda_opt_continue2_"\n"

      empty_list_params ":\n\t"
      "mov r13, [rbp +3*8]\n\t"  
      "mov r12, r13\n\t"    
      "add r12,1\n\t"
      "mov qword [rbp+3*8] , r12\n\t"
      "add r13, 3\n\t"
      "add r13, 1\n\t"
      "mov r14, rbp\n\t"
      "mov r15, r14\n\t"
      "sub r15 , 8\n"
      
      _lambda_opt_fix-stack2":\n\t"
      "mov r11,[r14]\n\t"            
      "mov qword [r15], r11\n\t"
      "add r14,8\n\t"
      "add r15,8\n\t"
      "dec r13\n\t"
      "cmp r13,0\n\t"
      
      "ja "_lambda_opt_fix-stack2"\n\t" 
      "sub rsp , 8\n\t"
      "sub rbp , 8\n\t"
      "mov r14,const1\n\t"
      "mov qword [r15], r14\n"

      _lambda_opt_continue2_":\n\t"
      (code-gen body ft ct (+ 1 major)) "\n\t"
      "pop rbp\n\t"
      "ret\n"
      _lambda_opt_exit":\n"
      ))))    
         
         
         
  

(define code-gen-applic
  (lambda (exp ft ct major)
    (string-append
     (str-lst->str (map (lambda (x) (string-append (code-gen x ft ct major) "push rax\n")) (reverse (caddr exp))))
     "mov rbx, "(number->string  (length (caddr exp))) "\n"
     "push rbx\n"
     (code-gen (cadr exp) ft ct major)
     "mov rbx, qword[rax]\n"
     "CLOSURE_ENV rbx\n"
     "push rbx\n"
     "mov rax, qword[rax]\n"
     "CLOSURE_CODE rax\n"
     "call rax\n"          
     "mov rbx, [rsp+8]\n"
     "add rbx,2\n"
     "shl rbx, 3\n"
     "add rsp,rbx\n"
     )
    ))





(define code-gen-tc-applic
  (lambda (exp ft ct major)
    (let
        ((for1 (label-for-loop))
         (exit1 (label-for-exit)))
      (string-append
       (str-lst->str (map (lambda (x) (string-append (code-gen x ft ct major) "push rax\n")) (reverse (caddr exp))))
       "mov rbx, "(number->string (length (caddr exp))) "\n"
       "push rbx\n"
       (code-gen (cadr exp) ft ct major)
       "mov rbx, qword[rax]\n"
       "CLOSURE_ENV rbx\n"
       "push rbx\n"
       "mov rax, qword[rax]\n"
       "CLOSURE_CODE rax\n"
  
       "mov rbx, [rbp+8]\n"  
       "push rbx\n"
        
       "mov r11, rbp\n"      
        
       "mov rbp,[rbp]\n"     
       "mov r12,[r11+8*3]\n"
       "add r12, 4\n"
       "shl r12,3\n"
       "add r12,r11\n"
       "mov rbx, "(number->string (+ (length (caddr exp)) 3)) "\n"
        for1 " :\n"
       "cmp rbx, 0\n"
       "je " exit1 "\n"
       "sub r11, 8\n"
       "sub r12, 8\n"
       "mov r13, [r11]\n"
       "mov [r12],r13\n"
       "dec rbx\n"
       "jmp "for1 "\n"
        exit1 " :\n" 
       "mov rsp, r12\n"
       "jmp rax\n" 
        ))))




(define code-gen-pvar
  (lambda (exp ft ct)
    (string-append "mov rax, qword[rbp + (4 +" (number->string (caddr exp)) ")*8]  \n")
    
    ))


(define code-gen-set-pvar
  (lambda (exp ft ct minor)
    (string-append
     (code-gen (caddr exp) ft ct 0) "\n"
     "mov [rbp + "(number->string (+ 4 minor)) "*8], rax \n"
     "mov rax, SOB_VOID\n"
     )))


(define code-gen-bvar
  (lambda (exp ft ct major minor)
    (string-append
     "mov rax, [rbp + 2*8]  \n"
     "mov rax, [rax + " (number->string major) "*8]  \n"
     "mov rax, [rax + "(number->string minor) "*8]  \n"
     )))


(define code-gen-set-bvar
  (lambda (exp ft ct)
    (string-append
     (code-gen (caddr exp) ft ct 0) "\n"   
     "mov rbx, qword[rbp + 2*8]  \n"
     "mov rbx, qword[rbx + " (number->string (caddr (cadr exp))) "*8]  \n"
     "mov qword[rbx + " (number->string (cadddr (cadr exp))) "*8], rax \n"
     "mov rax, SOB_VOID\n"
     )))

(define code-gen-fvar
  (lambda (exp ft ct)
    (string-append
     "mov rax, [" (search-in-fvar (cadr exp) ft) "]\n"
     )))

     
   (define code-gen-set-fvar
    (lambda (exp ft ct major)
     (string-append 
     (code-gen (caddr exp) ft ct major) "\n\t"
     "mov [" (search-in-fvar (cadr (cadr exp)) ft) "], rax\n"
     "mov rax, const0\n")
     ))
     
     

(define code-gen-box
  (lambda (exp ft ct major)
    (string-append
     (code-gen (cadr exp) ft ct (caddr (cadr exp))) "\n" 
     "mov rbx,  rax\n"
     "mov rdi, 8\n"
     "call malloc\n"
     "mov qword[rax], rbx\n"
     )))

(define code-gen-box-get
  (lambda (exp ft ct major)
    (string-append
     (code-gen (cadr exp) ft ct (caddr (cadr exp))) "\n" 
     "mov rax, [rax]\n"
     )))

(define code-gen-box-set
  (lambda (exp ft ct major)
		(string-append
                 (code-gen (caddr exp) ft ct major) "\n" 
                 "mov rbx, rax\n"
                 (code-gen (cadr exp) ft ct (caddr (cadr exp))) "\n"
                 "mov [rax], rbx\n"
                 "mov rax, SOB_VOID\n"
                 )))



(define code-gen-apply
  (lambda(ft ct)
    (code-gen-lambda-general
     (string-append
      "apply_body:\n"
      "mov rax, [rbp+4*8]\n"				
      "mov rax, qword [rax]\n"
      "mov r10, qword [rbp]\n" 
      "mov r11,qword [rbp+8]\n" 
      "mov r12, rbp\n"              
       "add r12, 6*8\n"
  
      "mov rcx, [rbp+5*8]\n"   
      "mov rcx, qword [rcx]\n" 
      "mov rbx, rcx\n"
      "TYPE rbx\n"
 
      "mov rsi, 0\n"  
     
      "apply_calculate_list_length:\n"
      "cmp rbx, T_NIL\n"
      "je apply_calculate_list_length_done\n"
      "CDR rcx\n"
      "mov rbx, rcx\n"
      "TYPE rbx\n"
      "inc rsi\n"
      "jmp apply_calculate_list_length\n"
     
      "apply_calculate_list_length_done:\n"
	        "shl rsi, 3\n"
	        "sub r12, rsi\n"
	        "shr rsi, 3\n"
     
      "mov rdi, 0\n"
      "mov rcx, [rbp+5*8]\n"  			 
      "mov rcx, qword [rcx]\n"
     
      "apply_loop:\n"
     
      "cmp rdi, rsi\n"
      "je apply_loop_exit\n"
      "mov rbx, rcx\n"
      "DATA_UPPER rbx\n"
      "add rbx, start_of_data\n"    
      "mov qword [r12 + 8*rdi], rbx\n"
      "CDR rcx\n"
      "inc rdi\n"
      "jmp apply_loop\n"
     
      "apply_loop_exit:\n"
     
      "sub r12, 8\n"
      "mov qword [r12],rsi\n"
      "sub r12, 8\n"
      "mov rbx, rax\n"
      "CLOSURE_ENV rbx\n"
      "mov qword [r12], rbx\n" 
      "sub r12, 8\n"
      "mov qword [r12], r11\n"   
      "mov rsp, r12\n"
      "mov rbp, r10\n"
	        "mov rbx, rax\n"
	        "TYPE rbx\n"
	        
	        "cmp rbx, T_CLOSURE\n"
	        "jne apply_finish\n"
      
      "CLOSURE_CODE rax\n"
      "jmp rax\n"
      "apply_finish:\n"
     )
    'apply ft ct)))



(define code-gen-integer->char
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_integer_to_char_body: \n\t"
      "mov rbx, qword[rbp+4*8]\n\t"
      "mov rbx ,[rbx]\n\t"
      "DATA rbx\n\t"
      "shl rbx, TYPE_BITS\n\t"
      "or rbx, T_CHAR\n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov [rax], rbx\n"
      ) 'integer->char ft ct)))


(define code-gen-char->integer
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_char_to_integer_body: \n\t"
      "mov rbx, qword[rbp+4*8]\n\t"
      "mov rbx ,[rbx]\n\t"
      "DATA rbx\n\t"
      "shl rbx, TYPE_BITS\n\t"
      "or rbx, T_INTEGER\n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov [rax], rbx\n\t"
      ) 'char->integer ft ct)))

(define code-gen-not
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_not_body: \n\t"
      "mov r14,[rbp+8*(4+0)]\n\t" 
      "mov r14,[r14]\n\t"
      "mov r15,[rbp+8*(3+0)]\n\t" 
      "cmp r14,SOB_FALSE\n\t"
      "je _not_return_true\n\t"
      "mov rax," (find-label2 #f ct)"\n\t"
      "jmp _not_finish\n"
      "_not_return_true:\n\t"
      "mov rax," (find-label2 #t ct)"\n"       
      "_not_finish:\n"
      )
     'not ft ct)))

(define code-gen-null?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_nil_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_NIL\n\t"
      "je _is_nil_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_nil_exit\n"
      "_is_nil_true: \n\t"
      "mov rax, const3\n"
      "_is_nil_exit: \n"
      )
     'null? ft ct)))


(define code-gen-boolean?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_boolean_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_BOOL\n\t"
      "je _is_boolean_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_boolean_exit\n"
      "_is_boolean_true: \n\t"
      "mov rax, const3\n"
      "_is_boolean_exit: \n"
      )
     'boolean? ft ct)))


(define code-gen-char?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_char_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_CHAR\n\t"
      "je _is_char_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_char_exit\n"
      "_is_char_true: \n\t"
      "mov rax, const3\n"
      "_is_char_exit: \n"
      )
     'char? ft ct)))

(define code-gen-eq?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_eq_body: \n"
      
      "mov r10, qword [rbp + 4*8] \n"
      "mov r10, [r10] \n"
      "mov r11, qword [rbp + 5*8] \n"
      "mov r11, [r11] \n"
      
      "TYPE r10 \n"      
      "TYPE r11 \n"
      "cmp r11,r10 \n"
      "jne _eq_false \n"
      
      "cmp r10,T_VOID \n"
      "je L_eq_cmp_addr \n"
      
      "cmp r10, T_NIL \n"
      "je L_eq_cmp_addr \n"
      
      "cmp r10,T_BOOL \n"
      "je L_eq_cmp_addr \n"
      
      "cmp r10,T_STRING \n"
      "je L_eq_cmp_addr \n"
      
      "cmp r10,T_VECTOR \n"
      "je L_eq_cmp_addr \n"
      
      "cmp r10,T_PAIR \n"
      "je L_eq_cmp_addr \n"
      
      "cmp r10,T_CLOSURE \n"
      "je L_eq_cmp_addr \n"
      
      "cmp r10,T_INTEGER \n"
      "je L_eq_cmp_single_value \n"
      
      "cmp r10,T_SYMBOL \n"
      "je L_eq_cmp_single_value \n"
      
      "cmp r10,T_FRACTION \n"
      "je L_eq_cmp_fraction \n"
      
      "L_eq_cmp_addr: \n"
      "mov r10, qword [rbp + 4*8] \n"
      "mov r10, [r10] \n"
      "mov r11, qword [rbp + 5*8] \n"
      "mov r11, [r11] \n"
      "cmp r11,r10 \n"
      "jne _eq_false  \n"
      "jmp eq_true \n"
      
      "L_eq_cmp_fraction: \n"
      "mov r10, qword [rbp + 4*8] \n"
      "mov r10, [r10] \n"
      "mov r11, qword [rbp + 5*8] \n"
      "mov r11, [r11] \n"
      "CAR r10 \n"
      "CAR r11 \n"
      "cmp r10,r11 \n"
      "jne _eq_false \n"
      "mov r10, qword [rbp + 4*8] \n"
      "mov r10, [r10] \n"
      "mov r11, qword [rbp + 5*8] \n"
      "mov r11, [r11] \n"
      "CDR r10 \n"
      "CDR r11 \n"
      "cmp r10,r11 \n"
      "jne _eq_false  \n"
      "jmp eq_true\n"
      
      "L_eq_cmp_single_value: \n"
      "mov r10, qword [rbp + 4*8] \n"
      "mov r10, [r10] \n"
      "mov r11, qword [rbp + 5*8] \n"
      "mov r11, [r11] \n"
      "DATA r10 \n"
      "DATA r11 \n"
      "cmp r10,r11 \n"
      "jne _eq_false  \n"
      "jmp eq_true \n"
      
      "eq_true: \n"
      "mov rax,const3 \n"
      "jmp _eq_done \n"
      
      "_eq_false: \n"
      "mov rax,const2 \n"
      
      "_eq_done: \n"
      
      )'eq? ft ct)))

(define code-gen-number?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_number_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_INTEGER\n\t"
      "je _is_number_true\n\t"
      "cmp r11, T_FRACTION\n\t"
      "je _is_number_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_number_exit\n"
      "_is_number_true: \n\t"
      "mov rax, const3\n"
      "_is_number_exit: \n"
      )
     'number? ft ct)))


(define code-gen-procedure?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_procedure_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_CLOSURE\n\t"
      "je _is_procedure_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_procedure_exit\n"
      "_is_procedure_true: \n\t"
      "mov rax, const3\n"
      "_is_procedure_exit: \n"
      )
     'procedure? ft ct)))


(define code-gen-integer?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_integer_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_INTEGER\n\t"
      "je _is_integer_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_integer_exit\n"
      "_is_integer_true: \n\t"
      "mov rax, const3\n"
      "_is_integer_exit: \n"
      )
     'integer? ft ct)))



(define code-gen-rational?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_rational_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_FRACTION\n\t"
      "je _is_rational_true\n\t"
      "cmp r11, T_INTEGER\n\t"
      "je _is_rational_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_rational_exit\n"
      "_is_rational_true: \n\t"
      "mov rax, const3\n"
      "_is_rational_exit: \n"
      )
     'rational? ft ct)))


(define code-gen-zero?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_zero_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "DATA r11\n\t"
      "cmp r11, 0\n\t"
      "je _zero_true\n\t"
      "mov rax, const2\n\t"
      "jmp _zero_exit\n"
      "_zero_true: \n\t"
      "mov rax, const3\n"
      "_zero_exit: \n"
      )
     'zero? ft ct)))


(define code-gen-remainder
  (lambda(ft ct)	
    (code-gen-lambda-general
     (string-append
      "_remainder_body:\n\t"
      "mov r12, qword [rbp + 4 * 8]\n\t"
      "mov r12, [r12]\n\t"
      
      "mov r13, qword [rbp + 5 * 8]\n\t"
      "mov r13, [r13]\n\t"

      "cmp r12, 0\n\t"
      "jl _remainder_negative\n"
 
      "_remainder_positive:\n\t"
      "DATA r12\n\t"
      "DATA r13\n\t"
      "xor rdx, rdx\n\t"
      "mov rax, r12\n\t"
      "idiv r13\n\t"
      "mov r12, rax\n\t"
      "mov r12, rdx\n\t"
      "shl r12, TYPE_BITS\n\t"
      "add r12, T_INTEGER\n\t"
      "jmp _remainder_finish\n"
      
      "_remainder_negative:\n\t"
      "DATA r12\n\t"
      "neg r12\n\t"
      "DATA r13\n\t"
      "xor rdx, rdx\n\t"
      "mov rax, r12\n\t"
      "idiv r13\n\t"
      "mov r12, rax\n\t"
      "neg rdx\n\t"
      "mov r12, rdx\n\t"
      "shl r12, TYPE_BITS\n\t"
      "add r12, T_INTEGER\n\t"
      "jmp _remainder_finish\n"
      
      "_remainder_finish:\n"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov [rax], r12\n"
      )
     'remainder ft ct)))



     
(define code-gen-symbol?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_symbol_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_SYMBOL\n\t"
      "je _symbol_true\n\t"
      "mov rax, const2\n\t"
      "jmp _symbol_exit\n"
      "_symbol_true: \n\t"
      "mov rax, const3\n"
      "_symbol_exit: \n"
      )
     'symbol? ft ct)))





(define code-gen-symbol->string
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_symbol_to_string_body: \n\t"
      "mov r11, [rbp + 4*8]\n\t"
      "mov r11, [r11]\n\t"
      "SYMBOL_NAME rax, r11\n\t"
      "_symbol_to_string_finish:\n"
      )
     'symbol->string ft ct)))


(define code-gen-string->symbol
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_string_to_symbol_body: \n\t"
      "mov r11, [rbp + 4*8]\n\t"
      "mov r10, [symbol_start]\n\t"
      "mov r10, [r10]\n\t"
      "cmp r10, [const1]\n\t"
      
      "je _string_to_symbol_create \n\t"
      "_string_to_symbol_loop: \n\t"
      "mov r12, r10\n\t"          

      "CAR r12\n\t"
      "SYMBOL_NAME r12, r12\n\t"
      "EQUAL_STRINGS r11, r12\n\t"
      "cmp rax, [const3]\n\t"
      
      "je _string_to_symbol_found \n\t"
      
      "CDR_POINTR r10\n\t"
      "mov r10, [r10]\n\t"
      "cmp r10, [const1]\n\t"
      "je _string_to_symbol_create\n\t"
      "jmp _string_to_symbol_loop\n\t"
      
      
      "_string_to_symbol_found:\n"
      "CAR_POINTR r10\n"
      "mov rax, r10\n"
      "jmp _string_to_symbol_finish\n\t"
      
      "_string_to_symbol_create: \n\t"
      "mov rdi,8\n\t"
      "call malloc\n\t"
      "MAKE_LITERAL_SYMBOL2 rax , r11\n"
      "mov r11, rax\n"
      "mov r13, r11\n"                    
      "mov r14, [symbol_start]\n\t"       
      
      "MAKE_LITERAL_PAIR2 r11 ,r14\n\n"
      
       "mov rdi, 8\n\t"
       "call malloc\n\t"
      "mov [rax], r11\n"
      "mov [symbol_start],rax\n"
      "mov rax, r13\n\n"
      
      "_string_to_symbol_finish:\n"
      
      )
     'string->symbol ft ct)))



(define code-gen-car
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_car_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "CAR r11\n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov qword[rax], r11\n\t"
      "_car_finish:\n"
      )
     'car ft ct)))

(define code-gen-cdr
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_cdr_body: \n\t" 
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "CDR r11\n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov qword[rax], r11\n\t"
      "_cdr_finish:\n"
      )
     'cdr ft ct)))

(define code-gen-cons
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_cons_body: \n\t"
      
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "mov r12, qword[rbp+5*8]\n\t"
      "mov r12, qword[r12]\n\t"
      
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov r13, rax\n\t"
      "mov qword[r13], r11\n\t"
      
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov r14, rax\n\t"
      "mov qword[r14], r12\n\t"
      
      "mov rdi, 16\n\t"
      "call malloc\n\t"
      "MAKE_MALLOC_LITERAL_PAIR rax, r13, r14\n"
      )
     'cons ft ct)))



(define code-gen-pair?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_pair_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_PAIR\n\t"
      "je _is_pair_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_pair_exit\n"
      "_is_pair_true: \n\t"
      "mov rax, const3\n"
      "_is_pair_exit: \n"
      )
     'pair? ft ct)))





(define code-gen-vector?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_vector_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_VECTOR\n\t"
      "je _is_vector_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_vector_exit\n"
      "_is_vector_true: \n\t"
      "mov rax, const3\n"
      "_is_vector_exit: \n"
      )
     'vector? ft ct)))

     
     
(define code-gen-vector-length
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_vector_length_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "VECTOR_LENGTH r11\n\t"
      "shl r11,4\n\t"
      "add r11,T_INTEGER\n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov qword[rax], r11\n"
      )
     'vector-length ft ct)))



(define code-gen-vector-ref
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_vector_ref_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "mov r12, qword[rbp+5*8]\n\t"
      "mov r12, qword[r12]\n\t"
      "DATA r12\n\t"
      "VECTOR_REF rbx, r11, r12\n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov qword[rax], rbx\n\t"
      "_vector_ref_finish:\n"
      )
     'vector-ref ft ct)))



(define code-gen-vector-set!
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_vector_set_body :\n\t"
      "mov r11, qword[rbp+4*8]\n\t" 
      "mov r11, qword[r11]\n"
      "mov r12, qword[rbp+5*8]\n\t" 
      "mov r12, qword[r12]\n\t"
      "DATA r12\n\t"
      "mov r13, qword[rbp+6*8]\n\t" 
      "VECTOR_ELEMENTS r11\n\t"
      "mov [r11 + r12*8], r13\n"
      "mov rax, const0\n\t"
      "_vector_set_finish:\n"
      )
     'vector-set! ft ct)))


(define code-gen-vector
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append    
      "custom_vector_body:\n"       
      "mov rbx, arg_count\n"
      
      "push rbx\n"
      "shl rbx, 3\n"
      "mov rdi, rbx\n"
      "call malloc\n"
      "pop rbx\n"
      
      "mov r10, 0\n" 
      "for_vector:\n"
      "cmp r10, rbx\n"
      "je end_of_vector\n"
      
      "mov rdx, An(r10)\n" 
      "mov qword [rax+r10*8], rdx\n"
      "inc r10\n"
      "jmp for_vector\n"
      "end_of_vector:\n"
      
      "mov rcx, rax\n"
      "shl rbx, 3\n"
      "MAKE_LITERAL_VECTOR2 rcx, rbx\n" 
      "push rcx\n"
      "mov rdi, 8\n"
      "call malloc\n"
      "pop rcx\n"
      "mov [rax], rcx\n"
      
      "custom_vector_finish:\n")
     'vector ft ct)))
  
 

(define code-gen-make-vector
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append    
      "make_vector_body:\n"        
      "mov rbx, arg_count\n"
      "cmp rbx, 1\n" 
      "je make_vector_null\n"
      
      "make_vector_val:\n\t"
      "mov rax, [rbp+4*8]\n"        
      "mov rax, [rax]\n"
      "mov rbx, rax\n"
      "DATA rbx\n" 
      
      "mov rdx, [rbp+5*8]\n" 
  
      "push rbx\n"
      "push rdx\n"
      "shl rbx, 3\n"
      "mov rdi, rbx\n"
      "call malloc\n"
      "pop rdx\n"
      "pop rbx\n"

      "mov r10, 0\n" 
      
      "for_create_vector:\n"
      "cmp r10, rbx\n"
      "je end_of_create_vector\n"
      "mov qword [rax+r10*8], rdx\n"
      "inc r10\n"
      "jmp for_create_vector\n"
      "end_of_create_vector:\n"
      
      "mov rcx, rax\n"
      "shl rbx, 3\n"
      "MAKE_LITERAL_VECTOR2 rcx, rbx\n"
      "push rcx\n"
      "mov rdi, 8\n"
      "call malloc\n"
      "pop rcx\n"
      "mov [rax], rcx\n"
      "jmp make_vector_finish\n"
      
      
      "make_vector_null:\n\t"
      "mov rax, [rbp+4*8]\n"         
      "mov rax, [rax]\n"
      "mov rbx, rax\n"
      "DATA rbx\n" 
      
      "push rbx\n"
      "shl rbx, 3\n"
      "mov rdi, rbx\n"
      "call malloc\n"
      "mov r11, rax\n\t"
      "pop rbx\n"
      "mov rdx,0\n\t"
      "shl rdx, TYPE_BITS\n\t"
      "add rdx, T_INTEGER\n\t" 
      "mov r10, 0\n" 
      
      "mov rdi,8\n\t"
      "push rdx\n\t"
      "call malloc\n\t"
      "pop rdx\n\t"
      "mov [rax], rdx\n\t"
      

      "for_create_vector_nul:\n"
      "cmp r10, rbx\n"
      "je end_of_create_vector_nul\n"
      
      "mov qword [r11+r10*8], rax\n"
      "inc r10\n"
      "jmp for_create_vector_nul\n"
      "end_of_create_vector_nul:\n"
      
      "mov rcx, r11\n"
      "shl rbx, 3\n"
      "MAKE_LITERAL_VECTOR2 rcx, rbx\n"
      "push rcx\n"
      "mov rdi, 8\n"
      "call malloc\n"
      "pop rcx\n"
      "mov [rax], rcx\n"
      
 
      "make_vector_finish:\n"
      )
     'make-vector ft ct)))



(define code-gen-string?
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_is_string_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "TYPE r11\n\t"
      "cmp r11, T_STRING\n\t"
      "je _is_string_true\n\t"
      "mov rax, const2\n\t"
      "jmp _is_string_exit\n"
      "_is_string_true: \n\t"
      "mov rax, const3\n"
      "_is_string_exit: \n"
      )
     'string? ft ct)))



(define code-gen-string-length
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_string_length_body :\n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "STRING_LENGTH r11\n\t"
      "shl r11,4\n\t"
      "add r11,T_INTEGER\n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov qword[rax], r11\n"
      )
     'string-length ft ct)))




(define code-gen-string-ref
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_string_ref_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t" 
      "mov r11, qword[r11]\n\t"
      "mov r12, qword[rbp+5*8]\n\t" 
      "mov r12, qword[r12]\n\t"
      "DATA r12\n\t"
      "mov r13, 0\n\t"
      "STRING_REF r13B, r11, r12\n\t"
      "sal r13, 4\n"
      "or r13, T_CHAR\n"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov qword[rax], r13\n\t"
      "_string_ref_finish:\n"
      )
     'string-ref ft ct)))




(define code-gen-string-set!
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append      
      "string_set_body:\n\t"
      
      "mov r11, qword[rbp+4*8]\n\t" 
      "mov r11, qword[r11]\n\t"
      
      "mov r12, qword[rbp+5*8]\n\t" 
      "mov r12, qword[r12]\n\t"
      "DATA r12\n\t"
      
      "mov r13, An(2)\n\t" 
      "mov r13, [r13]\n\t"      
      "DATA r13\n\t"

      
      "STRING_ELEMENTS r11\n\t"
      "add r11, r12\n\t"
      "mov rcx, r13\n\t"
      "mov byte [r11], cl\n\t"
      
      "mov rax, const0\n"
      
      "string_set_finish:\n"
      
      )
     'string-set! ft ct)))



(define code-gen-make-string
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append          
      "make_string_body:\n"
      "mov rdx, qword 0\n"         
      "mov r9, arg_count\n"
      "cmp r9, 2\n"
      "jg make_string_finish\n"
      
      "mov rax, An(0)\n" 	        
      "mov rax, [rax]\n"
      "mov rbx, rax\n"
      "DATA rbx\n" 
      
      "TYPE rax\n"
      "cmp rax, T_INTEGER\n"
      "jne make_string_finish\n"
      
      "cmp r9, 1\n"
      "je start_creating_string\n"
      
      "mov rcx, An(1)\n" 
      "mov rcx, [rcx]\n"
      "mov rdx, rcx\n"
      "DATA rdx\n"
      
      "TYPE rcx\n"
      "cmp rcx, T_CHAR\n"
      "jne make_string_finish\n"
      
      "start_creating_string:\n"
      
      "push rbx\n"
      "push rdx\n"
      "mov rdi, rbx\n"
      "call malloc\n"
      "pop rdx\n"
      "pop rbx\n"
      
      
      "mov r10, 0\n" 
      
      "for_create_string:\n"
      "cmp r10, rbx\n"
      "je end_of_create_string\n"
      "mov byte [rax+r10], dl\n"
      "inc r10\n"
      "jmp for_create_string\n"
      "end_of_create_string:\n"
      
      "mov rcx, rax\n"
      
      "MAKE_LITERAL_STRING2 rcx, rbx\n" 

      "push rcx\n"
      "mov rdi, 8\n"
      "call malloc\n"
      "pop rcx\n"
      
      "mov [rax], rcx\n"
      
      "make_string_finish:\n"
      )
     'make-string ft ct)))





(define code-gen-denominator
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_denominator_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "mov r12, r11\n\t"
      "TYPE r12\n\t"
      "cmp r12, T_INTEGER\n\t"
      "je denominator_is_integer\n\t"
      "CDR r11\n\t"
      "jmp denominator_exit\n"
      "denominator_is_integer: \n\t"
      "mov r11, 1\n"
      "shl r11, TYPE_BITS\n\t"
      "add r11, T_INTEGER\n\t"
      "denominator_exit: \n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov qword[rax], r11\n"
      )
     'denominator ft ct)))




(define code-gen-numerator
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append
      "_numerator_body: \n\t"
      "mov r11, qword[rbp+4*8]\n\t"
      "mov r11, qword[r11]\n\t"
      "mov r12, r11\n\t"
      "TYPE r12\n\t"
      "cmp r12, T_INTEGER\n\t"
      "je numerator_exit\n\t"
      "CAR r11\n\t"
      "jmp numerator_exit\n"
      "numerator_exit: \n\t"
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov qword[rax], r11\n"              
      )
     'numerator ft ct)))







(define code-gen-plus
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append 
      "_plus_body:\n\t"
      "mov rdi, 0\n\t"                          
      "mov r10, 0\n\t"			
      "mov r11, 1\n"			
      
      "_plus_loop_label: \n\t"
      "cmp rdi, qword[rbp + 3*8]\n\t"
      "je _plus_end_loop\n\t"
      
      "mov r12, qword[rbp + (4 +rdi)*8]\n\t"	
      "mov r12, [r12]\n\t"                
      "mov r13, r12\n\t"                   
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _plus_is_integer\n\t"
      
      "_plus_is_fraction:\n\t"                      
      "CAR r14\n\t"                        
      "DATA r14\n\t"
      "CDR r15\n\t"                        
      "DATA r15\n\t"
      "jmp _plus_add_fraction_to_accs\n"
      
      "_plus_is_integer:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                      
      
      "_plus_add_fraction_to_accs: \n\t"
      
      "mov rax, r15\n\t"
      "mul r10\n\t"					
      "mov r10, rax\n\t"
      
      "mov rax, r11\n\t"
      "mul r14\n\t"					
      "mov r14, rax\n\t"
      
      "mov rax, r15\n\t"
      "mul r11\n\t"				
      "mov r11, rax\n\t"
      
      "add r10, r14\n\t"                       
      
      "inc rdi\n\t"
      "jmp _plus_loop_label\n"
      
      "_plus_end_loop:\n\t"	   
      "cmp r11,1\n\t"
      "je _plus_final_is_int\n\t"
      
      "NUM_GCD r10,r11\n\t"			
      "mov rbx, rdi\n\t"
      
      "mov rax, r11\n\t"
      "mov rdx, 0\n"
      "CQO\n"
      "idiv rbx\n\t"
      "mov r11, rax\n\t"
      
      "mov rax, r10\n\t"
      "mov rdx, 0\n"
      "CQO\n"
      "idiv rbx\n\t"
      "mov r10, rax\n\t"
      
      "cmp r11, 1\n\t"
      "je _plus_final_is_int\n\t"
      "cmp r11, 0\n\t"
      "jge _plus_make_literal\n\t"
      "neg r11\n\t"
      "neg r10\n\t"
       
      
       "_plus_make_literal:\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "mov r12, rax\n\t"
       "shl r10, TYPE_BITS\n\t"
       "add r10, T_INTEGER\n\t"
       "mov [r12], r10\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "mov r13, rax\n\t"
       "shl r11, TYPE_BITS\n\t"
       "add r11, T_INTEGER\n\t"
       "mov [r13], r11\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       
       "MAKE_MALLOC_LITERAL_FRACTION rax, r12, r13\n\t"
       
       "jmp _plus_exit\n\t"
       
       "_plus_final_is_int:\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "shl r10, TYPE_BITS\n\t"
       "add r10, T_INTEGER\n\t"
       "mov [rax], r10\n"
       
       "_plus_exit:\n"
       
       )
     '+ ft ct)))




(define code-gen-multi
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append 
      "_multi_body:\n\t"
      "mov rdi, 0\n\t"                          
      "mov r10, 1\n\t"			
      "mov r11, 1\n"			
      
      "_multi_loop_label: \n\t"
      "cmp rdi, qword[rbp + 3*8]\n\t"
      "je _multi_end_loop\n\t"
      
      "mov r12, qword[rbp + (4 +rdi)*8]\n\t"	
      "mov r12, [r12]\n\t"                 
      "mov r13, r12\n\t"                    
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _multi_is_integer\n\t"
      
      "_multi_is_fraction:\n\t"                      
      "CAR r14\n\t"                        
      "DATA r14\n\t"
      "CDR r15\n\t"                        
      "DATA r15\n\t"
      "jmp _multi_mul_fraction_to_accs\n"
      
      "_multi_is_integer:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                    
      
      "_multi_mul_fraction_to_accs: \n\t"
      
      "mov rax, r14\n\t"
      "mul r10\n\t"					
      "mov r10, rax\n\t"
      
      "mov rax, r15\n\t"
      "mul r11\n\t"					
      "mov r11, rax\n\t"
      
      
      "inc rdi\n\t"
      "jmp _multi_loop_label\n"
      
      "_multi_end_loop:\n\t"	   
      "cmp r11,1\n\t"
      "je _multi_final_is_int\n\t"
      
      "NUM_GCD r10,r11\n\t"			
      
      "mov rbx, rdi\n\t"
      
      "mov rax, r11\n\t"
      "mov rdx, 0\n"
      "CQO\n"
      "idiv rbx\n\t"
      "mov r11, rax\n\t"
      
      "mov rax, r10\n\t"
      "mov rdx, 0\n"
      "CQO\n"
      "idiv rbx\n\t"
      "mov r10, rax\n\t"
      
      "cmp r11, 1\n\t"
      "je _multi_final_is_int\n\t"
      "cmp r11, 0\n\t"
      "jge _mul_make_literal\n\t"
      "neg r11\n\t"
      "neg r10\n\t"
      
      
      "_mul_make_literal:\n\t"
      
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov r12, rax\n\t"
      "shl r10, TYPE_BITS\n\t"
      "add r10, T_INTEGER\n\t"
      "mov [r12], r10\n\t"

      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "mov r13, rax\n\t"
      "shl r11, TYPE_BITS\n\t"
      "add r11, T_INTEGER\n\t"
      "mov [r13], r11\n\t"
      
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      
      "MAKE_MALLOC_LITERAL_FRACTION rax, r12, r13\n\t"
      
      "jmp _multi_exit\n\t"
      
      "_multi_final_is_int:\n\t"
      
      "mov rdi, 8\n\t"
      "call malloc\n\t"
      "shl r10, TYPE_BITS\n\t"
      "add r10, T_INTEGER\n\t"
      "mov [rax], r10\n"
      
      "_multi_exit:\n"
      
      )
     '* ft ct)))






(define code-gen-div
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append 
      "_div_body:\n\t"
      
      "mov r12, qword[rbp + 4*8]\n\t"	
      "mov r12, [r12]\n\t"                
      "mov r13, r12\n\t"                    
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _div_is_integer\n\t"
      
      "_div_is_fraction:\n\t"                      
      "CAR r14\n\t"                       
      "DATA r14\n\t"
      "CDR r15\n\t"            
      "DATA r15\n\t"
      "jmp _div_begin_check\n"
      
      "_div_is_integer:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                    
      
      "_div_begin_check:\n\t"
      "mov rdi, qword[rbp + 3*8]\n\t"
      "cmp rdi, 1\n\t"
      "je _div_with_one_arg\n"
      
      
      "mov rdi, 1\n\t"
      "mov r10, r14\n\t"
      "mov r11, r15\n\t"
      "_div_loop_label: \n\t"
      "cmp rdi, qword[rbp + 3*8]\n\t"
      "je _div_end_loop\n\t"
      
      "mov r12, qword[rbp + (4 +rdi)*8]\n\t"	
      "mov r12, [r12]\n\t"                  
      "mov r13, r12\n\t"                  
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _div_is_integer2\n\t"
      
      "_div_is_fraction2:\n\t"                      
      "CAR r14\n\t"                        
      "DATA r14\n\t"
      "CDR r15\n\t"                       
      "DATA r15\n\t"
      "jmp _div_div_fraction_to_accs\n"
      
      "_div_is_integer2:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                    
      
      "_div_div_fraction_to_accs: \n\t"
      
      "mov rax, r15\n\t"
      "mul r10\n\t"				
      "mov r10, rax\n\t"
      
      "mov rax, r14\n\t"
      "mul r11\n\t"					
      "mov r11, rax\n\t"
      
      "inc rdi\n\t"
      "jmp _div_loop_label\n"
      

      
       "_div_with_one_arg:\n\t"
       "mov r10, 1\n\t"
       "mov r11, 1\n\t"
       
       "mov rax, r15\n\t"
       "mul r10\n\t"					
       "mov r10, rax\n\t"
       
       "mov rax, r14\n\t"
       "mul r11\n\t"					
       "mov r11, rax\n\t"
       
       
       "_div_end_loop:\n\t"	   
       "cmp r11,1\n\t"
       "je _div_final_is_int\n\t"
       "cmp r10,0\n\t"
       "je _div_final_is_int\n\t"
       
       "NUM_GCD r10,r11\n\t"			
       
       "mov rbx, rdi\n\t"
       
       "mov rax, r11\n\t"
       "mov rdx, 0\n"
       "CQO\n"
       "idiv rbx\n\t"
       "mov r11, rax\n\t"
       
       "mov rax, r10\n\t"
       "mov rdx, 0\n"
       "CQO\n"
       "idiv rbx\n\t"
       "mov r10, rax\n\t"
       
       "cmp r10,0\n\t"
       "je _div_final_is_int\n\t"
       "cmp r11, 0\n\t"
       "jge _div_make_literal\n\t"
       "neg r11\n\t"
       "neg r10\n\t"
       

       "_div_make_literal:\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "mov r12, rax\n\t"
       "shl r10, TYPE_BITS\n\t"
       "add r10, T_INTEGER\n\t"
       "mov [r12], r10\n\t"

       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "mov r13, rax\n\t"
       "shl r11, TYPE_BITS\n\t"
       "add r11, T_INTEGER\n\t"
       "mov [r13], r11\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       
       "MAKE_MALLOC_LITERAL_FRACTION rax, r12, r13\n\t"

       "jmp _div_exit\n\t"
       
       "_div_final_is_int:\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "shl r10, TYPE_BITS\n\t"
       "add r10, T_INTEGER\n\t"
       "mov [rax], r10\n"
       
       "_div_exit:\n"
       
       )
     '/ ft ct)))




(define code-gen-minus
  (lambda (ft ct)
      (code-gen-lambda-general
       (string-append 
       "_minus_body:\n\t"

       "mov r12, qword[rbp + 4*8]\n\t"	
       "mov r12, [r12]\n\t"                 
       "mov r13, r12\n\t"                 
       "TYPE r13\n\t"
       "mov r14, r12\n\t"
       "mov r15, r12\n\t"
       "cmp r13, T_INTEGER\n\t"
       "je _minus_is_integer\n\t"

       "_minus_is_fraction:\n\t"                      
       "CAR r14\n\t"                       
       "DATA r14\n\t"
       "CDR r15\n\t"                       
       "DATA r15\n\t"
       "jmp _minus_begin_check\n"

       "_minus_is_integer:\n\t"
       "DATA r14\n\t"
       "mov r15, 1\n"                       
       
       "_minus_begin_check:\n\t"
       "mov rdi, qword[rbp + 3*8]\n\t"
       "cmp rdi, 1\n\t"
       "je _minus_with_one_arg\n"

       
       "mov rdi, 1\n\t"
       "mov r10, r14\n\t"
       "mov r11, r15\n\t"
       "_minus_loop_label: \n\t"
       "cmp rdi, qword[rbp + 3*8]\n\t"
       "je _minus_end_loop\n\t"
       
       "mov r12, qword[rbp + (4 +rdi)*8]\n\t"	
       "mov r12, [r12]\n\t"                 
       "mov r13, r12\n\t"                   
       "TYPE r13\n\t"
       "mov r14, r12\n\t"
       "mov r15, r12\n\t"
       "cmp r13, T_INTEGER\n\t"
       "je _minus_is_integer2\n\t"

       "_minus_is_fraction2:\n\t"                      
       "CAR r14\n\t"                 
       "DATA r14\n\t"
       "CDR r15\n\t"                 
       "DATA r15\n\t"
       "jmp _minus_minus_fraction_to_accs\n"

       "_minus_is_integer2:\n\t"
       "DATA r14\n\t"
       "mov r15, 1\n"                   
      
       "_minus_minus_fraction_to_accs: \n\t"
       
       "mov rax, r15\n\t"
       "mul r10\n\t"					
       "mov r10, rax\n\t"
       
       "mov rax, r11\n\t"
       "mul r14\n\t"					
       "mov r14, rax\n\t"
       
       "mov rax, r15\n\t"
       "mul r11\n\t"					
       "mov r11, rax\n\t"
       
       "sub r10, r14\n\t"                      
       
       "inc rdi\n\t"
       "jmp _minus_loop_label\n"



       "_minus_with_one_arg:\n\t"
       "mov r10, 0\n\t"
       "mov r11, 1\n\t"
       
       "mov rax, r15\n\t"
       "mul r10\n\t"					
       "mov r10, rax\n\t"
       
       "mov rax, r11\n\t"
       "mul r14\n\t"					
       "mov r14, rax\n\t"
       
       "mov rax, r15\n\t"
       "mul r11\n\t"				
       "mov r11, rax\n\t"
       
       "sub r10, r14\n\t"                              

       
       "_minus_end_loop:\n\t"	   
       "cmp r11,1\n\t"
       "je _minus_final_is_int\n\t"
       "cmp r10,0\n\t"
       "je _minus_final_is_int\n\t"
       
       "NUM_GCD r10,r11\n\t"			
       
       "mov rbx, rdi\n\t"
       
       "mov rax, r11\n\t"
       "mov rdx, 0\n"
       "CQO\n"
       "idiv rbx\n\t"
       "mov r11, rax\n\t"
       
       "mov rax, r10\n\t"
       "mov rdx, 0\n"
       "CQO\n"
       "idiv rbx\n\t"
       "mov r10, rax\n\t"


       "cmp r11, 0\n\t"
       "jge _minus_make_literal\n\t"
       "neg r11\n\t"
       "neg r10\n\t"
       
       "cmp r11,1\n\t"
       "je _minus_final_is_int\n\t"
       "cmp r10,0\n\t"
       "je _minus_final_is_int\n\t"

       "_minus_make_literal:\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "mov r12, rax\n\t"
       "shl r10, TYPE_BITS\n\t"
       "add r10, T_INTEGER\n\t"
       "mov [r12], r10\n\t"

       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "mov r13, rax\n\t"
       "shl r11, TYPE_BITS\n\t"
       "add r11, T_INTEGER\n\t"
       "mov [r13], r11\n\t"

       "mov rdi, 8\n\t"
       "call malloc\n\t"
   
       "MAKE_MALLOC_LITERAL_FRACTION rax, r12, r13\n\t"

       "jmp _minus_exit\n\t"
       
       "_minus_final_is_int:\n\t"
       
       "mov rdi, 8\n\t"
       "call malloc\n\t"
       "shl r10, TYPE_BITS\n\t"
       "add r10, T_INTEGER\n\t"
       "mov [rax], r10\n"
       
       "_minus_exit:\n"

       )
       '- ft ct)))






(define code-gen-<
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append 
      "_lower_then_body:\n\t"
      "mov rsi, qword [rbp + 3*8]\n\t"       
      "cmp rsi, 1\n\t"
      "je _lower_then_true \n\t"
      
      "mov r12, qword[rbp + 4*8]\n\t"	
      "mov r12, [r12]\n\t"                 
      "mov r13, r12\n\t"                  
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _lower_then_is_integer\n\t"
      
      "_lower_then_is_fraction:\n\t"                      
      "CAR r14\n\t"                        
      "DATA r14\n\t"
      "CDR r15\n\t"                        
      "DATA r15\n\t"
      "jmp _lower_then_start_loop\n"
      
      "_lower_then_is_integer:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                       
      
      
      
      "_lower_then_start_loop:\n\t"
      "mov rdi, 1\n\t"
      "mov r10, r14\n\t"
      "mov r11, r15\n\t"
      "_lower_then_loop_label: \n\t"
      "cmp rdi, qword[rbp + 3*8]\n\t"
      "je _lower_then_true\n\t"
      
      "mov r12, qword[rbp + (4 +rdi)*8]\n\t"	
      "mov r12, [r12]\n\t"                  
      "mov r13, r12\n\t"                   
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _lower_then_is_integer2\n\t"
      
      "_lower_then_is_fraction2:\n\t"                      
      "CAR r14\n\t"                       
      "DATA r14\n\t"
      "CDR r15\n\t"                        
      "DATA r15\n\t"
      "jmp _lower_then_fraction_to_accs\n"
      
      "_lower_then_is_integer2:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                      
      
      "_lower_then_fraction_to_accs: \n\t"
      
      
      
      "mov r8, r14\n\t"				
      "mov r9, r15\n\t"			
      
      "mov rax, r15\n\t"
      "mul r10\n\t"					
      "mov r10, rax\n\t"
      
      "mov rax, r11\n\t"
      "mul r14\n\t"					
      "mov r14, rax\n\t"
      
      "cmp r10, r14\n\t"
      "jge _lower_then_false \n\t"
      
      "mov r10, r8\n\t"
      "mov r11, r9\n\t"
      
      
      "inc rdi\n\t"
      "jmp _lower_then_loop_label\n"
      
      
      
      
      
      
      "_lower_then_false:\n\t"
      "mov rax, const2\n\t"
      "jmp _lower_then_exit\n"
      
      "_lower_then_true:\n\t"
      "mov rax, const3\n\t"
      
      "_lower_then_exit:\n"
      
      )
     '< ft ct)))






(define code-gen->
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append 
      "_greater_then_body:\n\t"
      "mov rsi, qword [rbp + 3*8]\n\t"       
      "cmp rsi, 1\n\t"
      "je _greater_then_true \n\t"
      
      "mov r12, qword[rbp + 4*8]\n\t"	
      "mov r12, [r12]\n\t"                
      "mov r13, r12\n\t"                    
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _greater_then_is_integer\n\t"
      
      "_greater_then_is_fraction:\n\t"                      
      "CAR r14\n\t"                         
      "DATA r14\n\t"
      "CDR r15\n\t"                       
      "DATA r15\n\t"
      "jmp _greater_then_start_loop\n"
      
      "_greater_then_is_integer:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                        
      
      
      
      "_greater_then_start_loop:\n\t"
      "mov rdi, 1\n\t"
      "mov r10, r14\n\t"
      "mov r11, r15\n\t"
      "_greater_then_loop_label: \n\t"
      "cmp rdi, qword[rbp + 3*8]\n\t"
      "je _greater_then_true\n\t"
      
      "mov r12, qword[rbp + (4 +rdi)*8]\n\t"	
      "mov r12, [r12]\n\t"                 
      "mov r13, r12\n\t"                    
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _greater_then_is_integer2\n\t"
      
      "_greater_then_is_fraction2:\n\t"                      
      "CAR r14\n\t"                         
      "DATA r14\n\t"
      "CDR r15\n\t"                         
      "DATA r15\n\t"
      "jmp _greater_then_fraction_to_accs\n"
      
      "_greater_then_is_integer2:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                        
      
      "_greater_then_fraction_to_accs: \n\t"
      
      
      
      "mov r8, r14\n\t"				
      "mov r9, r15\n\t"			
      
      "mov rax, r15\n\t"
      "mul r10\n\t"					
      "mov r10, rax\n\t"
      
      "mov rax, r11\n\t"
      "mul r14\n\t"					
      "mov r14, rax\n\t"
      
      "cmp r10, r14\n\t"
      "jle _greater_then_false \n\t"
      
      "mov r10, r8\n\t"
      "mov r11, r9\n\t"
      
      
      "inc rdi\n\t"
      "jmp _greater_then_loop_label\n"
      
      
      
      
      
      
      "_greater_then_false:\n\t"
      "mov rax, const2\n\t"
      "jmp _greater_then_exit\n"
      
      "_greater_then_true:\n\t"
      "mov rax, const3\n\t"
      
      "_greater_then_exit:\n"
      
      )
     '> ft ct)))





(define code-gen-=
  (lambda (ft ct)
    (code-gen-lambda-general
     (string-append 
      "_equal_body:\n\t"
      "mov rsi, qword [rbp + 3*8]\n\t"       
      "cmp rsi, 1\n\t"
      "je _equal_true \n\t"
      
      "mov r12, qword[rbp + 4*8]\n\t"	
      "mov r12, [r12]\n\t"                  
      "mov r13, r12\n\t"                  
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _equal_is_integer\n\t"
      
      "_equal_is_fraction:\n\t"                      
      "CAR r14\n\t"                         
      "DATA r14\n\t"
      "CDR r15\n\t"                        
      "DATA r15\n\t"
      "jmp _equal_start_loop\n"
      
      "_equal_is_integer:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                        
      
      
      
      "_equal_start_loop:\n\t"
      "mov rdi, 1\n\t"
      "mov r10, r14\n\t"
      "mov r11, r15\n\t"
      "_equal_loop_label: \n\t"
      "cmp rdi, qword[rbp + 3*8]\n\t"
      "je _equal_true\n\t"
      
      "mov r12, qword[rbp + (4 +rdi)*8]\n\t"	
      "mov r12, [r12]\n\t"                  
      "mov r13, r12\n\t"                    
      "TYPE r13\n\t"
      "mov r14, r12\n\t"
      "mov r15, r12\n\t"
      "cmp r13, T_INTEGER\n\t"
      "je _equal_is_integer2\n\t"
      
      "_equal_is_fraction2:\n\t"                      
      "CAR r14\n\t"                      
      "DATA r14\n\t"
      "CDR r15\n\t"                       
      "DATA r15\n\t"
      "jmp _equal_fraction_to_accs\n"
      
      "_equal_is_integer2:\n\t"
      "DATA r14\n\t"
      "mov r15, 1\n"                       
      
      "_equal_fraction_to_accs: \n\t"
      
      
      
      "mov r8, r14\n\t"				
      "mov r9, r15\n\t"			
      
      "mov rax, r15\n\t"
      "mul r10\n\t"					
      "mov r10, rax\n\t"
      
      "mov rax, r11\n\t"
      "mul r14\n\t"					
      "mov r14, rax\n\t"
      
      "cmp r10, r14\n\t"
      "jne _equal_false \n\t"
      
      "mov r10, r8\n\t"
      "mov r11, r9\n\t"
      
      
      "inc rdi\n\t"
      "jmp _equal_loop_label\n"
      
      
      
      
      
      
      "_equal_false:\n\t"
      "mov rax, const2\n\t"
      "jmp _equal_exit\n"
      
      "_equal_true:\n\t"
      "mov rax, const3\n\t"
      
      "_equal_exit:\n"
      
      )
     '= ft ct)))







(define label-creation
  (lambda (pre)
    (lambda ()
      (let ((n 0))
        (lambda ()
          (set! n (+ n 1))
          (string-append
           pre (number->string n)))))))


(define label-ex ((label-creation "L_if3_exit_")))
(define label-if-else ((label-creation "L_if3_else_")))
(define label-for-loop ((label-creation "L_for_")))
(define label-for-exit ((label-creation "L_for_exit_")))
(define label-or-exit ((label-creation "L_or_exit_")))
(define label-body ((label-creation "L_clos_body_")))
(define label-closes-exit ((label-creation "L_exit_body_")))
(define label-print ((label-creation "DONT_PRINT_")))
(define label-stack ((label-creation "FIX_STACK_")))
(define label-sub ((label-creation "L_substraction_")))
(define label-pram-empty-lst ((label-creation "_empty_list_params")))
(define label-continue ((label-creation "L_continue_")))



(define str-lst->str
	(lambda (lst)
		(if (null? lst) ""
			(string-append (car lst) (str-lst->str (cdr lst))))))


