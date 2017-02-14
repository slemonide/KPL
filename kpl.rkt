#lang racket

;; =================
;; KPL (K Programming Language) interpreter

;; =================
;; Constants:

(define MAX-ITER 100) ;the maximum number of iterations a cycle can run for

;; =================
;; Data definitions:

(struct tape (v l r) #:mutable #:transparent)
;; Tape is one of:
;;  - (tape Integer Tape Tape)
;;  - false
;; INVARIANT: touching tapes are mutually referential,
;;            left tape references right tape through r,
;;            right tape references left tape through l
;; interp. an arbitrary large tape of integers

(define T0 false)
(define LOT (shared ([-1- (tape 0  false -2-)]
                     [-2- (tape 1  -1-   -3-)]
                     [-3- (tape -2 -2-   -4-)]
                     [-4- (tape 3  -3-   -5-)]
                     [-5- (tape 4  -4-   -6-)]
                     [-6- (tape -5 -5-   -7-)]
                     [-7- (tape 6  -6-   false)])
              (list -1- -2- -3- -4- -5- -6- -7-)))

(define T1 (first LOT))
(define T2 (second LOT))
(define T3 (third LOT))
(define T4 (fourth LOT))
(define T5 (fifth LOT))
(define T6 (sixth LOT))
(define T7 (seventh LOT))
#;
(define (fn-for-tape t)
  (cond [(tape? t)
         (... (tape-v t)
              (fn-for-tape (tape-l t))
              (fn-for-tape (tape-r t)))]
        [else
         (...)]))

;; Command is one of:
;;  - Program
;;  - '>
;;  - '<
;;  - '+
;;  - '-
;; interp. a command in KPL, v is the number at the current tape position
;;   > goes to the right in the tape, if tape ends, extend it
;;   < goes to the left in the tape, if tape ends, extend it
;;   + increases the number at the current position by one
;;   - decreases the number at the current position by one
;;   Program creates a cycle
;;           cycle will run for as long as n is not zero
;;           or for as long as the cycle is valid
;; Cycle is invalid if:
;; - The cycle does not contain - < or >
;; - The cycle contains different number of < and >
;; - The last symbol of the cycle is +
;; - The cycle runs for more than MAX-ITER

(define C1 '>)
(define C2 '<)
(define C3 '+)
(define C4 '-)
(define C5 '(> + < -))
#;
(define (fn-for-command c)
  (cond [(list? c)
         (... (fn-for-program c))]
        [(symbol=? '> c) (...)]
        [(symbol=? '< c) (...)]
        [(symbol=? '+ c) (...)]
        [(symbol=? '- c) (...)]))

;; Program is (listof Command)
;; interp. a program in KPL
;;  '+ and '- never go together
;;  '> and '< never go together

(define P0 empty)
(define P1 '(+))
(define P2 '(+ + + + + (> + < -)))
#;
(define (fn-for-program p)
  (cond [(empty? p) (...)]
        [else
         (... (fn-for-command (first p))
              (fn-for-program (rest p)))]))

(struct mac (t p) #:transparent)
;; Machine is (mac Tape Program)
;; interp. a machine with a tape and a program to run
;; INVARIANT: Tape is never empty

(define M1 (mac (tape 0 false false) empty))
(define M2 (mac T1 P2))
#;
(define (fn-for-machine m)
  (... (fn-for-tape (mac-t m))
       (fn-for-program (mac-p m))))

;; =================
;; Functions:

;; Machine -> Machine
;; produce the next machine state by evaluating one command from a program,
;; if it is a cycle, just bring the cycle on the top level

;; templates as encapsulated types
(define (tock m)
  (if (empty? (mac-p m))
      m
      (local [(define cmd (first (mac-p m)))
              
              ;; Command Tape -> Tape
              ;; template from command
              (define (fn-for-tape c t)
                (cond [(list? c) t]
                      [(symbol=? '> c)
                       (if (false? (tape-r t))
                           (shared ([-t- (tape 0 (tape (tape-v t)
                                                       (tape-l t)
                                                       -t-)
                                               false)])
                             -t-)
                           (tape (tape-v (tape-r t))
                                 t
                                 (tape-r (tape-r t))))]
                      [(symbol=? '< c)
                       (if (false? (tape-l t))
                           (shared ([-t- (tape 0 false
                                               (tape (tape-v t)
                                                     -t-
                                                     (tape-r t)))])
                             -t-)
                           (tape (tape-v (tape-l t))
                                 (tape-l (tape-l t))
                                 t))]
                      [(symbol=? '+ c) (tape (add1 (tape-v t))
                                             (tape-l t)
                                             (tape-r t))]
                      [(symbol=? '- c) (tape (sub1 (tape-v t))
                                             (tape-l t)
                                             (tape-r t))]))
              
              ;; Command Program -> Program
              ;; template from command
              (define (fn-for-program cmd val p)
                (cond [(list? cmd)
                       (if (not (= val 0))
                           (append cmd p)
                           (rest p))]
                      [else (rest p)]))]
        
        (mac (fn-for-tape cmd (mac-t m))
             (fn-for-program cmd (tape-v (mac-t m)) (mac-p m))))))


;; Tape -> List
;; produce a list that contains the whole tape

;; template from Tape
(define (tape->list t)
  (local [(define (tape->list t)
            (cond [(tape? t)
                   (append (tape->list-l (tape-l t))
                           (list (tape-v t))
                           (tape->list-r (tape-r t)))]
                  [else
                   empty]))

          (define (tape->list-l t)
            (cond [(tape? t)
                   (append (tape->list-l (tape-l t))
                           (list (tape-v t)))]
                  [else
                   empty]))

          (define (tape->list-r t)
            (cond [(tape? t)
                   (append (list (tape-v t))
                           (tape->list-r (tape-r t)))]
                  [else
                   empty]))]
    (tape->list t)))

;; (listof Integer) -> Tape
;; produce a tape, so that the tape starts at the beginning of the list

;; template as (listof Integer) + context preserving accumulator
(define (list->tape l)
  ;; prev: Tape; tape on the left of the current tape
  (local [(define (list->tape l prev)
            (cond [(empty? l) #f]
                  [else
                   (shared ([-t- (tape (first l) prev
                                       (list->tape (rest l) -t-))])
                     -t-)]))]
    (list->tape l #f)))

;; Function Natural X -> Function X
;; apply a function n times on X

; template from Natural
(define (repeat fn n x)
  (cond [(zero? n) x]
        [else
         (fn (repeat fn (sub1 n) x))]))

;; ===================
;; Experimenting area:
#;
(tape->list (mac-t (repeat tock 100 (mac (tape 200 #f #f) '((> + < -)) ))))
#;
(build-list 104
            (λ (x) (local [(define mech (repeat tock x
                                                (mac (tape 10 #f #f) '((- > + <) > (- < + >)))))]
                     (cons (tape->list (mac-t mech))
                           (mac-p mech)))))
#;
(repeat tock 3
        (mac (tape 10 #f #f) '((- > + <))))
#;#;
(tape-v (mac-t (repeat tock (+ 2 (* 5 12)) (mac (tape 12 #f #f) '((- > + <) >)))))
(tape-v (mac-t (repeat tock (+ 4 (* 10 12)) (mac (tape 12 #f #f) '((- > + <) > (- < + >) <)))))
#;
(tape->list (mac-t (repeat tock 200 (mac (list->tape '(0)) '(+ + + ((<) + (>) <)) ))))
#;; produces a list of natural numbers
(build-list 1000 (λ (x)
                  (tape->list (mac-t (repeat tock x
                                             (mac (list->tape '(0))
                                                  '(- ((<) + (> +) -))
                                                  ))))))
#;; produces a list of natural numbers up to a given number
(build-list 400 (λ (x)
                  (tape->list (mac-t (repeat tock x
                                             (mac (list->tape '(10))
                                                  '(< - ((<) + (> +) - > -))
                                                  ))))))
#;
(build-list 100 (λ (x)
                  (tape->list (mac-t (repeat tock x
                                             (mac (list->tape '(10))
                                                  '((- > > +
                                                       (- (>) > + > + (<) >)
                                                       > (>)
                                                       (- (<) + (>))))
                                                  ))))))
#;
(build-list 3000 (λ (x)
                  (tape->list (mac-t (repeat tock x
                                             (mac (list->tape '(20))
                                                  '(< - ((<) + (> +) - > -) ;generate a list of positive integers
                                                      < + < (<) >           ;go to the start of the list
                                                      - >                   ;delete 1
                                                      > > ((-) > >)         ;delete every multiple of two
                                                      < < <
                                                      )
                                                  ))))))

;; ================
;; Tests:
#;
(module+ test 
  
  (require rackunit rackunit/text-ui)

  ;; basic tests for tock

  (check-equal? (tock (mac (tape 0 #f #f) '()))
                (mac (tape 0 #f #f) '())
                "no commands")
  (check-equal? (tock (mac (tape 0 #f #f) '(>)))
                (mac (shared ([-t- (tape 0 (tape 0 #f -t-) #f)]) -t-) '())
                "move right")
  (check-equal? (tock (mac (tape 0 #f #f) '(<)))
                (mac (shared ([-t- (tape 0 #f (tape 0 -t- #f))]) -t-) '())
                "move left")
  (check-equal? (tock (mac (tape 0 #f #f) '(+)))
                (mac (tape 1 #f #f) '())
                "increment")
  (check-equal? (tock (mac (tape 0 #f #f) '(-)))
                (mac (tape -1 #f #f) '())
                "decrement")
  (check-equal? (tock (mac (tape 0 #f #f) '(())))
                (mac (tape 0 #f #f) '())
                "if evaluates to false")
  (check-equal? (tock (mac (tape 1 #f #f) '((+))))
                (mac (tape 1 #f #f) '(+ (+)))
                "if evaluates to true")

  ;; tape->list
  (check-equal? (tape->list #f) '())
  (check-equal? (tape->list (tape 20 #f #f)) '(20))
  (check-equal? (tape->list T1) '(0 1 -2 3 4 -5 6))
  (check-equal? (tape->list T7) '(0 1 -2 3 4 -5 6))
  (check-equal? (tape->list T4) '(0 1 -2 3 4 -5 6))
  (check-equal? (tape->list (shared ([-t- (tape 20 (tape 40 #f -t-) #f)]) -t-))
                '(40 20))

  ;; list->tape
  (check-equal? (list->tape empty) #f)
  (check-equal? (list->tape (list 0)) (tape 0 #f #f))
  (check-equal? (list->tape (list 0 1)) (shared ([-1- (tape 0 #f -2-)]
                                                 [-2- (tape 1 -1- #f)]) -1-))
  (check-equal? (list->tape (list 3 1 4 1 5 9 2 6))
                (shared ([-1- (tape 3 #f  -2-)]
                         [-2- (tape 1 -1- -3-)]
                         [-3- (tape 4 -2- -4-)]
                         [-4- (tape 1 -3- -5-)]
                         [-5- (tape 5 -4- -6-)]
                         [-6- (tape 9 -5- -7-)]
                         [-7- (tape 2 -6- -8-)]
                         [-8- (tape 6 -7-  #f)]) -1-))

  
  ;; repeat
  (check-equal? (repeat add1  0 0)  0)
  (check-equal? (repeat add1 10 0) 10)
  (check-equal? (repeat sub1 10 10) 0)

  ;; ---------------------------------------------------------------------------
  ;; testing random properties of the language

  ;; Property:
  ;; The following code is equivalent to (- m n)
  ;; tape position by n times
  (define (prop:substraction m n)
    (check-equal?
     (tape-v (mac-t (repeat tock (* 2 n)
                            (mac (tape m #f #f) '((-) - (-))))))
     (- m n)))

  ;; Property:
  ;; The following code is equivalent to (+ m n)
  ;; tape position by n times
  (define (prop:addition m n)
    (check-equal?
     (tape-v (mac-t (repeat tock (* 2 n)
                            (mac (tape m #f #f) '((+) + (+))))))
     (+ m n)))

  ;; Property:
  ;; Moving the content (positive) of a cell to the right cell
  (define (prop:right-move n)
    (check-equal?
     (tape-v (mac-t (repeat tock (+ 2 (* 5 n)) (mac (tape n #f #f) '((- > + <) >)))))
     n "checks that the tape is not teared apart when moved back and forth"))

  ;; Property:
  ;; Moving the content (positive) of a given cell to the right cell and back
  (define (prop:right-left-move n)
    (check-equal?
     (tape-v (mac-t (repeat tock (+ 4 (* 10 n)) (mac (tape n #f #f) '((- > + <) > (- < + >) <)))))
     n "checks that the tape is not teared apart when moved back and forth"))

  
  ;; property tests
  (for ([i (in-range 1000)])
    (prop:substraction (random 1000) (random 1000))
    (prop:addition (random 1000) (random 1000))
    (prop:right-move (random 1000))
    (prop:right-left-move (random 1000)))
  
  "all tests run")
