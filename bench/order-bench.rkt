#lang racket/base

;; First-answer enumeration index per engine, per target.
;;
;; For each (engine, target) pair, counts how many candidates the
;; engine emits before (and including) the first one whose behavior
;; matches the target's I/O examples. This measures WHERE the
;; target's representative sits in each engine's enumeration order,
;; independently of the engine's throughput. The indices feed the
;; index annotations in Table 1 of the paper.
;;
;; Counting is capped by a per-cell wall-clock budget (as in
;; deep-bench.rkt); cells that exceed it are reported as TIMEOUT.
;; Unlike the timing benches, the reported indices are deterministic:
;; they depend only on the enumeration order, not on machine speed.

(require "../main.rkt"
         "bank.rkt")

;; --- per-cell timeout via thread + custodian (as in deep-bench) ---

(define (with-time-limit ms thunk on-timeout)
  (define result-ch (make-channel))
  (define cust (make-custodian))
  (parameterize ([current-custodian cust])
    (thread
      (lambda ()
        (with-handlers ([exn:fail? (lambda (e) (channel-put result-ch (cons 'error e)))])
          (channel-put result-ch (cons 'ok (thunk)))))))
  (sync
    (handle-evt result-ch
      (lambda (v)
        (case (car v)
          [(ok) (cdr v)]
          [(error) (raise (cdr v))])))
    (handle-evt (alarm-evt (+ (current-inexact-milliseconds) ms))
      (lambda (_)
        (custodian-shutdown-all cust)
        (on-timeout)))))

;; --- index counting -------------------------------------------------------

;; first-match-index : (var -> goal) (term -> boolean) -> natural | 'no-answer
;;
;; Applies the goal to a single fresh query variable and walks its
;; answer stream, counting states until the query term walks to a
;; ground term satisfying pred. Returns the 1-based index of that
;; state. Runs inside a memo session, mirroring what `run` does.
(define (first-match-index make-goal pred)
  (with-memo-session
    (let loop ([$ ((call/fresh make-goal) empty-state)] [i 1])
      (let ([$ (pull $)])
        (cond
          [(null? $) 'no-answer]
          [else
           (let ([t (walk* (var 0) (car (car $)))])
             (if (and (ground? t) (pred t))
                 i
                 (loop (cdr $) (+ i 1))))])))))

;; Weighted-stream analogue: cells are (weight . state).
(define (first-match-index-w make-goal pred)
  (with-memo-session
    (let loop ([$ ((call/fresh make-goal) empty-state)] [i 1])
      (let ([$ (pull-w $)])
        (cond
          [(null? $) 'no-answer]
          [else
           (let ([t (walk* (var 0) (car (cdr (car $))))])
             (if (and (ground? t) (pred t))
                 i
                 (loop (cdr $) (+ i 1))))])))))

;; Host bank: 1-based index of the first matching program in the bank
;; built to the target's minimum depth (level-by-level order).
(define (host-bank-index grammar-step terminals behavior depth pred)
  (define bank (build-bank/depth grammar-step terminals behavior depth))
  (let loop ([ps bank] [i 1])
    (cond
      [(null? ps) 'no-answer]
      [(pred (car ps)) i]
      [else (loop (cdr ps) (+ i 1))])))

;; --- arithmetic domain (as in deep-bench.rkt) ------------------------------

(define inputs '(2 3 4))

(define (interp e x)
  (cond
    [(eq? e 'x) x]
    [(number? e) e]
    [(eq? (car e) 'plus)  (+ (interp (cadr e) x) (interp (caddr e) x))]
    [(eq? (car e) 'times) (* (interp (cadr e) x) (interp (caddr e) x))]))

(define (arith-key e)
  (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs))))

(define (arith-pred io-pairs)
  (lambda (t)
    (andmap (lambda (io) (equal? (interp t (car io)) (cdr io))) io-pairs)))

(defrel/bank (arith-bank e)
  #:prune (arith-key e)
  (conde
    [(== e 'x)] [(== e 0)] [(== e 1)]
    [(fresh (l r) (conde [(== e `(plus ,l ,r))] [(== e `(times ,l ,r))])
       (arith-bank l) (arith-bank r))]))

(defrel/bank-w (arith-bank-w e)
  #:prune (arith-key e)
  #:decay 0.5
  (conde-w
    [(== e 'x)] [(== e 0)] [(== e 1)]
    [(fresh-w (l r) (conde-w [(== e `(plus ,l ,r))] [(== e `(times ,l ,r))])
       (arith-bank-w l) (arith-bank-w r))]))

(define (arith-bounded e depth)
  (prune (arith-key e)
    (cond
      [(zero? depth) (conde [(== e 'x)] [(== e 0)] [(== e 1)])]
      [else
       (conde
         [(== e 'x)] [(== e 0)] [(== e 1)]
         [(fresh (l r) (conde [(== e `(plus ,l ,r))] [(== e `(times ,l ,r))])
            (arith-bounded l (- depth 1)) (arith-bounded r (- depth 1)))])])))

(define arith-terminals '(x 0 1))

(define (arith-grammar-step bank)
  (for*/list ([l (in-list bank)]
              [r (in-list bank)]
              [op (in-list '(plus times))])
    (list op l r)))

(define (arith-behavior p) (map (lambda (x) (interp p x)) inputs))

;; (name io-pairs minimum-depth budget-ms) -- same targets as deep-bench.rkt.
(define arith-targets
  `(("(1+x)^2  (d=2)"
     ((2 . 9)   (3 . 16)   (4 . 25))        2 10000)
    ("(1+x)^3  (d=3)"
     ((2 . 27)  (3 . 64)   (4 . 125))       3 30000)
    ("x^5  (d=4)"
     ((2 . 32)  (3 . 243)  (4 . 1024))      4 10000)
    ("(1+x)^4  (d=4)"
     ((2 . 81)  (3 . 256)  (4 . 625))       4 30000)
    ("x^5 + x  (d=5)"
     ((2 . 34)  (3 . 246)  (4 . 1028))      5 30000)
    ("x^5 + 1  (d=5)"
     ((2 . 33)  (3 . 244)  (4 . 1025))      5 30000)
    ("x^6  (d=5)"
     ((2 . 64)  (3 . 729)  (4 . 4096))      5 30000)
    ("(1+x)^5  (d=5)"
     ((2 . 243) (3 . 1024) (4 . 3125))      5 30000)
    ("x^6 + 1  (d=6)"
     ((2 . 65)  (3 . 730)  (4 . 4097))      6 60000)
    ("x^7  (d=6)"
     ((2 . 128) (3 . 2187) (4 . 16384))     6 60000)))

;; --- string domain (as in shallow-bench.rkt) -------------------------------

(define str-inputs '("world" "Alice" "Bob"))

(define (str-interp e s)
  (cond
    [(eq? e 'in) s]
    [(string? e) e]
    [(eq? (car e) 'concat)
     (string-append (str-interp (cadr e) s) (str-interp (caddr e) s))]))

(define (str-key e)
  (ground-key e (lambda (t) (map (lambda (s) (str-interp t s)) str-inputs))))

(define (str-pred io-pairs)
  (lambda (t)
    (andmap (lambda (io) (equal? (str-interp t (car io)) (cdr io))) io-pairs)))

(define str-literals '("" " " "!" "?" ", " "Hello, " "Hi, " "Dear "))

(defrel/bank (str-bank e)
  #:prune (str-key e)
  (conde
    [(== e 'in)]
    [(membero e str-literals)]
    [(fresh (l r) (== e `(concat ,l ,r))
       (str-bank l) (str-bank r))]))

(defrel/bank-w (str-bank-w e)
  #:prune (str-key e)
  #:decay 0.5
  (conde-w
    [(== e 'in)]
    [(== e "")]        [(== e " ")]    [(== e "!")]       [(== e "?")]
    [(== e ", ")]      [(== e "Hello, ")]
    [(== e "Hi, ")]    [(== e "Dear ")]
    [(fresh-w (l r) (== e `(concat ,l ,r))
       (str-bank-w l) (str-bank-w r))]))

(define (str-bounded e depth)
  (prune (str-key e)
    (cond
      [(zero? depth)
       (conde [(== e 'in)] [(membero e str-literals)])]
      [else
       (conde
         [(== e 'in)]
         [(membero e str-literals)]
         [(fresh (l r) (== e `(concat ,l ,r))
            (str-bounded l (- depth 1)) (str-bounded r (- depth 1)))])])))

(define str-terminals (cons 'in str-literals))

(define (str-grammar-step bank)
  (for*/list ([l (in-list bank)]
              [r (in-list bank)])
    (list 'concat l r)))

(define (str-behavior p) (map (lambda (s) (str-interp p s)) str-inputs))

(define str-targets
  `(("greeting: 'Hello, X!'"
     (("world" . "Hello, world!")
      ("Alice" . "Hello, Alice!")
      ("Bob"   . "Hello, Bob!"))
     2 30000)
    ("informal greeting: 'Hi, X?'"
     (("world" . "Hi, world?")
      ("Alice" . "Hi, Alice?")
      ("Bob"   . "Hi, Bob?"))
     2 30000)
    ("echo-with-comma: 'X, X'"
     (("world" . "world, world")
      ("Alice" . "Alice, Alice")
      ("Bob"   . "Bob, Bob"))
     2 30000)
    ("greeting+shout: 'Hello, X!!'"
     (("world" . "Hello, world!!")
      ("Alice" . "Hello, Alice!!")
      ("Bob"   . "Hello, Bob!!"))
     3 30000)))

;; --- driver -----------------------------------------------------------------

(define (fmt v)
  (cond [(eq? v 'TIMEOUT) "TIMEOUT"]
        [(eq? v 'no-answer) "no-answer"]
        [else (format "#~a" v)]))

(define (report-cell label budget thunk)
  (define v (with-time-limit budget thunk (lambda () 'TIMEOUT)))
  (printf "    ~a: ~a~n" label (fmt v))
  (flush-output))

(module+ main
  (printf "First-answer enumeration index per engine~n")
  (printf "==========================================~n")
  (printf "~nArithmetic PBE  (inputs: ~v)~n" inputs)
  (for ([target (in-list arith-targets)])
    (define name     (car target))
    (define io-pairs (cadr target))
    (define depth    (caddr target))
    (define budget   (cadddr target))
    (define pred     (arith-pred io-pairs))
    (printf "  ~a~n" name)
    (report-cell "bounded  " budget
      (lambda () (first-match-index (lambda (q) (arith-bounded q depth)) pred)))
    (report-cell "bank     " budget
      (lambda () (first-match-index (lambda (q) (arith-bank q)) pred)))
    (report-cell "bank-w   " budget
      (lambda () (first-match-index-w (lambda (q) (arith-bank-w q)) pred)))
    (report-cell "host-bank" budget
      (lambda () (host-bank-index arith-grammar-step arith-terminals
                                  arith-behavior depth pred))))

  (printf "~nString PBE  (inputs: ~v)~n" str-inputs)
  (for ([target (in-list str-targets)])
    (define name     (car target))
    (define io-pairs (cadr target))
    (define depth    (caddr target))
    (define budget   (cadddr target))
    (define pred     (str-pred io-pairs))
    (printf "  ~a~n" name)
    (report-cell "bounded  " budget
      (lambda () (first-match-index (lambda (q) (str-bounded q depth)) pred)))
    (report-cell "bank     " budget
      (lambda () (first-match-index (lambda (q) (str-bank q)) pred)))
    (report-cell "bank-w   " budget
      (lambda () (first-match-index-w (lambda (q) (str-bank-w q)) pred)))
    (report-cell "host-bank" budget
      (lambda () (host-bank-index str-grammar-step str-terminals
                                  str-behavior depth pred)))))
