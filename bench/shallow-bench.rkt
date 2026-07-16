#lang racket/base

;; Synthesis benchmark suite: defrel/bank vs depth-bounded prune.
;;
;; Compares the clean depth-less defrel/bank style against the more
;; verbose expr-bounded idiom across multiple PBE targets, in two
;; domains:
;;
;;   1. Arithmetic -- polynomials over a single integer input x.
;;   2. String manipulation -- concatenation grammar over a single
;;      string input, à la Polikarpova's "Big Ideas in Program
;;      Synthesis" examples (greeting formatters, echo patterns, etc).
;;
;; For each target, bounded is run at the smallest depth that admits a
;; solution (best case for bounded). defrel/bank has no depth knob.
;;
;; --- Observed patterns ----------------------------------------------------
;;
;; Arithmetic (3 integer inputs, small behavior space):
;;   - bank ties or BEATS bounded for several targets (x^2+x, x^3, x^3+1).
;;     The x^3+1 case is the most striking: bank is ~5x faster than
;;     depth-3 bounded.
;;   - bank is ~1.5x slower for (1+x)^2+1.
;;
;; String (3 string inputs, wide behavior space):
;;   - At depth 2, bank is 3-10x slower than bounded depth=2. Wide
;;     behavior space means depth-less exploration visits many
;;     non-pruned states before reaching the depth-2 answer.
;;   - At depth 3, bank and bounded are tied.
;;
;; Likely reason bank can beat bounded at depth >= 3 in arithmetic: the
;; expr-bounded version creates a *fresh* prune cache per recursive
;; call (each `prune` call gets its own `make-hash`), so the depth-1
;; subgoal can't reuse the depth-2 subgoal's dedup work. defrel/bank
;; has a single shared cache for the whole canonical run.

(require "../main.rkt"
         "bank.rkt")

;; --- per-target timeout via thread + custodian (copied from deep-bench) ---

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

(define (timed-run budget-ms thunk)
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (define result
    (with-time-limit budget-ms thunk (lambda () 'TIMEOUT)))
  (define elapsed (- (current-inexact-milliseconds) start))
  (values result elapsed))

(define (time-it iters thunk)
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (define result #f)
  (for ([i (in-range iters)])
    (set! result (thunk)))
  (define elapsed (- (current-inexact-milliseconds) start))
  (values result (/ elapsed iters)))

(define (pad-right n s)
  (if (>= (string-length s) n)
      s
      (string-append s (make-string (- n (string-length s)) #\space))))

(define (run-target target target-bank target-bounded)
  (define name (car target))
  (define io-pairs (cadr target))
  (define depth (caddr target))
  (define iters (cadddr target))
  (define-values (bank-result bank-ms) (time-it iters target-bank))
  (define-values (bounded-result bounded-ms) (time-it iters target-bounded))
  (printf "  ~a  depth=~a   bounded ~ams   bank ~ams   ratio ~ax~n"
          (pad-right 24 name)
          depth
          (pad-right 7 (real->decimal-string bounded-ms 3))
          (pad-right 7 (real->decimal-string bank-ms 3))
          (real->decimal-string (/ bank-ms bounded-ms) 2))
  (unless (and (pair? bank-result) (pair? bounded-result))
    (printf "    !!! one of the searches returned no answer~n"))
  (printf "    bounded found: ~v~n" (and (pair? bounded-result) (car bounded-result)))
  (printf "    bank    found: ~v~n" (and (pair? bank-result) (car bank-result))))

;; ============================================================
;; Domain 1: Arithmetic
;; ============================================================

(define arith-inputs '(2 3 4))

(define (arith-interp e x)
  (cond
    [(eq? e 'x) x]
    [(number? e) e]
    [(eq? (car e) 'plus)  (+ (arith-interp (cadr e) x) (arith-interp (caddr e) x))]
    [(eq? (car e) 'times) (* (arith-interp (cadr e) x) (arith-interp (caddr e) x))]))

(define (arith-key e)
  (ground-key e (lambda (t) (map (lambda (x) (arith-interp t x)) arith-inputs))))

(define (arith-matches e io-pairs)
  (when-ground e (lambda (t)
    (andmap (lambda (io) (equal? (arith-interp t (car io)) (cdr io))) io-pairs))))

(defrel/bank (arith-bank e)
  #:prune (arith-key e)
  (conde
    [(== e 'x)] [(== e 0)] [(== e 1)]
    [(fresh (l r) (conde [(== e `(plus ,l ,r))] [(== e `(times ,l ,r))])
       (arith-bank l) (arith-bank r))]))

(define (arith-bounded e depth)
  (prune (arith-key e)
    (cond
      [(zero? depth) (conde [(== e 'x)] [(== e 0)] [(== e 1)])]
      [else
       (conde
         [(== e 'x)] [(== e 0)] [(== e 1)]
         [(fresh (l r) (conde [(== e `(plus ,l ,r))] [(== e `(times ,l ,r))])
            (arith-bounded l (- depth 1)) (arith-bounded r (- depth 1)))])])))

;; (name io-pairs minimum-depth iterations)
(define arith-targets
  `(("identity: x"
     ((2 . 2) (3 . 3) (4 . 4))                       0 1000)
    ("square: x*x"
     ((2 . 4) (3 . 9) (4 . 16))                      1 500)
    ("x^2 + x"
     ((2 . 6) (3 . 12) (4 . 20))                     2 200)
    ("x^2 + 2x + 1 = (x+1)^2"
     ((2 . 9) (3 . 16) (4 . 25))                     2 200)
    ("(1+x)^2 + 1"
     ((2 . 10) (3 . 17) (4 . 26))                    3 50)
    ("x^3"
     ((2 . 8) (3 . 27) (4 . 64))                     2 100)
    ("x^3 + 1"
     ((2 . 9) (3 . 28) (4 . 65))                     3 50)))

(define (arith-bench)
  (printf "~n============================================================~n")
  (printf "Arithmetic synthesis  (inputs: ~v)~n" arith-inputs)
  (printf "Grammar: e ::= x | 0 | 1 | (plus e e) | (times e e)~n")
  (printf "============================================================~n")
  (for ([target (in-list arith-targets)])
    (define io-pairs (cadr target))
    (define depth (caddr target))
    (run-target target
      (lambda () (run 1 (e) (arith-bank e) (arith-matches e io-pairs)))
      (lambda () (run 1 (e) (arith-bounded e depth) (arith-matches e io-pairs))))))

;; ============================================================
;; Domain 2: String manipulation (Polikarpova-style)
;; ============================================================

(define str-inputs '("world" "Alice" "Bob"))

(define (str-interp e s)
  (cond
    [(eq? e 'in) s]
    [(string? e) e]
    [(eq? (car e) 'concat)
     (string-append (str-interp (cadr e) s) (str-interp (caddr e) s))]))

(define (str-key e)
  (ground-key e (lambda (t) (map (lambda (s) (str-interp t s)) str-inputs))))

(define (str-matches e io-pairs)
  (when-ground e (lambda (t)
    (andmap (lambda (io) (equal? (str-interp t (car io)) (cdr io))) io-pairs))))

;; String literals available as terminals. In a real PBE system these
;; would be mined from the I/O examples (Polikarpova's approach uses
;; substrings of the outputs that aren't substrings of the inputs).
(define str-literals '("" " " "!" "?" ", " "Hello, " "Hi, " "Dear "))

(defrel/bank (str-bank e)
  #:prune (str-key e)
  (conde
    [(== e 'in)]
    [(membero e str-literals)]
    [(fresh (l r) (== e `(concat ,l ,r))
       (str-bank l) (str-bank r))]))

;; Weighted variant for best-first enumeration. Literals must be
;; spelled out as conde-w branches so that each contributes a uniform
;; ceiling weight; recursive concat branches get scale-w'd by the
;; default decay.
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

;; Host-language bottom-up bank for strings.
(define str-terminals (cons 'in str-literals))

(define (str-grammar-step bank)
  (for*/list ([l (in-list bank)]
              [r (in-list bank)])
    (list 'concat l r)))

(define (str-behavior p) (map (lambda (s) (str-interp p s)) str-inputs))

(define (str-host-bank-result depth io-pairs)
  (define bank (build-bank/depth str-grammar-step str-terminals
                                 str-behavior depth))
  (run 1 (e) (membero e bank) (str-matches e io-pairs)))

(define str-targets
  `(("greeting: 'Hello, X!'"
     (("world" . "Hello, world!")
      ("Alice" . "Hello, Alice!")
      ("Bob"   . "Hello, Bob!"))
     2 100)
    ("informal greeting: 'Hi, X?'"
     (("world" . "Hi, world?")
      ("Alice" . "Hi, Alice?")
      ("Bob"   . "Hi, Bob?"))
     2 100)
    ("echo-with-comma: 'X, X'"
     (("world" . "world, world")
      ("Alice" . "Alice, Alice")
      ("Bob"   . "Bob, Bob"))
     2 200)
    ("greeting+shout: 'Hello, X!!'"
     (("world" . "Hello, world!!")
      ("Alice" . "Hello, Alice!!")
      ("Bob"   . "Hello, Bob!!"))
     3 10)))

(define (fmt-result v)
  (cond
    [(eq? v 'TIMEOUT) "TIMEOUT"]
    [(pair? v) (format "~v" (car v))]
    [(null? v) "no-answer"]
    [else (format "~v" v)]))

;; Per-target budget for the bank-w engine on string targets. bank-w
;; can be very slow on wide behavior spaces, so we wrap it in a
;; timeout rather than relying on the iteration count to bound it.
(define str-bank-w-budget-ms 30000)

(define (str-bench)
  (printf "~n============================================================~n")
  (printf "String synthesis  (inputs: ~v)~n" str-inputs)
  (printf "Grammar: e ::= in | <literal> | (concat e e)~n")
  (printf "Literals: ~v~n" str-literals)
  (printf "============================================================~n")
  (for ([target (in-list str-targets)])
    (define name (car target))
    (define io-pairs (cadr target))
    (define depth (caddr target))
    (define iters (cadddr target))
    (printf "  ~a   depth=~a  (iters=~a)~n"
            (pad-right 30 name) depth iters)
    (flush-output)

    (define-values (bounded-r bounded-ms)
      (time-it iters (lambda () (run 1 (e) (str-bounded e depth) (str-matches e io-pairs)))))
    (printf "    bounded:    ~ams  ~a~n"
            (pad-right 8 (real->decimal-string bounded-ms 3))
            (fmt-result bounded-r))
    (flush-output)

    (define-values (bank-r bank-ms)
      (time-it iters (lambda () (run 1 (e) (str-bank e) (str-matches e io-pairs)))))
    (printf "    bank:       ~ams  ~a~n"
            (pad-right 8 (real->decimal-string bank-ms 3))
            (fmt-result bank-r))
    (flush-output)

    (define-values (bank-w-r bank-w-ms)
      (timed-run str-bank-w-budget-ms
        (lambda () (run-w 1 (e) (str-bank-w e) (str-matches e io-pairs)))))
    (printf "    bank-w:     ~ams  ~a~n"
            (pad-right 8 (real->decimal-string bank-w-ms 3))
            (fmt-result bank-w-r))
    (flush-output)

    (define-values (host-r host-ms)
      (time-it iters (lambda () (str-host-bank-result depth io-pairs))))
    (printf "    host-bank:  ~ams  ~a~n"
            (pad-right 8 (real->decimal-string host-ms 3))
            (fmt-result host-r))
    (printf "~n")
    (flush-output)))

(module+ main
  (arith-bench)
  (str-bench))
