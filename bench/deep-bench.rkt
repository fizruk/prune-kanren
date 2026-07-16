#lang racket/base

;; Deep arithmetic PBE benchmark -- targets at depth 4 and beyond.
;;
;; Depth convention: (op a b) has depth 1 + max(depth(a), depth(b));
;; leaves are depth 0. Right-associated x^k has depth k-1, and
;; (1+x)^k right-assoc has depth k.
;;
;; Each target runs under a per-call wall-clock budget. If a run
;; doesn't finish in time, it's reported as "TIMEOUT". This keeps the
;; bench finite even when one strategy runs into a hard case.
;;
;; Three strategies are compared per target:
;;
;;   bounded   -- depth-bounded with prune (idiomatic miniKanren). User
;;               must know the right depth.
;;   bank      -- defrel/bank: depth-first canonical enumeration with
;;               shared prune cache. Fast for right-spine targets
;;               (x^k); the canonical order makes (1+x)^k slow because
;;               its compact representative sits very late in the
;;               enumeration.
;;   bank-w    -- defrel/bank-w: depth-decayed best-first enumeration
;;               (decay=0.5). Weights on immature streams (the `lazy`
;;               struct) prevent the memo-thunk re-entry that would
;;               otherwise occur. Finds the most compact representative
;;               first; pays for it on deep targets because it must
;;               emit all shallower cells first (BFS-style).
;;
;; --- Results (author's machine, heap-based mplus-w) --------------------------
;;
;; Target     d   bounded     bank (DFS)      bank-w (BFS)    Bank-w compact?
;; -------------------------------------------------------------------------
;; (1+x)^2    2   0.2 ms      0.2 ms (d=4)    16 ms (d=2)     YES
;; (1+x)^3    3   3.3 ms      9.9 ms (d=8)    5.3 s (d=3)     YES
;; x^5        4   0.6 ms      0.1 ms (d=4)    126 ms (d=4)    YES (left-assoc)
;; (1+x)^4    4   139 ms      1993 ms (d=10)  TIMEOUT (30s)   --
;; x^5 + x    5   3.3 ms      0.1 ms          14.7 s          YES (left-assoc)
;; x^5 + 1    5   24 ms       0.7 ms          26.4 s          YES (left-assoc)
;; x^6        5   3.6 ms      0.2 ms          12.6 s          YES (balanced)
;; (1+x)^5    5   6.6 s       TIMEOUT (30s)   TIMEOUT (30s)   --
;; x^6 + 1    6   139 ms      1.4 ms          TIMEOUT (60s)   --
;; x^7        6   20 ms       0.3 ms          TIMEOUT (60s)   --
;;
;; Summary:
;;
;;   - bank (DFS) wins big on right-spine targets (x^k, x^k+1, x^k+x) --
;;     10-100x faster than bounded. Compact representatives too.
;;   - bank-w (BFS) reliably finds the COMPACT representative when it
;;     succeeds, and with the pairing-heap mplus-w it solves 6 of 10
;;     targets (the earlier binary-merge nests solved only 2: each
;;     pull re-traversed the whole frontier of suspended
;;     alternatives). Deep arithmetic still overwhelms it: every cell
;;     of a weight class must be emitted before any lower class, and
;;     class sizes grow with the number of distinct behaviors.
;;   - (1+x)^4 and (1+x)^5 defeat both bank variants; only bounded
;;     finds them by virtue of its hard depth cut.
;;
;; Neither bank variant dominates. Use defrel/bank for performance on
;; right-spine-like grammars; use defrel/bank-w when the behavior
;; space is wide but the target is shallow, or when you need the
;; compact representative. Use bounded when you know the depth and
;; want predictable behavior.

(require "../main.rkt"
         "bank.rkt")

;; --- per-target timeout via thread + custodian ---

(define (with-time-limit ms thunk on-timeout)
  (define result-ch (make-channel))
  (define cust (make-custodian))
  (define t
    (parameterize ([current-custodian cust])
      (thread
        (lambda ()
          (with-handlers ([exn:fail? (lambda (e) (channel-put result-ch (cons 'error e)))])
            (channel-put result-ch (cons 'ok (thunk))))))))
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
    (with-time-limit budget-ms
      thunk
      (lambda () 'TIMEOUT)))
  (define elapsed (- (current-inexact-milliseconds) start))
  (values result elapsed))

;; --- problem setup ---

(define inputs '(2 3 4))

(define (interp e x)
  (cond
    [(eq? e 'x) x]
    [(number? e) e]
    [(eq? (car e) 'plus)  (+ (interp (cadr e) x) (interp (caddr e) x))]
    [(eq? (car e) 'times) (* (interp (cadr e) x) (interp (caddr e) x))]))

(define (arith-key e)
  (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs))))

(define (matches e io-pairs)
  (when-ground e (lambda (t)
    (andmap (lambda (io) (equal? (interp t (car io)) (cdr io))) io-pairs))))

;; Standard depth-first bank -- uses `conj` and emits cells in
;; canonical recursion order. Fast on "right-spine" targets like x^k;
;; loses on (1+x)^k because the natural representative appears late
;; in the canonical enumeration order.
(defrel/bank (arith-bank e)
  #:prune (arith-key e)
  (conde
    [(== e 'x)] [(== e 0)] [(== e 1)]
    [(fresh (l r) (conde [(== e `(plus ,l ,r))] [(== e `(times ,l ,r))])
       (arith-bank l) (arith-bank r))]))

;; Depth-decayed best-first bank -- weighted streams with decay=0.5
;; per recursive call. Finds the most compact (shallowest)
;; representative for each behavior. Slower on deep targets because
;; it explores all shallower cells first.
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

;; --- host-language bottom-up bank ---
;;
;; Builds the deduplicated bank in Racket (no relational composition)
;; and then exposes its membership predicate to a relational query via
;; `membero`. End-to-end time includes bank build.

(define arith-terminals '(x 0 1))

(define (arith-grammar-step bank)
  (for*/list ([l (in-list bank)]
              [r (in-list bank)]
              [op (in-list '(plus times))])
    (list op l r)))

(define (arith-behavior p) (map (lambda (x) (interp p x)) inputs))

(define (arith-host-bank-result depth io-pairs)
  (define bank (build-bank/depth arith-grammar-step arith-terminals
                                 arith-behavior depth))
  (run 1 (e) (membero e bank) (matches e io-pairs)))

;; --- targets ---

;; (name io-pairs minimum-depth budget-ms)
(define targets
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

(define (pad-right n s)
  (if (>= (string-length s) n)
      s
      (string-append s (make-string (- n (string-length s)) #\space))))

(define (fmt v)
  (cond
    [(eq? v 'TIMEOUT) "TIMEOUT"]
    [(pair? v) (format "~v" (car v))]
    [(null? v) "no-answer"]
    [else (format "~v" v)]))

(module+ main
  (printf "Deep arithmetic PBE benchmark  (inputs: ~v)~n" inputs)
  (printf "Grammar: e ::= x | 0 | 1 | (plus e e) | (times e e)~n")
  (printf "============================================================~n")
  (flush-output)
  (for ([target (in-list targets)])
    (define name     (car target))
    (define io-pairs (cadr target))
    (define depth    (caddr target))
    (define budget   (cadddr target))

    (printf "  ~a   (budget=~as)~n"
            (pad-right 18 name)
            (real->decimal-string (/ budget 1000) 0))
    (flush-output)

    (define-values (bounded-r bounded-ms)
      (timed-run budget
        (lambda () (run 1 (e) (arith-bounded e depth) (matches e io-pairs)))))
    (printf "    bounded(d=~a):  ~ams ~a~n"
            depth
            (pad-right 9 (real->decimal-string bounded-ms 1))
            (fmt bounded-r))
    (flush-output)

    (define-values (bank-r bank-ms)
      (timed-run budget
        (lambda () (run 1 (e) (arith-bank e) (matches e io-pairs)))))
    (printf "    bank (DFS  ):  ~ams ~a~n"
            (pad-right 9 (real->decimal-string bank-ms 1))
            (fmt bank-r))
    (flush-output)

    (define-values (bank-w-r bank-w-ms)
      (timed-run budget
        (lambda () (run-w 1 (e) (arith-bank-w e) (matches e io-pairs)))))
    (printf "    bank-w (BFS): ~ams ~a~n"
            (pad-right 9 (real->decimal-string bank-w-ms 1))
            (fmt bank-w-r))
    (flush-output)

    (define-values (host-r host-ms)
      (timed-run budget
        (lambda () (arith-host-bank-result depth io-pairs))))
    (printf "    host-bank   :  ~ams ~a~n"
            (pad-right 9 (real->decimal-string host-ms 1))
            (fmt host-r))

    (define (ratio-str a-r a-ms b-r b-ms)
      (cond
        [(or (eq? a-r 'TIMEOUT) (eq? b-r 'TIMEOUT)) "(timeout)"]
        [else
         (define r (/ a-ms (max 0.001 b-ms)))
         (cond [(< r 1) (string-append (real->decimal-string (/ 1 r) 2) "x FASTER")]
               [else    (string-append (real->decimal-string r 2) "x slower")])]))
    (printf "    => bank      vs bounded: ~a~n"
            (ratio-str bank-r bank-ms bounded-r bounded-ms))
    (printf "    => bank-w    vs bounded: ~a~n"
            (ratio-str bank-w-r bank-w-ms bounded-r bounded-ms))
    (printf "    => host-bank vs bounded: ~a~n"
            (ratio-str host-r host-ms bounded-r bounded-ms))
    (printf "    => host-bank vs bank:    ~a~n"
            (ratio-str host-r host-ms bank-r bank-ms))
    (printf "~n")
    (flush-output)))
