#lang racket/base

;; Micro-benchmark: depth-bounded `expr` vs depth-less `expr`, both
;; searching for an arithmetic expression behaving as x*x on (2 3 4).

(require "../main.rkt"
         "bank.rkt")

(define inputs '(2 3 4))

;; Easy target: x*x. Reachable at depth 1.
(define easy-io '((2 . 4) (3 . 9) (4 . 16)))

;; Harder target: (1+x)^2 + 1. Reachable at depth 3:
;;   (plus 1 (times (plus 1 x) (plus 1 x)))
;; On inputs (2 3 4), evaluates to (10 17 26).
(define hard-io '((2 . 10) (3 . 17) (4 . 26)))

(define (interp e x)
  (cond
    [(eq? e 'x) x]
    [(number? e) e]
    [(and (pair? e) (eq? (car e) 'plus))
     (+ (interp (cadr e) x) (interp (caddr e) x))]
    [(and (pair? e) (eq? (car e) 'times))
     (* (interp (cadr e) x) (interp (caddr e) x))]
    [else (error 'interp "bad expression: ~v" e)]))

(define (behavior-key e)
  (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs))))

(define (matches e io-pairs)
  (when-ground e
    (lambda (t)
      (andmap (lambda (io) (equal? (interp t (car io)) (cdr io)))
              io-pairs))))

;; depth-bounded
(define (expr-bounded e depth)
  (prune (behavior-key e)
    (cond
      [(zero? depth)
       (conde [(== e 'x)] [(== e 0)] [(== e 1)])]
      [else
       (conde
         [(== e 'x)]
         [(== e 0)]
         [(== e 1)]
         [(fresh (l r)
            (conde
              [(== e `(plus  ,l ,r))]
              [(== e `(times ,l ,r))])
            (expr-bounded l (- depth 1))
            (expr-bounded r (- depth 1)))])])))

;; depth-less
(define (expr-unbounded e)
  (prune (behavior-key e)
    (conde
      [(== e 'x)]
      [(== e 0)]
      [(== e 1)]
      [(fresh (l r)
         (conde
           [(== e `(plus  ,l ,r))]
           [(== e `(times ,l ,r))])
         (expr-unbounded l)
         (expr-unbounded r))])))

(define (synth-bounded depth io-pairs)
  (run 1 (e) (expr-bounded e depth) (matches e io-pairs)))

(define (synth-unbounded io-pairs)
  (run 1 (e) (expr-unbounded e) (matches e io-pairs)))

;; --- bank-based ---

(define (behavior p) (map (lambda (x) (interp p x)) inputs))

(define (arithmetic-step bank)
  (for*/list ([l (in-list bank)]
              [r (in-list bank)]
              [op (in-list '(plus times))])
    (list op l r)))

(define terminals '(x 0 1))

(define (synth-bank d io-pairs)
  (define bank (build-bank/depth arithmetic-step terminals behavior d))
  (run 1 (e) (membero e bank) (matches e io-pairs)))

;; Search-only timing using a pre-built bank.
(define (synth-bank/prebuilt bank io-pairs)
  (run 1 (e) (membero e bank) (matches e io-pairs)))

(define (time-it label n thunk)
  ;; warm up
  (for ([i (in-range 50)]) (thunk))
  ;; measure
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (for ([i (in-range n)]) (thunk))
  (define elapsed (- (current-inexact-milliseconds) start))
  (define per-iter (/ elapsed n))
  (printf "  ~a: ~a iters in ~a ms  ->  ~a ms/iter~n"
          label n
          (real->decimal-string elapsed 1)
          (real->decimal-string per-iter 4))
  per-iter)

(module+ main
  (printf "=== easy target: x*x  (reachable at depth 1) ===~n")
  (printf "results:~n")
  (printf "  bounded depth=2: ~v~n" (synth-bounded 2 easy-io))
  (printf "  unbounded:       ~v~n" (synth-unbounded easy-io))
  (printf "  bank depth=2:    ~v~n" (synth-bank 2 easy-io))
  (printf "timing (1000 iters):~n")
  (define bank-easy (build-bank/depth arithmetic-step terminals behavior 2))
  (printf "  (bank depth=2 has ~a entries)~n" (length bank-easy))
  (define te-b (time-it "bounded depth=2     " 1000
                        (lambda () (synth-bounded 2 easy-io))))
  (define te-u (time-it "unbounded           " 1000
                        (lambda () (synth-unbounded easy-io))))
  (define te-bank (time-it "bank depth=2 (total)" 1000
                           (lambda () (synth-bank 2 easy-io))))
  (define te-bs (time-it "bank (search only)  " 1000
                         (lambda () (synth-bank/prebuilt bank-easy easy-io))))
  (printf "  bank/bounded speedup (search only): ~ax~n"
          (real->decimal-string (/ te-b te-bs) 2))

  (printf "~n=== hard target: (1+x)^2 + 1  (reachable at depth 3) ===~n")
  (printf "results:~n")
  (printf "  bounded depth=2: ~v~n" (synth-bounded 2 hard-io))
  (printf "  bounded depth=3: ~v~n" (synth-bounded 3 hard-io))
  (printf "  unbounded:       ~v~n" (synth-unbounded hard-io))
  (printf "  bank depth=3:    ~v~n" (synth-bank 3 hard-io))
  (printf "timing (50 iters):~n")
  (define bank-hard (build-bank/depth arithmetic-step terminals behavior 3))
  (printf "  (bank depth=3 has ~a entries)~n" (length bank-hard))
  (define th-3 (time-it "bounded depth=3     " 50
                        (lambda () (synth-bounded 3 hard-io))))
  (define th-5 (time-it "bounded depth=5     " 50
                        (lambda () (synth-bounded 5 hard-io))))
  (define th-u (time-it "unbounded           " 50
                        (lambda () (synth-unbounded hard-io))))
  (define th-bank (time-it "bank depth=3 (total)" 50
                           (lambda () (synth-bank 3 hard-io))))
  (define th-bs (time-it "bank (search only)  " 50
                         (lambda () (synth-bank/prebuilt bank-hard hard-io))))
  (printf "  bank/bounded speedup (search only): ~ax~n"
          (real->decimal-string (/ th-3 th-bs) 2))
  (printf "  bank/bounded speedup (total):       ~ax~n"
          (real->decimal-string (/ th-3 th-bank) 2)))
