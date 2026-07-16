#lang racket/base

;; Benchmark defrel/memo against the bounded and unbounded variants.

(require "../main.rkt")

(define inputs '(2 3 4))
(define easy-io '((2 . 4) (3 . 9) (4 . 16)))
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

(define (matches e io-pairs)
  (when-ground e
    (lambda (t)
      (andmap (lambda (io) (equal? (interp t (car io)) (cdr io)))
              io-pairs))))

;; depth-bounded reference
(define (expr-bounded e depth)
  (prune (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs)))
    (cond
      [(zero? depth)
       (conde [(== e 'x)] [(== e 0)] [(== e 1)])]
      [else
       (conde
         [(== e 'x)] [(== e 0)] [(== e 1)]
         [(fresh (l r)
            (conde [(== e `(plus  ,l ,r))] [(== e `(times ,l ,r))])
            (expr-bounded l (- depth 1)) (expr-bounded r (- depth 1)))])])))

;; depth-less memoized -- NO prune, just memo
(defrel/memo (expr-memo e)
  (conde
    [(== e 'x)] [(== e 0)] [(== e 1)]
    [(fresh (l r)
       (conde [(== e `(plus  ,l ,r))] [(== e `(times ,l ,r))])
       (expr-memo l) (expr-memo r))]))

;; depth-less memo + prune by behavior
(defrel/bank (expr-bank e)
  #:prune (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs)))
  (conde
    [(== e 'x)] [(== e 0)] [(== e 1)]
    [(fresh (l r)
       (conde [(== e `(plus  ,l ,r))] [(== e `(times ,l ,r))])
       (expr-bank l) (expr-bank r))]))

(define (time-it label thunk)
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (define result (thunk))
  (define elapsed (- (current-inexact-milliseconds) start))
  (printf "  ~a: ~v  (~a ms)~n"
          label result (real->decimal-string elapsed 1))
  ;; Return void: a non-void value at module level would print twice.
  (void))

(module+ main
  (printf "=== easy target: x*x ===~n")
  (time-it "bounded d=2 " (lambda () (run 1 (e) (expr-bounded e 2) (matches e easy-io))))
  (time-it "memo (no prune)" (lambda () (run 1 (e) (expr-memo e) (matches e easy-io))))
  (time-it "bank (memo+prune)" (lambda () (run 1 (e) (expr-bank e) (matches e easy-io))))

  (printf "~n=== hard target: (1+x)^2 + 1 ===~n")
  (time-it "bounded d=3 " (lambda () (run 1 (e) (expr-bounded e 3) (matches e hard-io))))
  (time-it "memo (no prune)" (lambda () (run 1 (e) (expr-memo e) (matches e hard-io))))
  (time-it "bank (memo+prune)" (lambda () (run 1 (e) (expr-bank e) (matches e hard-io)))))
