#lang racket/base

;; Depth-less variant of pbe-example.rkt.
;;
;; The recursive `expr` clause has no depth bound -- it relies on:
;;   1. `Zzz` (inserted by conde/fresh) to keep recursive calls lazy, so
;;      (expr l) / (expr r) aren't forced until the search pulls on them;
;;   2. miniKanren's fair mplus interleaving, so every finite candidate is
;;      eventually reached;
;;   3. `prune` to dedup observationally-equivalent candidates, so the
;;      search doesn't drown in syntactic redundancy.
;;
;; `run 1` stops at the first match, so we don't need a termination
;; argument for the full enumeration -- just that the target behavior is
;; reachable in finite interleaved search.

(require "../main.rkt")

(define inputs '(2 3 4))

(define (interp e x)
  (cond
    [(eq? e 'x) x]
    [(number? e) e]
    [(and (pair? e) (eq? (car e) 'plus))
     (+ (interp (cadr e) x) (interp (caddr e) x))]
    [(and (pair? e) (eq? (car e) 'times))
     (* (interp (cadr e) x) (interp (caddr e) x))]
    [else (error 'interp "bad expression: ~v" e)]))

(define (expr e)
  (prune (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs)))
    (conde
      [(== e 'x)]
      [(== e 0)]
      [(== e 1)]
      [(fresh (l r)
         (conde
           [(== e `(plus  ,l ,r))]
           [(== e `(times ,l ,r))])
         (expr l)
         (expr r))])))

(module+ main
  (define io-pairs '((2 . 4) (3 . 9) (4 . 16)))
  (printf "synthesizing without depth bound...~n")
  (define start (current-inexact-milliseconds))
  (define answers
    (run 1 (e)
      (expr e)
      (when-ground e
        (lambda (t)
          (andmap (lambda (io) (equal? (interp t (car io)) (cdr io)))
                  io-pairs)))))
  (define elapsed (- (current-inexact-milliseconds) start))
  (cond
    [(null? answers) (displayln "  no program found")]
    [else (printf "  found: ~v (in ~ams)~n" (car answers) (inexact->exact (round elapsed)))]))
