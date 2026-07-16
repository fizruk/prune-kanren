#lang racket/base

;; Experimental: shared dedup table across nested prunes via a parameter.
;; The outermost prune call creates the table; recursive prune calls
;; inherit it via current-prune-table. Tests whether sharing speeds up
;; the depth-less search AND preserves the synthesis answer.
;;
;; RESULT: sharing breaks completeness. Running this file hangs on the
;; easy target (`x*x`) before reaching the hard one. The reason: the
;; outer prune emits the leaf `(== e 'x)` first, adding behavior (2 3 4)
;; to the shared table. When the recursive branch then runs `(expr l)`
;; and `(expr r)` to try to form `(times x x)`, both children would be
;; `x` with behavior (2 3 4) -- which is now blocked by the table.
;; (times x x) is unreachable, and the search never finds another ground
;; term with behavior (4 9 16) so it loops forever pulling at the
;; depth-less stream.
;;
;; More generally: simple sharing breaks any synthesis target whose
;; sub-expressions share a behavior with anything already emitted.
;; This benchmark is kept as a witness to that failure. It is NOT meant
;; to be run unattended; the second run will hang.

(require "../main.rkt")

;; --- shared-table prune ---

(define current-prune-table (make-parameter #f))

(define (prune/shared key g)
  (let ([table (or (current-prune-table) (make-hash))])
    (lambda (s/c)
      (parameterize ([current-prune-table table])
        (prune-stream/shared key table (g s/c))))))

(define (prune-stream/shared key seen $)
  (cond
    [(null? $) '()]
    [(procedure? $)
     (lambda ()
       (parameterize ([current-prune-table seen])
         (prune-stream/shared key seen ($))))]
    [else
     (let* ([s/c (car $)]
            [k (key s/c)])
       (cond
         [(eq? k skip-prune)
          (cons s/c (prune-stream/shared key seen (cdr $)))]
         [(hash-has-key? seen k)
          (prune-stream/shared key seen (cdr $))]
         [else
          (hash-set! seen k #t)
          (cons s/c (prune-stream/shared key seen (cdr $)))]))]))

;; --- problem ---

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

(define (behavior-key e)
  (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs))))

(define (matches e io-pairs)
  (when-ground e
    (lambda (t)
      (andmap (lambda (io) (equal? (interp t (car io)) (cdr io)))
              io-pairs))))

;; --- expr with each prune flavor ---

(define (expr-orig e)
  (prune (behavior-key e)
    (conde
      [(== e 'x)] [(== e 0)] [(== e 1)]
      [(fresh (l r)
         (conde
           [(== e `(plus  ,l ,r))]
           [(== e `(times ,l ,r))])
         (expr-orig l) (expr-orig r))])))

(define (expr-shared e)
  (prune/shared (behavior-key e)
    (conde
      [(== e 'x)] [(== e 0)] [(== e 1)]
      [(fresh (l r)
         (conde
           [(== e `(plus  ,l ,r))]
           [(== e `(times ,l ,r))])
         (expr-shared l) (expr-shared r))])))

(define (time-it label thunk)
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (define result (thunk))
  (define elapsed (- (current-inexact-milliseconds) start))
  (printf "  ~a: result=~v  (~a ms)~n"
          label result (real->decimal-string elapsed 1))
  ;; Return void: a non-void value at module level would print twice.
  (void))

(module+ main
  (printf "=== easy target: x*x  (expected: (times x x)) ===~n")
  (time-it "expr-orig    " (lambda () (run 1 (e) (expr-orig e) (matches e easy-io))))
  (time-it "expr-shared  " (lambda () (run 1 (e) (expr-shared e) (matches e easy-io))))

  (printf "~n=== hard target: (1+x)^2+1 ===~n")
  (time-it "expr-orig    " (lambda () (run 1 (e) (expr-orig e) (matches e hard-io))))
  (time-it "expr-shared  " (lambda () (run 1 (e) (expr-shared e) (matches e hard-io)))))
