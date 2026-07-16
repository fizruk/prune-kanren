#lang racket/base

;; Tiny PBE program-synthesis demo using prune-kanren.
;;
;; Synthesize an arithmetic expression e over a single input x such that:
;;   x=2 -> 4, x=3 -> 9, x=4 -> 16   (i.e. e = x*x).
;;
;; Grammar:
;;   e ::= 'x | 0 | 1 | (list 'plus e e) | (list 'times e e)
;;
;; Pruning: at each layer, dedup candidates by their value-vector on the
;; input examples. Because `prune` wraps the recursive subgoal, observational-
;; equivalence pruning propagates bottom-up -- `conj` only feeds one
;; representative per behavior into the next layer.
;;
;; --- Pruning impact ---------------------------------------------------------
;;
;; Candidates enumerated by `expr e d` (with prune) vs `expr-raw e d`
;; (identical grammar, no prune). Both numbers measured by `collect-all`:
;;
;;   depth  | unpruned    | pruned  | ratio
;;     0    |        3    |     3   |    1x
;;     1    |       21    |     7   |    3x
;;     2    |      885    |    29   |   30x
;;     3    |  1,566,453  |   437   | 3585x
;;
;; The branching factor of the unpruned grammar is 2 * |prev|^2 + 3, so
;; counts blow up as |prev|^2 each layer. Pruning replaces |prev| with the
;; number of distinct behaviors on the input examples, which grows much
;; more slowly.
;;
;; Concretely at depth 1, the 21 syntactic programs collapse to 7
;; equivalence classes (behaviors on inputs (2 3 4)). Pruning keeps one
;; rep per class and drops the rest:
;;
;;   [0 0 0]  keep  0            drop  (plus 0 0), (times x 0), (times 0 x),
;;                                     (times 0 0), (times 0 1), (times 1 0)
;;   [2 3 4]  keep  x            drop  (plus x 0), (plus 0 x),
;;                                     (times x 1), (times 1 x)
;;   [1 1 1]  keep  1            drop  (plus 0 1), (plus 1 0), (times 1 1)
;;   [3 4 5]  keep  (plus x 1)   drop  (plus 1 x)
;;   [4 6 8]  keep  (plus x x)         --
;;   [2 2 2]  keep  (plus 1 1)         --
;;   [4 9 16] keep  (times x x)        -- this is the target behavior
;;
;; (Which specific syntactic form is "kept" depends on miniKanren's
;; interleaved search order, not on source position.)

(require "../main.rkt")

;; --- problem-specific evaluator ---

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

;; --- grammar as a pruned goal ---

(define (expr e depth)
  (prune (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs)))
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
            (expr l (- depth 1))
            (expr r (- depth 1)))])])))

;; Same grammar, no prune -- for the comparison harness.
(define (expr-raw e depth)
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
          (expr-raw l (- depth 1))
          (expr-raw r (- depth 1)))])]))

;; --- comparison harness ---

(define (count-answers expr-builder d)
  (length (run* (e) (expr-builder e d))))

(define (group-by-behavior progs)
  (define table (make-hash))
  (for ([p (in-list progs)])
    (define b (map (lambda (x) (interp p x)) inputs))
    (hash-update! table b (lambda (xs) (cons p xs)) '()))
  (sort (hash->list table) > #:key (lambda (g) (length (cdr g)))))

(module+ main
  (printf "candidates per depth (without vs with prune):~n")
  (for ([d (in-list '(0 1 2 3))])
    (printf "  depth ~a: ~a -> ~a~n"
            d
            (count-answers expr-raw d)
            (count-answers expr d)))

  (printf "~nequivalence classes at depth 1 (unpruned enumeration):~n")
  (for ([g (in-list (group-by-behavior (run* (e) (expr-raw e 1))))])
    (printf "  ~v  (~a programs): ~v~n"
            (car g) (length (cdr g)) (cdr g)))

  (printf "~nsynthesis result:~n")
  (define io-pairs '((2 . 4) (3 . 9) (4 . 16)))
  (define answers
    (run 1 (e)
      (expr e 2)
      (when-ground e
        (lambda (t)
          (andmap (lambda (io) (equal? (interp t (car io)) (cdr io)))
                  io-pairs)))))
  (cond
    [(null? answers) (displayln "  no program found")]
    [else (printf "  found: ~v~n" (car answers))]))
