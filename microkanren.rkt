#lang racket/base

;; Minimal microKanren core, after Hemann & Friedman (2013).
;; No disequality constraints.

(provide var var? var=?
         walk unify
         empty-state
         == call/fresh disj conj
         mzero unit mplus bind
         mplus-i bind-i
         (struct-out lazy) peek-weight
         lift-w scale-w mplus-w bind-w)

;; Logic variables are 1-element vectors holding an integer index, so they are
;; distinguishable from other terms (e.g. plain integers) by unification.
(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

;; A substitution is an association list mapping variables to terms.

(define (assp p l)
  (cond
    [(null? l) #f]
    [(p (car (car l))) (car l)]
    [else (assp p (cdr l))]))

(define (walk u s)
  (let ([pr (and (var? u) (assp (lambda (v) (var=? u v)) s))])
    (if pr (walk (cdr pr) s) u)))

(define (ext-s x v s) (cons (cons x v) s))

(define (unify u v s)
  (let ([u (walk u s)] [v (walk v s)])
    (cond
      [(and (var? u) (var? v) (var=? u v)) s]
      [(var? u) (ext-s u v s)]
      [(var? v) (ext-s v u s)]
      [(and (pair? u) (pair? v))
       (let ([s (unify (car u) (car v) s)])
         (and s (unify (cdr u) (cdr v) s)))]
      [else (and (eqv? u v) s)])))

;; A state is (cons substitution fresh-var-counter).
(define empty-state '(() . 0))

;; Streams: '() is mzero; (cons s/c $) is a mature pair; a procedure of no
;; arguments is an immature stream used for inverse-eta delay.

(define mzero '())
(define (unit s/c) (cons s/c mzero))

(define (mplus $1 $2)
  (cond
    [(null? $1) $2]
    [(procedure? $1) (lambda () (mplus $2 ($1)))]
    [else (cons (car $1) (mplus (cdr $1) $2))]))

(define (bind $ g)
  (cond
    [(null? $) mzero]
    [(procedure? $) (lambda () (bind ($) g))]
    [else (mplus (g (car $)) (bind (cdr $) g))]))

;; Goals are functions from a state to a stream of states.

(define (== u v)
  (lambda (s/c)
    (let ([s (unify u v (car s/c))])
      (if s (unit (cons s (cdr s/c))) mzero))))

(define (call/fresh f)
  (lambda (s/c)
    (let ([c (cdr s/c)])
      ((f (var c)) (cons (car s/c) (+ c 1))))))

(define (disj g1 g2) (lambda (s/c) (mplus (g1 s/c) (g2 s/c))))
(define (conj g1 g2) (lambda (s/c) (bind (g1 s/c) g2)))

;; --- Fair interleaving variants ----------------------------------------
;;
;; Standard `bind` for conj is depth-biased: when stream $ is mature with
;; many states, `(mplus (g (car $)) (bind (cdr $) g))` recursively yields
;; all of (g (car $))'s mature head before the next state from (cdr $).
;; For a recursive relation like `(conj (expr l) (expr r))`, this means
;; the search drills down on (l = first-bank-cell, r = ...) before ever
;; advancing l, producing a strongly depth-biased canonical enumeration
;; order (see bench/deep-bench.rkt for empirical impact).
;;
;; `mplus-i` (interleave) and `bind-i` are the fair variants. After
;; emitting one element from $1, mplus-i suspends the remainder of $1
;; and switches to $2, forcing per-step alternation regardless of
;; whether the underlying streams are mature.
;;
;; References:
;;   Kiselyov, Shan, Friedman, Sabry. "Backtracking, Interleaving, and
;;     Terminating Monad Transformers." ICFP 2005. -- the `interleave`
;;     combinator on MonadPlus from which this is adapted.
;;   Byrd. "Relational Programming in miniKanren: Techniques,
;;     Applications, and Implementations." PhD thesis, Indiana
;;     University, 2009. -- discussion of conjunction fairness and
;;     interleaving alternatives.
;;
;; Note the asymmetry vs `mplus`: the `else` branch wraps the cdr in a
;; thunk so the consumer's next pull will alternate to $2. This costs
;; one thunk allocation per element but produces a fair diagonal
;; enumeration of (l, r) pairs.

(define (mplus-i $1 $2)
  (cond
    [(null? $1) $2]
    [(procedure? $1) (lambda () (mplus-i $2 ($1)))]
    [else (cons (car $1) (lambda () (mplus-i $2 (cdr $1))))]))

(define (bind-i $ g)
  (cond
    [(null? $) mzero]
    [(procedure? $) (lambda () (bind-i ($) g))]
    [else (mplus-i (g (car $)) (bind-i (cdr $) g))]))

;; --- Weighted streams (depth-decayed best-first) ----------------------
;;
;; A weighted stream is one of:
;;   '()                              -- empty
;;   (cons (cons weight state) rest)  -- mature head with explicit weight
;;   (lazy weight thunk)              -- immature, with a known upper bound
;;                                      on weights any forced cell could have
;;
;; Carrying a weight ceiling on immature streams is the critical design
;; choice: `mplus-w` can determine which side could possibly emit a
;; higher-weight cell *without forcing* either side. This avoids the
;; classic "peek requires force" trap that, in a recursive memoized
;; bank, would cause forcing of a memo-thunk while it's still being
;; computed (cycle / infinite recursion).
;;
;; Inspired by best-first proof search in Lean 4's aesop tactic
;; (Limperg & From, "Aesop: White-Box Best-First Proof Search for
;; Lean," CPP 2023), and by admissible heuristics in A*-style search
;; (Hart, Nilsson, Raphael 1968) -- `lazy-weight` plays the role of an
;; admissible upper bound on what the lazy can yield.
;;
;; Weight propagation:
;;   - Zzz-w wraps a goal as `(lazy 1.0 ...)` -- conservative default.
;;   - scale-w multiplies the lazy's ceiling (and each mature cell's
;;     weight) by `factor`.
;;   - bind-w on `(lazy w ...)` produces `(lazy w ...)` -- assumes the
;;     applied goal's output ceiling is <= 1.0 (true for unweighted
;;     goals; weighted goals are conservatively over-estimated).
;;   - mplus-w of two lazies returns a lazy with ceiling = max of the
;;     two ceilings (any cell emitted comes from one of them).
;;   - lift-w of an unweighted procedure stream wraps as `(lazy 1.0 ...)`.

(struct lazy (weight thunk) #:transparent)

(define (peek-weight $)
  (cond
    [(null? $) -inf.0]
    [(lazy? $) (lazy-weight $)]
    [else (caar $)]))

(define (weighted-cell? c)
  (and (pair? c) (pair? (car c)) (number? (caar c))))

;; lift-w : promote any stream to weighted form.
;; - Already weighted (mature with (weight . state) cell, or lazy) -> unchanged.
;; - Unweighted procedure -> wrap as lazy with ceiling 1.0.
;; - Unweighted mature stream -> tag each cell with weight 1.0.
(define (lift-w $)
  (cond
    [(null? $) '()]
    [(lazy? $) $]
    [(procedure? $) (lazy 1.0 (lambda () (lift-w ($))))]
    [(weighted-cell? $) $]
    [else (cons (cons 1.0 (car $)) (lift-w (cdr $)))]))

(define (scale-w factor $)
  (cond
    [(null? $) '()]
    [(lazy? $) (lazy (* factor (lazy-weight $))
                     (lambda () (scale-w factor ((lazy-thunk $)))))]
    [else (cons (cons (* factor (caar $)) (cdar $))
                (scale-w factor (cdr $)))]))

;; mplus-w: emit cells in descending weight order. Uses peek-weight to
;; decide which side wins without forcing the loser. Only forces a lazy
;; when its ceiling indicates it might still produce a winning cell.
;;
;; A merge of many alternatives (one per pending disjunct or bind
;; cell) is kept in a pairing max-heap keyed by peek-weight, rather
;; than in a nest of binary merges: with a binary nest, emitting the
;; next cell costs O(#alternatives), which dominates the run time of
;; best-first search (each pull re-traverses the whole frontier of
;; suspended alternatives). The heap is hidden behind the public
;; stream interface as `lazy-merge`, a subtype of `lazy` that
;; additionally carries the heap, so that nested mplus-w calls meld
;; heaps in O(1) while every other consumer treats the merge as an
;; ordinary immature stream.

(struct lazy-merge lazy (heap) #:transparent)

;; Pairing max-heap of (non-null, non-merge) streams keyed by
;; peek-weight. A heap is #f (empty) or (cons top-stream children),
;; where children is a list of heaps.
(define (heap-meld h1 h2)
  (cond
    [(not h1) h2]
    [(not h2) h1]
    [(>= (peek-weight (car h1)) (peek-weight (car h2)))
     (cons (car h1) (cons h2 (cdr h1)))]
    [else (cons (car h2) (cons h1 (cdr h2)))]))

(define (heap-meld-pairs hs)
  (cond
    [(null? hs) #f]
    [(null? (cdr hs)) (car hs)]
    [else (heap-meld (heap-meld (car hs) (cadr hs))
                     (heap-meld-pairs (cddr hs)))]))

;; heap-add: insert a stream, flattening nested merges by melding
;; their heaps directly.
(define (heap-add h $)
  (cond
    [(null? $) h]
    [(lazy-merge? $) (heap-meld h (lazy-merge-heap $))]
    [else (heap-meld h (cons $ '()))]))

;; heap->stream: expose a heap as a public weighted stream. If the
;; top is mature, emit its head cell and re-insert its tail. If the
;; top is immature, the whole merge is immature with the top's
;; ceiling; forcing it forces exactly one step of the top.
(define (heap->stream h)
  (cond
    [(not h) '()]
    [else
     (let ([top (car h)])
       (cond
         [(lazy? top)
          (lazy-merge (lazy-weight top)
                      (lambda ()
                        (let ([rest (heap-meld-pairs (cdr h))])
                          (heap->stream (heap-add rest ((lazy-thunk top))))))
                      h)]
         [else
          (let ([rest (heap-meld-pairs (cdr h))])
            (cons (car top) (heap->stream (heap-add rest (cdr top)))))]))]))

(define (mplus-w $1 $2)
  (heap->stream (heap-add (heap-add #f $1) $2)))

;; bind-w: for each (w, state) in $, apply g, scale by w. The output
;; ceiling is conservatively (lazy-weight $) -- assumes g's output is
;; bounded by 1.0. -w goals that produce smaller output simply emit
;; cells with lower weight; they still sort correctly because of how
;; scale-w decay propagates.
(define (bind-w $ g)
  (cond
    [(null? $) '()]
    [(lazy? $) (lazy (lazy-weight $)
                     (lambda () (bind-w ((lazy-thunk $)) g)))]
    [else
     (let ([w (caar $)] [s (cdar $)])
       (mplus-w (scale-w w (lift-w (g s)))
                (bind-w (cdr $) g)))]))
