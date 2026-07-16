#lang racket/base

;; miniKanren-style wrappers around the microKanren core: variadic
;; conde / fresh, run / run*, plus the stream driver and reifier.
;; Follows section 4 of Hemann & Friedman (2013).

(require (for-syntax racket/base)
         "microkanren.rkt")

(provide Zzz conj+ disj+ conde fresh
         conj-i conj-i+ conde-i fresh-i
         Zzz-w conj-w conj-w+ disj-w disj-w+ conde-w fresh-w
         run run* run-w run*-w
         pull take take-all pull-w take-w take-all-w
         walk*
         current-memo)

;; Memoization cache for defrel/memo, populated per `run` invocation.
;; #f means "no memo session active" -- memoized relations fall back to
;; running their body normally.
(define current-memo (make-parameter #f))

;; Inverse-eta delay: wraps a goal so that its stream is a thunk, which
;; lets disj+/conj+ recur into (potentially nonterminating) goals safely.
(define-syntax Zzz
  (syntax-rules ()
    [(_ g) (lambda (s/c) (lambda () (g s/c)))]))

(define-syntax conj+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g0 g ...) (conj (Zzz g0) (conj+ g ...))]))

(define-syntax disj+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g0 g ...) (disj (Zzz g0) (disj+ g ...))]))

(define-syntax conde
  (syntax-rules ()
    [(_ (g0 g ...) ...) (disj+ (conj+ g0 g ...) ...)]))

(define-syntax fresh
  (syntax-rules ()
    [(_ () g0 g ...) (conj+ g0 g ...)]
    [(_ (x0 x ...) g0 g ...)
     (call/fresh (lambda (x0) (fresh (x ...) g0 g ...)))]))

;; --- Fair interleaving variants (Kiselyov-Shan-Friedman-Sabry 2005) ---
;;
;; conj-i  : like conj but uses bind-i instead of bind.
;; conj-i+ : variadic, like conj+ but each composition is interleaving.
;; fresh-i : like fresh but combines its body with conj-i+.
;; conde-i : like conde but uses conj-i+ inside each clause.
;;
;; Use these when conj's depth bias hurts -- typically when the body
;; has independent recursive subgoals like `(rel l) (rel r)` and you
;; want fair coverage of (l, r) pairs along antidiagonals rather than
;; a nested-loop enumeration. The cost is one extra thunk allocation
;; per emitted state.

(define (conj-i g1 g2) (lambda (s/c) (bind-i (g1 s/c) g2)))

(define-syntax conj-i+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g0 g ...) (conj-i (Zzz g0) (conj-i+ g ...))]))

(define-syntax conde-i
  (syntax-rules ()
    [(_ (g0 g ...) ...) (disj+ (conj-i+ g0 g ...) ...)]))

(define-syntax fresh-i
  (syntax-rules ()
    [(_ () g0 g ...) (conj-i+ g0 g ...)]
    [(_ (x0 x ...) g0 g ...)
     (call/fresh (lambda (x0) (fresh-i (x ...) g0 g ...)))]))

;; --- Weighted (best-first) combinators --------------------------------
;;
;; These operate on weighted streams (see microkanren.rkt). Each goal's
;; output is auto-lifted: == and other unweighted goals produce
;; weight-1 cells when consumed by a -w combinator. Goals returned by
;; defrel/bank-w already produce weighted streams and pass through
;; lift-w unchanged.

;; Zzz-w wraps a goal so its application produces an immature weighted
;; stream with a 1.0 weight ceiling. The ceiling is conservative --
;; a -w goal whose underlying cells are scaled down (e.g. by decay)
;; will report lower actual cell weights once forced, but the lazy's
;; advertised ceiling stays at 1.0 unless we have static info to do
;; better. scale-w can tighten the ceiling at relation boundaries.
(define-syntax Zzz-w
  (syntax-rules ()
    [(_ g) (lambda (s/c) (lazy 1.0 (lambda () (lift-w (g s/c)))))]))

(define (conj-w g1 g2)
  (lambda (s/c) (bind-w (lift-w (g1 s/c)) g2)))

(define (disj-w g1 g2)
  (lambda (s/c) (mplus-w (lift-w (g1 s/c)) (lift-w (g2 s/c)))))

(define-syntax conj-w+
  (syntax-rules ()
    [(_ g) (Zzz-w g)]
    [(_ g0 g ...) (conj-w (Zzz-w g0) (conj-w+ g ...))]))

(define-syntax disj-w+
  (syntax-rules ()
    [(_ g) (Zzz-w g)]
    [(_ g0 g ...) (disj-w (Zzz-w g0) (disj-w+ g ...))]))

(define-syntax conde-w
  (syntax-rules ()
    [(_ (g0 g ...) ...) (disj-w+ (conj-w+ g0 g ...) ...)]))

(define-syntax fresh-w
  (syntax-rules ()
    [(_ () g0 g ...) (conj-w+ g0 g ...)]
    [(_ (x0 x ...) g0 g ...)
     (call/fresh (lambda (x0) (fresh-w (x ...) g0 g ...)))]))

;; Weighted reify: extract state from weighted cell before reifying.
(define (reify-1st/w cell)
  (let* ([s/c (cdr cell)]
         [v (walk* (var 0) (car s/c))])
    (walk* v (reify-s v '()))))

;; pull/take for weighted streams: lazy structs (not procedures) signal
;; immature; force via lazy-thunk.
(define (pull-w $)
  (cond
    [(lazy? $) (pull-w ((lazy-thunk $)))]
    [else $]))

(define (take-w n $)
  (if (zero? n) '()
      (let ([$ (pull-w $)])
        (if (null? $) '()
            (cons (car $) (take-w (- n 1) (cdr $)))))))

(define (take-all-w $)
  (let ([$ (pull-w $)])
    (if (null? $) '()
        (cons (car $) (take-all-w (cdr $))))))

(define-syntax run-w
  (syntax-rules ()
    [(_ n (q) g0 g ...)
     (parameterize ([current-memo (make-hash)])
       (map reify-1st/w (take-w n ((fresh-w (q) g0 g ...) empty-state))))]
    [(_ n (x0 x ...) g0 g ...)
     (run-w n (q) (fresh-w (x0 x ...) (== q (list x0 x ...)) g0 g ...))]))

(define-syntax run*-w
  (syntax-rules ()
    [(_ (q) g0 g ...)
     (parameterize ([current-memo (make-hash)])
       (map reify-1st/w (take-all-w ((fresh-w (q) g0 g ...) empty-state))))]
    [(_ (x0 x ...) g0 g ...)
     (run*-w (q) (fresh-w (x0 x ...) (== q (list x0 x ...)) g0 g ...))]))

;; --- stream driver ---

(define (pull $) (if (procedure? $) (pull ($)) $))

(define (take-all $)
  (let ([$ (pull $)])
    (if (null? $) '()
        (cons (car $) (take-all (cdr $))))))

(define (take n $)
  (if (zero? n) '()
      (let ([$ (pull $)])
        (if (null? $) '()
            (cons (car $) (take (- n 1) (cdr $)))))))

;; --- reification ---

(define (walk* v s)
  (let ([v (walk v s)])
    (cond
      [(var? v) v]
      [(pair? v) (cons (walk* (car v) s) (walk* (cdr v) s))]
      [else v])))

(define (reify-name n)
  (string->symbol (string-append "_." (number->string n))))

(define (reify-s v s)
  (let ([v (walk v s)])
    (cond
      [(var? v) (cons (cons v (reify-name (length s))) s)]
      [(pair? v) (reify-s (cdr v) (reify-s (car v) s))]
      [else s])))

;; The first fresh variable introduced from empty-state has index 0;
;; the run macro arranges for that variable to hold the query value.
(define (reify-1st s/c)
  (let ([v (walk* (var 0) (car s/c))])
    (walk* v (reify-s v '()))))

;; --- run / run* ---
;;
;; Single-var form returns reified values directly.
;; Multi-var form bundles the query vars into a list under a hygienic q.

(define-syntax run
  (syntax-rules ()
    [(_ n (q) g0 g ...)
     (parameterize ([current-memo (make-hash)])
       (map reify-1st (take n ((fresh (q) g0 g ...) empty-state))))]
    [(_ n (x0 x ...) g0 g ...)
     (run n (q) (fresh (x0 x ...) (== q (list x0 x ...)) g0 g ...))]))

(define-syntax run*
  (syntax-rules ()
    [(_ (q) g0 g ...)
     (parameterize ([current-memo (make-hash)])
       (map reify-1st (take-all ((fresh (q) g0 g ...) empty-state))))]
    [(_ (x0 x ...) g0 g ...)
     (run* (q) (fresh (x0 x ...) (== q (list x0 x ...)) g0 g ...))]))
