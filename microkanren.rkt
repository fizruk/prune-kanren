#lang racket/base

;; Minimal microKanren core, after Hemann & Friedman (2013).
;; No disequality constraints.

(provide var var? var=?
         walk unify
         empty-state
         == call/fresh disj conj
         mzero unit mplus bind)

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
