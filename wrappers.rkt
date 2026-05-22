#lang racket/base

;; miniKanren-style wrappers around the microKanren core: variadic
;; conde / fresh, run / run*, plus the stream driver and reifier.
;; Follows section 4 of Hemann & Friedman (2013).

(require (for-syntax racket/base)
         "microkanren.rkt")

(provide Zzz conj+ disj+ conde fresh
         run run*
         pull take take-all
         walk*)

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
     (map reify-1st (take n ((fresh (q) g0 g ...) empty-state)))]
    [(_ n (x0 x ...) g0 g ...)
     (run n (q) (fresh (x0 x ...) (== q (list x0 x ...)) g0 g ...))]))

(define-syntax run*
  (syntax-rules ()
    [(_ (q) g0 g ...)
     (map reify-1st (take-all ((fresh (q) g0 g ...) empty-state)))]
    [(_ (x0 x ...) g0 g ...)
     (run* (q) (fresh (x0 x ...) (== q (list x0 x ...)) g0 g ...))]))
