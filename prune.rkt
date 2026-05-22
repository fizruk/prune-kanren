#lang racket/base

;; Pruning combinator.
;;
;; (prune key g) wraps a goal g and filters its answer stream so that at
;; most one state is emitted per distinct value of (key s/c). The key
;; function is supplied per call, so the equivalence used to prune is
;; chosen locally — e.g. "behavior on the input examples" for PBE
;; synthesis, or "shape modulo alpha-renaming" elsewhere.
;;
;; The dedup table is local to one prune call and shared across the
;; stream's lazy thunks (the closure captures it), so dedup state
;; survives the inverse-eta delay used by mplus/bind.
;;
;; This sketch uses equal?-keyed hashing; an efficient version would
;; hash-cons the key values produced by the user's semantic function.

(require "microkanren.rkt"
         "wrappers.rkt")

(provide prune skip-prune
         ground? ground-key when-ground)

;; Sentinel a key function may return to mean "don't dedup yet" —
;; typically because the relevant variables are still fresh.
(define skip-prune 'skip-prune)

;; prune : (state -> any) goal -> goal
(define (prune key g)
  (lambda (s/c)
    (prune-stream key (make-hash) (g s/c))))

(define (prune-stream key seen $)
  (cond
    [(null? $) '()]
    [(procedure? $) (lambda () (prune-stream key seen ($)))]
    [else
     (let* ([s/c (car $)]
            [k (key s/c)])
       (cond
         [(eq? k skip-prune)
          (cons s/c (prune-stream key seen (cdr $)))]
         [(hash-has-key? seen k)
          (prune-stream key seen (cdr $))]
         [else
          (hash-set! seen k #t)
          (cons s/c (prune-stream key seen (cdr $)))]))]))

;; --- key-building helpers ---

;; A term is ground if it contains no logic variables.
(define (ground? t)
  (cond
    [(var? t) #f]
    [(pair? t) (and (ground? (car t)) (ground? (cdr t)))]
    [else #t]))

;; ground-key : variable (term -> any) -> (state -> any)
;;
;; Lifts a host function on terms into a prune key on states: walks `v`
;; in the current substitution and, if the result is ground, applies `f`
;; to it. Returns `skip-prune` when `v` hasn't ground out yet, so those
;; states pass through `prune` unfiltered.
;;
;; Typical use in PBE synthesis:
;;   (prune (ground-key e (lambda (t) (map (eval-on t) inputs)))
;;          (expr e depth))
(define (ground-key v f)
  (lambda (s/c)
    (let ([t (walk* v (car s/c))])
      (if (ground? t)
          (f t)
          skip-prune))))

;; when-ground : variable (term -> boolean) -> goal
;;
;; A goal that succeeds when `v` walks to a ground term satisfying
;; `pred`, and fails otherwise (including when `v` is still non-ground).
;; Useful as the final "accept this candidate" stage of a synthesis run.
(define (when-ground v pred)
  (lambda (s/c)
    (let ([t (walk* v (car s/c))])
      (if (and (ground? t) (pred t))
          (unit s/c)
          '()))))
