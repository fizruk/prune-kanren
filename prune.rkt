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

(provide prune skip-prune)

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
