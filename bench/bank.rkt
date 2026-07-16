#lang racket/base

;; Bottom-up observational-equivalence bank for PBE synthesis.
;;
;; build-bank/depth grows a set of programs layer by layer, keeping one
;; representative per observable behavior. Composes in host code; the
;; produced bank is then enumerated relationally by `membero`.
;;
;; This is the standard PBE bank construction. It preserves completeness
;; under conj/bind (unlike a shared dedup table) because each entry in
;; the bank is a concrete syntactic rep that can be replayed any number
;; of times for any caller.

(require "../microkanren.rkt")

(provide build-bank/depth membero)

;; build-bank/depth :
;;   (listof prog -> listof prog)   ; grammar-step: compose bank entries
;;   (listof prog)                  ; terminals: leaf programs
;;   (prog -> any)                  ; behavior: observable key
;;   natural                        ; d: number of composition layers
;;   -> (listof prog)
(define (build-bank/depth grammar-step terminals behavior d)
  (define seen (make-hash))
  (define bank '())
  (define (try p)
    (define b (behavior p))
    (unless (hash-has-key? seen b)
      (hash-set! seen b #t)
      (set! bank (cons p bank))))
  (for ([t (in-list terminals)]) (try t))
  (for ([_ (in-range d)])
    (define snapshot bank)  ; freeze the bank for this layer's compositions
    (for ([p (in-list (grammar-step snapshot))]) (try p)))
  (reverse bank))

;; membero : term (listof term) -> goal
;;
;; A goal that succeeds with v unified to each element of ls in turn.
;; Lazy: produces one state per pull, so `run 1` stops at the first
;; match without materializing the whole list of states.
(define (membero v ls)
  (lambda (s/c)
    (let loop ([ls ls])
      (cond
        [(null? ls) '()]
        [else
         (let ([result ((== v (car ls)) s/c)])
           (cond
             [(null? result) (loop (cdr ls))]
             [else (cons (car result) (lambda () (loop (cdr ls))))]))]))))
