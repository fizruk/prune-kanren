#lang racket/base

;; Decay-factor experiment for defrel/bank-w.
;;
;; With a uniform decay factor d applied at every recursive call,
;; every canonical cell's weight is d^n, where n counts the recursive
;; calls in the cell's derivation. Since d^n is monotone in n for any
;; d in (0,1), the pairwise comparisons made by mplus-w are the same
;; for every such d, and the sorted-merge enumeration order is
;; invariant under the choice of d. The decay knob therefore only
;; becomes meaningful when different productions carry different
;; weights (e.g. Probe-style learned weights).
;;
;; This script verifies the claim empirically: for several values of
;; d, it (1) enumerates the first K representatives of the weighted
;; arithmetic bank and checks that the prefixes coincide, and
;; (2) times the (1+x)^2 synthesis target under each d.

(require "../main.rkt")

(define inputs '(2 3 4))

(define (interp e x)
  (cond
    [(eq? e 'x) x]
    [(number? e) e]
    [(eq? (car e) 'plus)  (+ (interp (cadr e) x) (interp (caddr e) x))]
    [(eq? (car e) 'times) (* (interp (cadr e) x) (interp (caddr e) x))]))

(define (arith-key e)
  (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs))))

(define (matches e io-pairs)
  (when-ground e
    (lambda (t)
      (andmap (lambda (io) (equal? (interp t (car io)) (cdr io))) io-pairs))))

;; One weighted bank per decay value. The macro duplicates the body
;; so that each relation gets its own canonical cache cell.
(define-syntax-rule (define-arith-bank-w name d)
  (defrel/bank-w (name e)
    #:prune (arith-key e)
    #:decay d
    (conde-w
      [(== e 'x)] [(== e 0)] [(== e 1)]
      [(fresh-w (l r) (conde-w [(== e `(plus ,l ,r))] [(== e `(times ,l ,r))])
         (name l) (name r))])))

(define-arith-bank-w bank-w/090 0.9)
(define-arith-bank-w bank-w/075 0.75)
(define-arith-bank-w bank-w/050 0.5)
(define-arith-bank-w bank-w/025 0.25)
(define-arith-bank-w bank-w/010 0.1)

(define decay-banks
  `((0.9  . ,bank-w/090)
    (0.75 . ,bank-w/075)
    (0.5  . ,bank-w/050)
    (0.25 . ,bank-w/025)
    (0.1  . ,bank-w/010)))

(define prefix-length 50)

(define target-io '((2 . 9) (3 . 16) (4 . 25)))  ; (1+x)^2

(define (time-it thunk)
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (define result (thunk))
  (define elapsed (- (current-inexact-milliseconds) start))
  (values result elapsed))

(module+ main
  (printf "Decay-factor experiment  (inputs: ~v)~n" inputs)
  (printf "Prefix length: ~a~n~n" prefix-length)

  ;; (1) enumeration-order prefixes, compared pairwise
  (define prefixes
    (for/list ([db (in-list decay-banks)])
      (define bank (cdr db))
      (cons (car db) (run-w prefix-length (e) (bank e)))))
  (define (first-diff xs ys)
    (let loop ([xs xs] [ys ys] [i 0])
      (cond [(or (null? xs) (null? ys)) (if (equal? xs ys) #f i)]
            [(equal? (car xs) (car ys)) (loop (cdr xs) (cdr ys) (+ i 1))]
            [else i])))
  (printf "  pairwise comparison of the ~a-representative prefixes:~n" prefix-length)
  (for* ([p (in-list prefixes)]
         [q (in-list prefixes)]
         #:when (< (car p) (car q)))
    (define d (first-diff (cdr p) (cdr q)))
    (printf "    decay=~a vs decay=~a: ~a~n"
            (car p) (car q)
            (if d (format "first difference at position ~a" (+ d 1)) "IDENTICAL")))
  ;; Same set of representatives, only permuted?
  (printf "  prefixes as sets (sorted):~n")
  (define (prefix-set p) (sort (map (lambda (t) (format "~v" t)) (cdr p)) string<?))
  (define ref-set (prefix-set (car prefixes)))
  (for ([p (in-list (cdr prefixes))])
    (printf "    decay=~a: ~a set of representatives as decay=~a~n"
            (car p)
            (if (equal? (prefix-set p) ref-set) "SAME" "DIFFERENT")
            (car (car prefixes))))

  ;; (1b) weight-class structure: for each decay, extract the raw
  ;; weight of each emitted cell and recover its exponent n (the
  ;; number of decay applications) as round(log w / log d). If the
  ;; class order is invariant, the exponent sequences coincide across
  ;; decays even where the within-class term order differs.
  (define exponent-seqs
    (for/list ([db (in-list decay-banks)])
      (define d (car db))
      (define bank (cdr db))
      (define cells
        (with-memo-session
          (take-w prefix-length ((call/fresh (lambda (q) (bank q))) empty-state))))
      (cons d (map (lambda (cell)
                     (inexact->exact (round (/ (log (car cell)) (log d)))))
                   cells))))
  (define ref-exps (cdr (car exponent-seqs)))
  (printf "  weight-exponent sequences (class structure):~n")
  (printf "    decay=~a: ~a~n" (car (car exponent-seqs)) ref-exps)
  (for ([es (in-list (cdr exponent-seqs))])
    (printf "    decay=~a: ~a~n"
            (car es)
            (if (equal? (cdr es) ref-exps) "IDENTICAL" (cdr es))))

  ;; (2) timing on the (1+x)^2 target
  (printf "~nTiming on target (1+x)^2:~n")
  (for ([db (in-list decay-banks)])
    (define bank (cdr db))
    (define-values (result elapsed)
      (time-it (lambda () (run-w 1 (e) (bank e) (matches e target-io)))))
    (printf "  decay=~a: ~a ms  ~v~n"
            (car db) (real->decimal-string elapsed 1) result)))
