#lang racket/base

;; Synthesis of `append` via defrel/bank with behavioral pruning of
;; list-typed sub-expressions.
;;
;; Purely type-directed synthesis of append times out without
;; disequality because the search space at the required depth is
;; wide. The idea here (user's suggestion): when generating
;; candidates of type [a], two candidates that compute the same list
;; value on a fixed set of sample inputs are observationally
;; equivalent for the purposes of finding a correct append. Prune by
;; that equivalence using defrel/bank.
;;
;; Pieces:
;;   - sample-list-evals : sample (xs, ys) environments used as the
;;     "tracer" for the prune key.
;;   - host-eval : a Racket-side interpreter for the synthesized
;;     expression syntax. It evaluates `append` using Racket's
;;     `append`, so the I/O oracle IS the prune-key evaluator.
;;   - list-exprᵒ : defrel/bank-defined relation that enumerates
;;     list-typed expressions in the append context, pruning by their
;;     list-valued behavior on the sample environments.
;;   - matches-appendᵒ : final filter -- the *full* expression must
;;     reproduce append's behavior on all I/O examples (including
;;     edge cases where xs is empty).
;;
;; Sample selection matters. The xs samples must be long enough that
;; (rest xs) doesn't immediately error: with `(xs . (1))`, then
;; `(rest (1)) = ()` and `(rest ())` errors, which forces many
;; otherwise-distinct expressions into the single `'eval-error`
;; equivalence class. That class dominates the bank and the bank
;; struggles to find non-error-producing combinations. Using xs
;; samples of length >= 2 keeps the behavior space well-spread.
;;
;; Result: the bank pulls representatives by their list-valued
;; behavior; among expressions with the target behavior (append's
;; output), the simplest representative `((append xs) ys)` is
;; emitted first. The full synthesized program reduces to:
;;
;;   (if (empty? xs) then ys else ((append xs) ys))
;;
;; which is a correct (and minimal) definition of append given
;; append is in the context as a recursive reference. The classic
;; recursive form `(cons (first xs) (append (rest xs) ys))` is
;; behavior-equivalent and gets pruned in favor of the shorter
;; representative.

(require "../main.rkt"
         (only-in racket/base [append rkt:append]))

;; --- samples & oracle ----------------------------------------------------

;; The prune key uses these (xs, ys) environments. To distinguish
;; expressions well, xs and ys should have different lengths and
;; element sets across samples. We only use *non-empty* xs samples in
;; the prune key, because the hint specializes us to the else branch
;; of `(if (empty? xs) ...)`; behavior on empty xs would not
;; distinguish list-typed sub-expressions that only matter when xs is
;; non-empty.
(define sample-list-evals
  '(((xs . (1 2))     (ys . (3)))
    ((xs . (a b c))   (ys . (d e)))
    ((xs . (10 20 30)) (ys . (40)))))

;; Full I/O spec for append (including empty-xs cases). Used by the
;; final `matches-appendᵒ` filter that checks the WHOLE candidate.
(define append-io-spec
  `(((()       ())        . ())
    ((()       (5 6))     . (5 6))
    (((1)      (2))       . (1 2))
    (((1 2)   (3))        . (1 2 3))
    (((a b c) (d e))      . (a b c d e))
    (((7 8)   ())         . (7 8))))

;; Racket-side interpreter for the expression syntax used in the
;; append context. The functions `cons`, `first`, `rest`, `append`,
;; `empty?` are interpreted by their host meanings -- so the prune
;; key's notion of "same behavior" matches the I/O oracle by
;; construction.
(define (host-eval expr env)
  (cond
    [(symbol? expr)
     (cond
       [(assq expr env) => cdr]
       [(eq? expr 'cons)   (lambda (x) (lambda (lst) (cons x lst)))]
       [(eq? expr 'first)  car]
       [(eq? expr 'rest)   cdr]
       [(eq? expr 'append) (lambda (xs) (lambda (ys) (rkt:append xs ys)))]
       [(eq? expr 'empty?) null?]
       [else (error 'host-eval "unknown symbol: ~v" expr)])]
    [(and (pair? expr) (= (length expr) 6) (eq? (car expr) 'if))
     ;; (if e1 then e2 else e3) -- 6 elements: 'if e1 'then e2 'else e3
     (if (host-eval (list-ref expr 1) env)
         (host-eval (list-ref expr 3) env)
         (host-eval (list-ref expr 5) env))]
    [(and (pair? expr) (= (length expr) 2))
     ((host-eval (car expr) env) (host-eval (cadr expr) env))]
    [else (error 'host-eval "unhandled expression: ~v" expr)]))

;; --- the prune-aware list-expression bank --------------------------------

;; Synthesized `[a]`-typed expressions: variables `xs`/`ys`, cons of
;; an element onto a list, rest of a list, or append of two lists.
;; Pruned by behavior on `sample-list-evals`.
(defrel/bank (list-exprᵒ e)
  #:prune (ground-key e
            (lambda (t)
              (with-handlers ([exn:fail? (lambda (_) 'eval-error)])
                (map (lambda (env) (host-eval t env)) sample-list-evals))))
  (conde
    [(== e 'xs)]
    [(== e 'ys)]
    [(fresh (head tail)
       (== e `((cons ,head) ,tail))
       (head-exprᵒ head)
       (list-exprᵒ tail))]
    [(fresh (lst)
       (== e `(rest ,lst))
       (list-exprᵒ lst))]
    [(fresh (xs-arg ys-arg)
       (== e `((append ,xs-arg) ,ys-arg))
       (list-exprᵒ xs-arg)
       (list-exprᵒ ys-arg))]))

;; `a`-typed expressions: the only way to get an element of type `a`
;; from this context is `(first <list>)`.
(define (head-exprᵒ e)
  (fresh (lst)
    (== e `(first ,lst))
    (list-exprᵒ lst)))

;; Final filter: the whole candidate (the `if`-expression) must
;; reproduce append's behavior on every I/O example. Catches cases
;; that pass the bank's per-sample prune but differ on empty-xs.
(define (matches-appendᵒ e)
  (when-ground e
    (lambda (t)
      (with-handlers ([exn:fail? (lambda (_) #f)])
        (andmap (lambda (io)
                  (define env `((xs . ,(car (car io)))
                                (ys . ,(cadr (car io)))))
                  (equal? (host-eval t env) (cdr io)))
                append-io-spec)))))

;; --- synthesis -----------------------------------------------------------

;; Synthesize the body of append given the homework's hint:
;;   (if (empty? xs) then ys else <e2>)
;; where e2 is a list expression.
(define (synth-append)
  (run 1 (e)
    (fresh (e2)
      (== e `(if (empty? xs) then ys else ,e2))
      (list-exprᵒ e2)
      (matches-appendᵒ e))))

;; --- demonstration -------------------------------------------------------

(module+ main
  (printf "Sample envs:    ~v~n" sample-list-evals)
  (printf "I/O spec:       ~v~n~n" append-io-spec)
  (flush-output)

  (define t0 (current-inexact-milliseconds))
  (define result (synth-append))
  (define elapsed (- (current-inexact-milliseconds) t0))

  (printf "~nSynthesis result (~a ms):~n" (real->decimal-string elapsed 1))
  (for ([r (in-list result)])
    (printf "  ~v~n" r))

  ;; Sanity check: verify the synthesized expression matches all I/O.
  (when (pair? result)
    (define answer (car result))
    (define passes
      (andmap (lambda (io)
                (define env `((xs . ,(car (car io)))
                              (ys . ,(cadr (car io)))))
                (equal? (host-eval answer env) (cdr io)))
              append-io-spec))
    (printf "~nMatches all I/O examples: ~a~n" passes)))
