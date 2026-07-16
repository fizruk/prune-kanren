#lang racket/base

;; defrel/memo: define a pure relation whose canonical answer stream is
;; computed once per `run` and replayed against each caller's arguments.
;;
;; The body of a memoized relation is run with canonical input vars
;; (var 0), (var 1), ..., (var N-1) (N = arity), starting counter N.
;; The resulting stream of states (lazy) is stored in the per-run cache.
;; Each subsequent call replays this canonical stream against the
;; caller's args:
;;   - canonical input vars are renamed to the caller's actual args;
;;   - canonical internal fresh vars (idx >= N) are shifted by the
;;     caller's counter to allocate fresh vars in the caller's namespace;
;;   - the renamed bindings are unified into the caller's substitution.
;;
;; Recursive calls inside the body Zzz-suspend, so by the time they fire
;; the cache entry is in place. The lazy thunks of the canonical stream
;; are memoized (`memo-thunk`) so forcing happens at most once per cell
;; across all replays.

(require "microkanren.rkt"
         "wrappers.rkt"
         "prune.rkt")

(provide defrel/memo defrel/bank defrel/bank-w with-memo-session)

(define-syntax-rule (with-memo-session body ...)
  (parameterize ([current-memo (make-hash)]) body ...))

;; --- thunk + stream memoization ---

(define (memo-thunk f)
  (let ([result #f] [done? #f])
    (lambda ()
      (unless done?
        (set! result (f))
        (set! done? #t))
      result)))

(define (memo-stream s)
  (cond
    [(null? s) '()]
    ;; Weighted: preserve the lazy's weight ceiling, but memoize the
    ;; forcing of its thunk. Each lazy gets its own memo-thunk; multiple
    ;; replays sharing the same canonical bank all hit the cache.
    [(lazy? s) (lazy (lazy-weight s)
                     (memo-thunk (lambda () (memo-stream ((lazy-thunk s))))))]
    [(procedure? s) (memo-thunk (lambda () (memo-stream (s))))]
    [else (cons (car s) (memo-stream (cdr s)))]))


;; --- replay ---

(define (replay-state canonical-state caller-state args-vec num-args)
  (define canonical-subst (car canonical-state))
  (define canonical-counter (cdr canonical-state))
  (define caller-subst (car caller-state))
  (define caller-counter (cdr caller-state))
  (define shift-internal (- caller-counter num-args))
  (define new-counter (+ caller-counter (- canonical-counter num-args)))
  (define (rename t)
    (cond
      [(var? t)
       (let ([idx (vector-ref t 0)])
         (cond
           [(< idx num-args) (vector-ref args-vec idx)]
           [else (var (+ idx shift-internal))]))]
      [(pair? t) (cons (rename (car t)) (rename (cdr t)))]
      [else t]))
  (let loop ([i 0] [s caller-subst])
    (cond
      [(= i num-args) (cons s new-counter)]
      [else
       (let* ([canonical-value (walk* (var i) canonical-subst)]
              [renamed (rename canonical-value)]
              [caller-arg (vector-ref args-vec i)]
              [s* (unify caller-arg renamed s)])
         (if s* (loop (+ i 1) s*) #f))])))

(define (replay-stream canonical caller-state args-vec num-args)
  (cond
    [(null? canonical) '()]
    [(procedure? canonical)
     ;; Collapse a chain of immature canonical thunks into a single
     ;; replay-thunk force -- when the consumer asks for the next state,
     ;; we keep forcing until we get a concrete cons (or null), instead
     ;; of producing a new replay-thunk for each layer of canonical
     ;; laziness. This is what `pull` does on the consumer side; doing
     ;; it here cuts the thunk-force count from ~330k to ~3k for the
     ;; PBE bench and brings defrel/bank to within 1.5x of the
     ;; depth-bounded baseline.
     (lambda ()
       (let loop ([c (canonical)])
         (cond
           [(null? c) '()]
           [(procedure? c) (loop (c))]
           [else
            (let ([new (replay-state (car c) caller-state args-vec num-args)])
              (cond
                [new (cons new (replay-stream (cdr c) caller-state args-vec num-args))]
                [else (replay-stream (cdr c) caller-state args-vec num-args)]))])))]
    [else
     (let ([new (replay-state (car canonical) caller-state args-vec num-args)])
       (cond
         [new
          (cons new
                (replay-stream (cdr canonical) caller-state args-vec num-args))]
         [else
          (replay-stream (cdr canonical) caller-state args-vec num-args)]))]))

;; --- init + memo-call ---

(define (init-cell cache rel-tag body-fn num-args)
  (define canonical-vars (for/list ([i (in-range num-args)]) (var i)))
  (define canonical-state (cons '() num-args))
  (define b (box #f))
  (hash-set! cache rel-tag b)
  (define s ((apply body-fn canonical-vars) canonical-state))
  (set-box! b (memo-stream s))
  b)

(define (make-memo-rel num-args body-fn)
  (define rel-tag (box #f))
  (lambda actual-args
    (let ([args-vec (list->vector actual-args)])
      (lambda (s/c)
        (let ([cache (current-memo)])
          (cond
            [cache
             (let ([b (or (hash-ref cache rel-tag #f)
                          (init-cell cache rel-tag body-fn num-args))])
               (replay-stream (unbox b) s/c args-vec num-args))]
            [else
             ((apply body-fn actual-args) s/c)]))))))

(define-syntax defrel/memo
  (syntax-rules ()
    [(_ (name x ...) body ...)
     (define name
       (make-memo-rel (length '(x ...))
                      (lambda (x ...) (conj+ body ...))))]))

;; defrel/bank: like defrel/memo but additionally prunes the canonical
;; stream by the supplied key. Prune runs once at canonical-stream
;; construction time; replays already see only one representative per
;; key. Use shape:
;;
;;   (defrel/bank (rel x ...) #:prune key-expr body ...)
;;
;; key-expr is evaluated in the scope of the relation parameters, so it
;; can reference them (e.g. (ground-key x (lambda (t) ...))). The
;; canonical run binds the parameters to (var 0), (var 1), ....

(define (init-bank-cell cache rel-tag body-fn key-fn num-args)
  (define canonical-vars (for/list ([i (in-range num-args)]) (var i)))
  (define canonical-state (cons '() num-args))
  (define b (box #f))
  (hash-set! cache rel-tag b)
  (define key (apply key-fn canonical-vars))
  (define body-goal (apply body-fn canonical-vars))
  (define s ((prune key body-goal) canonical-state))
  (set-box! b (memo-stream s))
  b)

(define (make-bank-rel num-args body-fn key-fn)
  (define rel-tag (box #f))
  (lambda actual-args
    (let ([args-vec (list->vector actual-args)])
      (lambda (s/c)
        (let ([cache (current-memo)])
          (cond
            [cache
             (let ([b (or (hash-ref cache rel-tag #f)
                          (init-bank-cell cache rel-tag body-fn key-fn num-args))])
               (replay-stream (unbox b) s/c args-vec num-args))]
            [else
             ;; No memo session: fall back to pruning per-call.
             (let ([k (apply key-fn actual-args)]
                   [g (apply body-fn actual-args)])
               ((prune k g) s/c))]))))))

(define-syntax defrel/bank
  (syntax-rules ()
    [(_ (name x ...) #:prune key-expr body ...)
     (define name
       (make-bank-rel (length '(x ...))
                      (lambda (x ...) (conj+ body ...))
                      (lambda (x ...) key-expr)))]))

;; --- defrel/bank-w : weighted bank with depth decay --------------------
;;
;; Same as defrel/bank but uses weighted streams and applies a decay
;; factor to each call. Recursive uses of the relation get weight
;; scaled by `decay` (default 0.5). With sorted-merge mplus-w, this
;; produces depth-ordered enumeration: shallow representatives are
;; emitted before deeper ones.
;;
;;   (defrel/bank-w (rel x ...) #:prune key-expr #:decay d body ...)
;;
;; The body should use the *-w combinators (conde-w, fresh-w, conj-w+)
;; so its internal scheduling participates in the weighted ordering.
;; Plain == is auto-lifted to weight 1.
;;
;; Replay-stream-w is the weighted analogue of replay-stream: each
;; canonical cell carries a weight that gets passed through to the
;; caller. The outer `(scale-w decay ...)` wrapper adds one factor of
;; decay per invocation, so a depth-K canonical cell delivered to the
;; caller has weight roughly decay^(2K+1).

(define (replay-stream-w canonical caller-state args-vec num-args)
  (cond
    [(null? canonical) '()]
    [(lazy? canonical)
     ;; Preserve the canonical lazy's weight ceiling -- replay doesn't
     ;; change weights, only renames vars. Crucially, we do NOT force
     ;; the canonical thunk here; the lazy is returned as-is, and the
     ;; consumer forces it only when its weight indicates it might win.
     (lazy (lazy-weight canonical)
           (lambda ()
             (replay-stream-w ((lazy-thunk canonical))
                              caller-state args-vec num-args)))]
    [else
     (let* ([cell (car canonical)] [w (car cell)] [cs (cdr cell)])
       (let ([new (replay-state cs caller-state args-vec num-args)])
         (cond
           [new (cons (cons w new)
                      (replay-stream-w (cdr canonical) caller-state args-vec num-args))]
           [else (replay-stream-w (cdr canonical) caller-state args-vec num-args)])))]))

(define (init-bank-cell-w cache rel-tag body-fn key-fn num-args)
  (define canonical-vars (for/list ([i (in-range num-args)]) (var i)))
  (define canonical-state (cons '() num-args))
  (define b (box #f))
  (hash-set! cache rel-tag b)
  (define key (apply key-fn canonical-vars))
  (define body-goal (apply body-fn canonical-vars))
  (define s ((prune-w key body-goal) canonical-state))
  (set-box! b (memo-stream s))
  b)

(define (make-bank-rel-w num-args body-fn key-fn decay)
  (define rel-tag (box #f))
  (lambda actual-args
    (let ([args-vec (list->vector actual-args)])
      (lambda (s/c)
        (let ([cache (current-memo)])
          (cond
            [cache
             (let ([b (or (hash-ref cache rel-tag #f)
                          (init-bank-cell-w cache rel-tag body-fn key-fn num-args))])
               (scale-w decay
                 (replay-stream-w (unbox b) s/c args-vec num-args)))]
            [else
             (scale-w decay
               ((prune-w (apply key-fn actual-args) (apply body-fn actual-args)) s/c))]))))))

(define-syntax defrel/bank-w
  (syntax-rules ()
    [(_ (name x ...) #:prune key-expr #:decay decay body ...)
     (define name
       (make-bank-rel-w (length '(x ...))
                        (lambda (x ...) (conj-w+ body ...))
                        (lambda (x ...) key-expr)
                        decay))]
    [(_ (name x ...) #:prune key-expr body ...)
     ;; default decay
     (defrel/bank-w (name x ...) #:prune key-expr #:decay 0.5 body ...)]))
