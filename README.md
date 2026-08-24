# prune-kanren

A miniKanren implementation with a built-in pruning mechanism, in
particular suitable for programming-by-example (PBE) program synthesis.

The library extends a minimal microKanren core (Hemann & Friedman,
2013) with two combinators:

- `prune` wraps a goal and keeps at most one answer per equivalence
  class. The equivalence is given by a user-supplied key function,
  e.g. "behavior on the input examples" for PBE synthesis.
- `defrel/memo` defines a relation whose answer stream is computed
  once per `run` and replayed for each caller. `defrel/bank`
  additionally prunes the memoized stream, which gives a bottom-up
  enumeration of representatives similar to the banks used in
  non-relational PBE synthesis tools.

A best-first variant `defrel/bank-w` enumerates representatives on
weighted streams, applying a decay factor per recursive call, so
shallow representatives are emitted before deeper ones.

For details, see the paper ["Towards Bottom-Up Enumeration in
miniKanren via Pruning and Memoization"](https://arxiv.org/abs/2607.25373)
(miniKanren 2026), and the
[slides](https://fizruk.github.io/files/miniKanren-2026-prune-kanren-slides.pdf)
from the workshop talk.

## Example

Synthesize an arithmetic expression `e` over one input `x` such that
`e(2) = 4`, `e(3) = 9`, `e(4) = 16`:

```racket
#lang racket/base
(require "main.rkt")

(define inputs '(2 3 4))

(define (interp e x)
  (cond
    [(eq? e 'x) x]
    [(number? e) e]
    [(eq? (car e) 'plus)  (+ (interp (cadr e) x) (interp (caddr e) x))]
    [(eq? (car e) 'times) (* (interp (cadr e) x) (interp (caddr e) x))]))

;; Enumerate expressions bottom-up, keeping one representative per
;; behavior on the inputs. No depth bound is needed.
(defrel/bank (expr e)
  #:prune (ground-key e (lambda (t) (map (lambda (x) (interp t x)) inputs)))
  (conde
    [(== e 'x)] [(== e 0)] [(== e 1)]
    [(fresh (l r)
       (conde [(== e `(plus ,l ,r))] [(== e `(times ,l ,r))])
       (expr l) (expr r))]))

(run 1 (e)
  (expr e)
  (when-ground e
    (lambda (t)
      (andmap (lambda (io) (equal? (interp t (car io)) (cdr io)))
              '((2 . 4) (3 . 9) (4 . 16))))))
;; => '((times x x))
```

## Layout

- `microkanren.rkt` — microKanren core, plus fair (`-i`) and weighted
  (`-w`) stream combinators.
- `wrappers.rkt` — miniKanren-style surface forms (`conde`, `fresh`,
  `run`, `run*`) and their `-i`/`-w` variants.
- `prune.rkt` — the `prune` combinator, the `skip-prune` sentinel, and
  the `ground-key` / `when-ground` helpers.
- `memo.rkt` — `defrel/memo`, `defrel/bank`, `defrel/bank-w`.
- `main.rkt` — re-export hub: `(require "main.rkt")` pulls in
  everything above.
- `examples/` — small self-contained demos, including PBE synthesis of
  arithmetic expressions and of `append`. Note that
  `examples/shared-table-witness.rkt` intentionally demonstrates a
  completeness failure and hangs partway through; see the comments in
  the file.
- `bench/` — benchmark drivers comparing the engines (depth-bounded
  `prune`, `defrel/bank`, `defrel/bank-w`, and a host-language bank).
- `tests/` — sanity checks.

## Running the examples

```sh
racket examples/pbe-example.rkt
racket examples/pbe-example-nodepth.rkt
racket examples/append-synth.rkt
racket tests/memo-test.rkt
```

The benchmark drivers take longer (some targets run with 30–60 s
timeouts):

```sh
racket bench/shallow-bench.rkt
racket bench/deep-bench.rkt
```

## License

MIT, see [LICENSE](LICENSE).
