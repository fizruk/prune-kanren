#lang racket/base

;; prune-kanren: miniKanren with built-in pruning for PBE program synthesis.
;; For now, just re-exports the bare microKanren core; pruning to follow.

(require "microkanren.rkt"
         "prune.rkt")
(provide (all-from-out "microkanren.rkt")
         (all-from-out "prune.rkt"))
