#lang info

(define collection "prune-kanren")
(define pkg-desc
  "A miniKanren implementation with a built-in pruning mechanism, suitable for PBE program synthesis.")
(define version "0.0")
(define pkg-authors '(nikolai-kudasov))
(define license 'MIT)

(define deps '("base"))
(define build-deps '("racket-doc"
                     "rackunit-lib"
                     "scribble-lib"))
