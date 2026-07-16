#lang racket/base

;; Sanity checks for defrel/memo.

(require "../main.rkt")

;; --- non-recursive ---

(defrel/memo (color c)
  (conde [(== c 'red)] [(== c 'green)] [(== c 'blue)]))

(printf "non-recursive: ~v~n" (run* (c) (color c)))

;; --- recursive: tree of pluses ---

(defrel/memo (expr e)
  (conde
    [(== e 'x)]
    [(== e 0)]
    [(== e 1)]
    [(fresh (l r)
       (== e `(plus ,l ,r))
       (expr l)
       (expr r))]))

(printf "first 10 expr answers: ~v~n" (run 10 (e) (expr e)))

;; --- structured arg dispatches via unification ---

(printf "expr of (plus l r): ~v~n"
        (run 3 (q)
          (fresh (l r)
            (== q (list l r))
            (expr `(plus ,l ,r)))))

;; --- two callers in conj should both see the bank ---
;; (times x x) needs both children to be 'x -- exactly the case that
;; broke under shared-table prune.

(defrel/memo (expr/m e)
  (conde
    [(== e 'x)]
    [(== e 0)]
    [(== e 1)]
    [(fresh (l r)
       (== e `(plus  ,l ,r))
       (expr/m l) (expr/m r))]
    [(fresh (l r)
       (== e `(times ,l ,r))
       (expr/m l) (expr/m r))]))

(printf "first 5 expr/m: ~v~n" (run 5 (e) (expr/m e)))
(printf "search for (times x x) shape: ~v~n"
        (run 1 (e)
          (fresh (l r)
            (== e `(times ,l ,r))
            (expr/m l) (expr/m r)
            (== l 'x) (== r 'x))))
