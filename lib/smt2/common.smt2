(define-sort Properties () (Array String MaybeVal))
(declare-fun GetProperties (Int) Properties)
(define-fun EmptyObject () Properties ((as const Properties) Nothing))

(define-fun js.=== ((x Val) (y Val)) Bool (= x y))
(define-fun js.!== ((x Val) (y Val)) Bool (not (js.=== x y)))