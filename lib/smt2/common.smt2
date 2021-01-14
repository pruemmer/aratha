(define-sort Properties () (Array String MaybeVal))
(declare-fun GetProperties (Int) Properties)
(define-fun EmptyObject () Properties ((as const Properties) Nothing))

(define-fun js.=== ((x Val) (y Val)) Bool (= x y))
(define-fun js.!== ((x Val) (y Val)) Bool (not (js.=== x y)))

(define-fun js.ToString ((x Val)) String
    (ite (is-Str x) (str x)
    (ite (is-undefined x) "undefined"
    (ite (is-null x) "null"
    (ite (is-Boolean x) (ite (bool x) "true" "false")
    "[object Object]")))))