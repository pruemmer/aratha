; Relational operators
;(define-sort Properties () (Array String MaybeVal))
;(declare-fun GetProperties (Int) Properties)
;(define-fun EmptyObject () Properties ((as const Properties) Nothing)) 
;;ostrich does not support const appearing above

(define-fun js.=== ((x String) (y String)) Bool (= x y))

(define-fun js.!== ((x String) (y String)) Bool (not (js.=== x y)))