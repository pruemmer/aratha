; ECMAScript internal functions
;
; These will have the same name as the functions in the specification with
; "js." prepended. The generally return values of an SMT-LIB sort, and may
; need to be wrapped with Val.

(define-fun NumberToString ((x Int)) String (ite (>= x 0) (int.to.str x) (str.++ "-" (int.to.str (- x)))))

(define-fun js.ToString ((x Val)) String
    (ite (is-Str x) (str x)
    (ite (is-undefined x) "undefined"
    (ite (is-null x) "null"
    (ite (is-Boolean x) (ite (bool x) "true" "false")
    (ite (is-Num x) (NumberToString (num x))
    "[object Object]"))))))

; Relational operators
(define-fun js.=== ((x Val) (y Val)) Bool (= x y))
(define-fun js.!== ((x Val) (y Val)) Bool (not (js.=== x y)))