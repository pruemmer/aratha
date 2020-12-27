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

; NOTE: "ab" < "ac" returns false by this definition, even though "c" < "a".
; This is because we can't implement the character-level < operation, since Z3
; doesn't (yet) let us access individual characters within strings/sequences.
; TODO: implement more of the string-to-number semantics


(define-fun min ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun max ((x Int) (y Int)) Int (ite (> x y) x y))
(define-fun clamp ((x Int) (lower Int) (upper Int)) Int (min (max x lower) upper))

; Relational operators
(define-fun js.=== ((x Val) (y Val)) Bool (= x y))
(define-fun js.!== ((x Val) (y Val)) Bool (not (js.=== x y)))




(define-fun StrLessThan ((x String) (y String)) Bool
    (and (not (str.prefixof y x)) (str.prefixof x y)))

(define-fun ToPrimitive ((x Val)) Val (ite (is-Obj x) (Str "[object Object]") x))




; Object operation
(define-fun StringToObject ((s String)) Properties (store EmptyObject "length" (Just (Num (str.len s)))))
(define-fun NumberToObject ((x Int)) Properties EmptyObject)
(define-fun BooleanToObject ((p Bool)) Properties EmptyObject)

(define-fun js.ToObject ((o Val)) Properties
    (ite (is-Obj o) (GetProperties (id o))
    (ite (is-Str o) (StringToObject (str o))
    EmptyObject)))

(define-fun GetField ((o Properties) (k Val)) Val
    (let ((v (select o (js.ToString k))))
        (ite (is-Just v) (just v) undefined)))
(define-fun PutField ((o Properties) (k Val) (v Val)) Properties (store o (js.ToString k) (Just v)))
(define-fun DeleteField ((o Properties) (k Val)) Properties (store o (js.ToString k) Nothing))

(define-fun MutableToProps ((base Val) (modified Properties)) Properties
    (ite (is-Obj base) modified (js.ToObject base)))


; string function


