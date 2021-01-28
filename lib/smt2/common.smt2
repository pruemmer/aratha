(define-sort Properties () (Array String MaybeVal))
(declare-fun GetProperties (Int) Properties)
(define-fun EmptyObject () Properties ((as const Properties) Nothing))
(define-fun StringToObject ((s String)) Properties (store EmptyObject "length" (Just (Num (str.len s)))))
(define-fun NumberToString ((x Int)) String (ite (>= x 0) (int.to.str x) (str.++ "-" (int.to.str (- x)))))
(define-fun js.ToString ((x Val)) String
    (ite (is-Str x) (str x)
    (ite (is-undefined x) "undefined"
    (ite (is-null x) "null"
    (ite (is-Boolean x) (ite (bool x) "true" "false")
    (ite (is-Num x) (NumberToString (num x))
    "[object Object]"))))))
(define-fun js.ToObject ((o Val)) Properties
    (ite (is-Obj o) (GetProperties (id o))
    (ite (is-Str o) (StringToObject (str o))
    EmptyObject)))
(define-fun GetField ((o Properties) (k Val)) Val
    (let ((v (select o (js.ToString k))))
        (ite (is-Just v) (just v) undefined)))
(define-fun StringToNumber ((x String)) Int
    (ite (= x "") 0
    (ite (str.prefixof "-" x) (- (str.to.int (str.substr x 1 (- (str.len x) 1))))
    (str.to.int x))))
(define-fun js.ToNumber ((x Val)) Int
    (ite (is-Num x) (num x)
    (ite (is-undefined x) 0
    (ite (is-null x) 0
    (ite (is-Boolean x) (ite (bool x) 1 0)
    (ite (is-Str x) (StringToNumber (str x))
    0)))))) 
(define-fun StrLessThan ((x String) (y String)) Bool
    (and (not (str.prefixof y x)) (str.prefixof x y)))
(define-fun ToPrimitive ((x Val)) Val (ite (is-Obj x) (Str "[object Object]") x))
(define-fun IsNumber ((x Val)) Bool (and
    (not (is-undefined x))
    (not (is-Obj x))
    (=> (is-Str x) (let ((sx (str x))) (or (distinct (str.to.int sx) (- 1)) (= sx "") (= sx "-1"))))))
(define-fun AbsRelComp ((x Val) (y Val)) Bool
    (let ((px (ToPrimitive x)) (py (ToPrimitive y)))
    (and (=> (not (and (is-Str px) (is-Str py))) (< (js.ToNumber px) (js.ToNumber py)))
    (=> (and (is-Str px) (is-Str py)) (StrLessThan (str px) (str py))))))
(define-fun IsDefinedComp ((x Val) (y Val)) Bool (or (and (IsNumber x) (IsNumber y)) (and (or (is-Str x) (is-Obj x)) (or (is-Str y) (is-Obj y)))))
(define-fun js.< ((x Val) (y Val)) Bool (and (IsDefinedComp x y) (AbsRelComp x y)))
(define-fun js.> ((x Val) (y Val)) Bool (and (IsDefinedComp y x) (AbsRelComp y x)))
(define-fun js.<= ((x Val) (y Val)) Bool (and (IsDefinedComp y x) (not (AbsRelComp y x))))
(define-fun js.>= ((x Val) (y Val)) Bool (and (IsDefinedComp x y) (not (AbsRelComp x y))))
(define-fun SameType ((x Val) (y Val)) Bool (or
    (and (is-undefined x) (is-undefined y))
    (and (is-null x) (is-null y))
    (and (is-Boolean x) (is-Boolean y))
    (and (is-Str x) (is-Str y))
    (and (is-Num x) (is-Num y))))
(define-fun js.=== ((x Val) (y Val)) Bool (= x y))
(define-fun js.!== ((x Val) (y Val)) Bool (not (js.=== x y)))
(define-fun js.== ((x Val) (y Val)) Bool
    (ite (SameType x y) (js.=== x y)
    (ite (and (is-null x) (is-undefined y)) true
    (ite (and (is-null y) (is-undefined x)) true
    (ite (and (is-Num x) (is-Str y)) (= (num x) (js.ToNumber y))
    (ite (and (is-Num y) (is-Str x)) (= (num y) (js.ToNumber x))
    (ite (is-Boolean x) (let ((nx (js.ToNumber x)))
        (ite (is-Num y) (= nx (num y))
        (ite (is-Str y) (= nx (js.ToNumber y))
        false)))
    (ite (is-Boolean y) (let ((ny (js.ToNumber y)))
        (ite (is-Num x) (= (num x) ny)
        (ite (is-Str x) (= ny (js.ToNumber x))
        false)))
    false))))))))
(define-fun js.!= ((x Val) (y Val)) Bool (not (js.== x y)))
(define-fun js.ToBoolean ((x Val)) Bool
    (ite (is-Num x) (distinct (num x) 0)
    (ite (is-undefined x) false
    (ite (is-null x) false
    (ite (is-Boolean x) (bool x)
    (ite (is-Str x) (distinct (str x) "")
    true))))))

(define-fun min ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun max ((x Int) (y Int)) Int (ite (> x y) x y))
(define-fun clamp ((x Int) (lower Int) (upper Int)) Int (min (max x lower) upper))
(define-fun js.ToInteger ((x Val)) Int (js.ToNumber x))

(define-fun substring ((x String) (start Int) (end Int)) String (str.substr x start (- end start)))
(define-fun js.substring ((x String) (start Int) (end Val)) String
    (let ((len (str.len x)))
        (let (
            (fs (clamp start 0 len))
            (fe (clamp (ite (is-undefined end) len (js.ToInteger end)) 0 len)))
                (substring x (min fs fe) (max fs fe)))))

(define-fun js.substr ((x String) (start Int) (len Val)) String
    (ite (>= start (str.len x))
        ""
        (let ((sp (ite (>= start 0) start (max 0 (+ (str.len x) start)))))
            (let ((remlen (- (str.len x) sp)))
                (str.substr x sp (ite (is-undefined len) remlen (clamp (js.ToInteger len) 0 remlen)))))))

(define-fun js.slice ((x String) (start Int) (end Val)) String
    (let ((len (str.len x)))
        (let ((ie (ite (is-undefined end) len (js.ToInteger end))))
            (let (
                (from (ite (< start 0) (max 0 (+ len start)) (min start len)))
                (to (ite (< ie 0) (max 0 (+ len ie)) (min ie len))))
                    (str.substr x from (max 0 (- to from)))))))

(define-fun Split1 ((x String) (delim String)) Properties
    (let ((n (str.indexof x delim 0)))
        (ite (= n (- 1))
            (store EmptyObject "0" (Just (Str x)))
            (store EmptyObject "0" (Just (Str (str.substr x 0 n)))))))

(define-fun Split2 ((x String) (delim String)) Properties
    (let ((n (str.indexof x delim 0)))
        (ite (= n (- 1))
            (store EmptyObject "0" (Just (Str x)))
            (store
                (store EmptyObject "0" (Just (Str (str.substr x 0 n))))
                "1"
                (Just (Str (str.substr
                    x
                    (+ n 1)
                    (- (str.len x) (+ n 1)))))))))

(define-fun js.split ((x String) (delim String) (maxSplits Int)) Properties
    (ite (= 0 maxSplits)
        EmptyObject
        (ite (= 1 maxSplits) (Split1 x delim) (Split2 x delim))))