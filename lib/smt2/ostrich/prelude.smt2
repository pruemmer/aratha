(set-option :produce-models true)
(set-option :inline-size-limit 10000)

; Datatypes

; Val is the datatype for an ECMAScript value.

(declare-datatype Val (
    (undefined)
    (null)
    (Boolean (bool Bool))
    (Str (str String))
    (Num (num Int))
    (Obj (id Int))))

(declare-datatype MaybeVal (
    (Nothing)
    (Just (just Val))))

(define-fun Int32ToInt  ((x (_ BitVec 32))) Int (bv2int x))
(define-fun Int32ToUInt ((x (_ BitVec 32))) Int (bv2nat x))

(define-sort Properties () (Array String MaybeVal))
(declare-fun GetProperties (Int) Properties)

(define-fun EmptyObject () Properties ((as const Properties) Nothing))
