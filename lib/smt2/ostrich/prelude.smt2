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


