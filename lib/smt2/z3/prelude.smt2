(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :timeout 30000)

; Datatypes

; Val is the datatype for an ECMAScript value.

(declare-datatypes () (
    (Val
        (undefined)
        (null)
        (Boolean (bool Bool))
        (Str (str String))
        (Num (num Int))
        (Obj (id Int))
    )
))

(declare-datatypes () (
    (MaybeVal
        (Nothing)
        (Just (just Val)))))
