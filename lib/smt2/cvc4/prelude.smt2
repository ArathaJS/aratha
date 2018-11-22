(set-option :produce-models true)

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

(define-fun Int32ToInt ((x (_ BitVec 32))) Int
    (let ((nx (bv2nat x)))
        (ite (>= nx 2147483648) (- nx 4294967296) nx)))
(define-fun Int32ToUInt ((x (_ BitVec 32))) Int (bv2nat x))
