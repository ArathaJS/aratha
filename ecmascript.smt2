; Datatypes

; Val is the datatype for an ECMAScript value. We do not currently have
; support for objects.

(declare-datatypes () (
    (Val
        (undefined)
        (null)
        (Boolean (bool Bool))
        (Str (str String))
        (Num (num Int))
    )
))

; ECMAScript internal functions
;
; These will have the same name as the functions in the specification with
; "js." prepended. The generally return values of an SMT-LIB sort, and may
; need to be wrapped with Val.

(define-fun js.ToString ((x Val)) String
    (ite (is-Str x) (str x)
    (ite (is-undefined x) "undefined"
    (ite (is-null x) "null"
    (ite (is-Boolean x) (ite (bool x) "true" "false")
    ;(ite (is-Num x) (int.to.str (num x))
    "FOOBARBAZ")))))

(define-fun js.ToNumber ((x Val)) Int
    (ite (is-Num x) (num x)
    (ite (is-undefined x) 0
    (ite (is-null x) 0
    (ite (is-Boolean x) (ite (bool x) 1 0)
    (ite (is-Str x) (str.to.int (str x))
    42))))))

; ECMAScript expressions

; Binary operators

(define-fun js.=== ((x Val) (y Val)) Bool (= x y))

(define-fun js.+ ((x Val) (y Val)) Val
    (ite (or (is-Str x) (is-Str y))
        (Str (str.++ (js.ToString x) (js.ToString y)))
        (Num (+ (js.ToNumber x) (js.ToNumber y)))))

(define-fun js.! ((x Bool)) Bool (not x))
