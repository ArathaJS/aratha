; Datatypes

; Val is the datatype for an ECMAScript value. We do not currently have
; support for objects.

(declare-datatypes () (
    (Val
        (undefined)
        (null)
        (Boolean (bool Bool))
        (Str (str String))
        (Num (num Real))
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
    (ite (is-Num x) (int.to.str (to_int (num x)))
    "FOOBARBAZ"))))))

(define-fun js.ToNumber ((x Val)) Real
    (ite (is-Num x) (num x)
    (ite (is-undefined x) 0
    (ite (is-null x) 0
    (ite (is-Boolean x) (ite (bool x) 1 0)
    (ite (is-Str x) (str.to.int (str x))
    42))))))


; ECMAScript expressions

; Binary operators

; Relational operators
(define-fun js.=== ((x Val) (y Val)) Bool (= x y))

; NOTE: "ab" < "ac" returns false by this definition, even though "c" < "a".
; This is because we can't implement the character-level < operation, since Z3
; doesn't (yet) let us access individual characters within strings/sequences.
(define-fun js.< ((x Val) (y Val)) Bool
    (ite (and (is-Str x) (is-Str y))
        (let ((sx (str x)) (sy (str y)))
            (and (not (str.prefixof sy sx)) (str.prefixof sx sy)))
        (< (js.ToNumber x) (js.ToNumber y))))

(define-fun js.> ((x Val) (y Val)) Bool (js.< y x))
(define-fun js.<= ((x Val) (y Val)) Bool (not (js.< y x)))
(define-fun js.>= ((x Val) (y Val)) Bool (not (js.< x y)))

; Arithmetic operators
(define-fun js.+ ((x Val) (y Val)) Val
    (ite (or (is-Str x) (is-Str y))
        (Str (str.++ (js.ToString x) (js.ToString y)))
        (Num (+ (js.ToNumber x) (js.ToNumber y)))))

(define-fun js.- ((x Val) (y Val)) Val
    (Num (- (js.ToNumber x) (js.ToNumber y))))

(define-fun js.* ((x Val) (y Val)) Val
    (Num (* (js.ToNumber x) (js.ToNumber y))))

(define-fun js./ ((x Val) (y Val)) Val
    (Num (/ (js.ToNumber x) (js.ToNumber y))))

(define-fun js.% ((x Val) (y Val)) Val
    (Num (mod (js.ToNumber x) (js.ToNumber y))))

(define-fun js.! ((x Bool)) Bool (not x))
