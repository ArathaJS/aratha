(declare-datatypes () (
    (Val
        (Str (str String))
        (Num (num Int))
    )
))

(define-fun js.ToString ((x Val)) String (ite (is-Num x) (int.to.str (num x)) ""))
(define-fun js.< ((x Val) (y Val)) Bool (not (= (js.ToString y) (js.ToString x))))

(declare-const var4 Val)
(declare-const var0 Val)
(declare-const var1 Val)
(assert (js.< var0 var4))
(assert (not (js.< var0 var1)))
(check-sat)
