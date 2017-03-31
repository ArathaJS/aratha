(define-fun js.ToInt32 ((x Val)) (_ BitVec 32) ((_ int2bv 32) (js.ToNumber x)))
(define-fun UInt32ToInt ((x Int)) Int (ite (>= x 2147483648) (- x 4294967296) x))

; Bit shift operators
(define-fun js.<< ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (UInt32ToInt (bv2nat (bvshl bx by))))))

(define-fun js.>> ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (UInt32ToInt (bv2nat (bvashr bx by))))))

(define-fun js.>>> ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (bv2nat (bvlshr bx by)))))

; Bitwise operators

; BUG: There seems to be an issue with Z3's bridge between integers and
; bitvectors. Currently waiting on a fix. Until then, bit ops may be incorrect.
; https://github.com/Z3Prover/z3/issues/948
(define-fun js.& ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (UInt32ToInt (bv2nat (bvand bx by))))))

(define-fun js.bitor ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (UInt32ToInt (bv2nat (bvand bx by))))))

(define-fun js.^ ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (UInt32ToInt (bv2nat (bvand bx by))))))

(define-fun js.~ ((x Val)) Val (Num (UInt32ToInt (bv2nat (bvnot (js.ToInt32 x))))))
