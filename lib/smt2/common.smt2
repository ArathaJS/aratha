; ECMAScript internal functions
;
; These will have the same name as the functions in the specification with
; "js." prepended. The generally return values of an SMT-LIB sort, and may
; need to be wrapped with Val.

(define-sort Properties () (Array String MaybeVal))
(declare-fun GetProperties (Int) Properties)

(define-fun NumberToString ((x Int)) String (ite (>= x 0) (int.to.str x) (str.++ "-" (int.to.str (- x)))))

(define-fun js.ToString ((x Val)) String
    (ite (is-Str x) (str x)
    (ite (is-undefined x) "undefined"
    (ite (is-null x) "null"
    (ite (is-Boolean x) (ite (bool x) "true" "false")
    (ite (is-Num x) (NumberToString (num x))
    "[object Object]"))))))

; TODO: implement more of the string-to-number semantics
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
    0)))))) ; Otherwise we're an Object, but we don't have NaNs, so we'll return zero here.

(define-fun js.ToInteger ((x Val)) Int (js.ToNumber x))

(define-fun js.ToBoolean ((x Val)) Bool
    (ite (is-Num x) (distinct (num x) 0)
    (ite (is-undefined x) false
    (ite (is-null x) false
    (ite (is-Boolean x) (bool x)
    (ite (is-Str x) (distinct (str x) "")
    true))))))

(define-fun SameType ((x Val) (y Val)) Bool (or
    (and (is-undefined x) (is-undefined y))
    (and (is-null x) (is-null y))
    (and (is-Boolean x) (is-Boolean y))
    (and (is-Str x) (is-Str y))
    (and (is-Num x) (is-Num y))))

(define-fun typeof ((x Val)) String
    (ite (is-Num x) "number"
    (ite (is-undefined x) "undefined"
    (ite (is-Boolean x) "boolean"
    (ite (is-Str x) "string"
    "object"))))) ; NOTE: typeof null === "object"

(define-fun EmptyObject () Properties ((as const Properties) Nothing))

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

; ECMAScript expressions

; Binary operators

(define-fun js.in ((x String) (y Properties)) Bool (is-Just (select y x)))

; Relational operators
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

;(define-fun CharToCode ((x String)) Int
;    (ite (= x "\x00") 0
;    1))
;(define-fun StrLessThan ((x String) (y String)) Bool
;    (and (not (str.prefixof y x)) (or (str.prefixof x y)
;    (exists ((i Int)) (and (<= 0 i) (< i (str.len x)) (< i (str.len y)) (= (str.substr x 0 i) (str.substr y 0 i)) (< (CharToCode (str.at x i)) (CharToCode (str.at y i))))))))

; NOTE: "ab" < "ac" returns false by this definition, even though "c" < "a".
; This is because we can't implement the character-level < operation, since Z3
; doesn't (yet) let us access individual characters within strings/sequences.
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

; Object relational operators

; BUG: Since there is little to no support for recursive functions, our
; axiomatization does not support prototypes, so we can never produce a model
; satisfying instanceof. As such, we define it to always be false.
(define-fun js.instanceof ((obj Val) (proto Val)) Bool false)

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
    (Num (div (js.ToNumber x) (js.ToNumber y))))

(define-fun js.% ((x Val) (y Val)) Val
    (Num (mod (js.ToNumber x) (js.ToNumber y))))

; Unary operators

(define-fun js.! ((x Bool)) Bool (not x))
(define-fun js.void ((x Val)) Val undefined)
(define-fun js.typeof ((x Val)) Val (Str (typeof x)))
(define-fun js.u+ ((x Val)) Val (Num (js.ToNumber x)))
(define-fun js.u- ((x Val)) Val (Num (- (js.ToNumber x))))

(define-fun min ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun max ((x Int) (y Int)) Int (ite (> x y) x y))
(define-fun clamp ((x Int) (lower Int) (upper Int)) Int (min (max x lower) upper))

; String functions

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

(define-fun js.constructArray ((len Val)) Properties
    (ite (is-Num len)
        (store EmptyObject "length" (Just len))
        (store (store EmptyObject "length" (Just (Num 1))) "0" (Just len))))

(define-fun IsWhitespaceString ((s String)) Bool (str.in.re s (re.* (re.union (str.to.re " ") (str.to.re "\xa0") (str.to.re "\t") (str.to.re "\f") (str.to.re "\v") (str.to.re "\r") (str.to.re "\n")))))

; TODO: implement parseInt for radices other than 10
(define-fun ParseIntCondition ((s String) (radix Int) (ws String) (numPart String) (rem String) (i Int)) Bool
    (and
        (= s (str.++ ws numPart rem))
        (IsWhitespaceString ws)
        (not (= "" numPart))
        (str.in.re numPart (re.++ (re.opt (str.to.re "-")) (re.+ (re.range "0" "9"))))
        (or (= 0 radix) (<= 2 radix 36))
        (or (= "" rem) (distinct (str.at rem 0) "0" "1" "2" "3" "4" "5" "6" "7" "8" "9"))
        (or (= radix 0) (= radix 10) (< i radix 10))
        (= i (StringToNumber numPart))))

(define-fun TOFIXED_ZEROS () String "00000000000000000000")

(define-fun js.toFixed ((n Int) (fracDigits Int)) String
    (ite (<= 1 fracDigits 20)
        (str.++ (NumberToString n) "." (str.substr TOFIXED_ZEROS 0 fracDigits))
        (NumberToString n)))

; The number regex for JavaScript is:
; \s*(0(x|X)[0-9a-fA-F]+|(+|-)?[0-9]*(\.)?[0-9]+(e|E)(+|-)?[0-9]+)\s*
; FIXME: add support for whitespace before and after
(define-fun IsFiniteNumberString ((s String)) Bool
    (str.in.re s (re.opt (re.union
        (re.++
            (str.to.re "0")
            (re.union (str.to.re "x") (str.to.re "X"))
            (re.+ (re.union
                (re.range "0" "9")
                (re.range "a" "f")
                (re.range "A" "F"))))
        (re.++
            (re.opt (re.union (str.to.re "+") (str.to.re "-")))
            (re.* (re.range "0" "9"))
            (re.union ; Need at least one digit before or after the point.
                (re.++ (re.range "0" "9") (re.opt (str.to.re ".")))
                (re.++ (str.to.re ".") (re.range "0" "9")))
            (re.* (re.range "0" "9"))
            (re.opt (re.++
                (re.union (str.to.re "e") (str.to.re "E"))
                (re.opt (re.union (str.to.re "+") (str.to.re "-")))
                (re.+ (re.range "0" "9")))))))))

(define-fun IsNumberString ((s String)) Bool (or
    (IsFiniteNumberString s)
    (not (distinct s "Infinity" "+Infinity" "-Infinity"))))

(define-fun js.isFinite ((v Val)) Bool
    (and
        (not (or (is-Obj v) (is-undefined v)))
        (=> (is-Str v) (IsFiniteNumberString (str v)))))
;(define-fun js.Number.isFinite ((v Val)) Bool (and (is-Num v) (js.isFinite v)))
(define-fun js.Number.isFinite ((v Val)) Bool (is-Num v))

(define-fun js.isNaN ((v Val)) Bool (or
    (is-undefined v)
    (is-Obj v)
    (and (is-Str v) (not (IsNumberString (str v))))))
(define-fun js.Number.isNaN ((v Val)) Bool false)

; FIXME: this only works for ASCII.
(define-fun js.isLowerCase ((s String)) Bool (not (str.in.re s (re.++ re.allchar (re.range "A" "Z") re.allchar))))
(define-fun js.toLowerCase ((s String)) String s)
(define-fun js.isUpperCase ((s String)) Bool (not (str.in.re s (re.++ re.allchar (re.range "a" "z") re.allchar))))
(define-fun js.toUpperCase ((s String)) String s)


(define-fun IntToInt32 ((x Int)) (_ BitVec 32) ((_ int2bv 32) x))
(define-fun js.ToInt32 ((x Val)) (_ BitVec 32) (IntToInt32 (js.ToNumber x)))

; Bit shift operators
(define-fun js.<< ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (Int32ToInt (bvshl bx by)))))

(define-fun js.>> ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (Int32ToInt (bvashr bx by)))))

(define-fun js.>>> ((x Val) (y Val)) Val
    (let ((bx (js.ToInt32 x)) (by (js.ToInt32 y)))
        (Num (Int32ToUInt (bvlshr bx by)))))

; Bitwise operators

; BUG: There seems to be an issue with Z3's bridge between integers and
; bitvectors. Currently waiting on a fix. Until then, bit ops may be incorrect.
; https://github.com/Z3Prover/z3/issues/948

(define-fun IntAnd32 ((x Int) (y Int)) Int
    (Int32ToInt (bvand (IntToInt32 x) (IntToInt32 y))))

(define-fun IntOr32 ((x Int) (y Int)) Int
    (Int32ToInt (bvor (IntToInt32 x) (IntToInt32 y))))

(define-fun IntXor32 ((x Int) (y Int)) Int
    (Int32ToInt (bvxor (IntToInt32 x) (IntToInt32 y))))

(define-fun IntNot32 ((x Int)) Int
    (Int32ToInt (bvnot (IntToInt32 x))))

(define-fun js.& ((x Val) (y Val)) Val
    (Num (IntAnd32 (js.ToNumber x) (js.ToNumber y))))

(define-fun js.bitor ((x Val) (y Val)) Val
    (Num (IntOr32 (js.ToNumber x) (js.ToNumber y))))

(define-fun js.^ ((x Val) (y Val)) Val
    (Num (IntXor32 (js.ToNumber x) (js.ToNumber y))))

(define-fun js.~ ((x Val)) Val
    (Num (IntNot32 (js.ToNumber x))))
