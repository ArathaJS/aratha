{

function escapeString(s) { return '"' + s.replace('"', '""') + '"'; }

class Literal {
    constructor(str) {
        this.str = str;
    }

    toRegexFormula() {
        return ["str.to.re", escapeString(this.str)];
    }
}

function simplifyConcat(concat) {
    let cursor = 0;
    for (let j = 1; j < concat.length; j++) {
        const part = concat[j];
        if (part instanceof Literal && concat[cursor] instanceof Literal) {
            concat[cursor].str += part.str;
        } else {
            cursor++;
            concat[cursor] = part;
        }
    }
    concat.length = cursor + 1;
    return concat;
}

class Or {
    constructor(disjuncts) {
        this.disjuncts = disjuncts;
    }

    _concatToFormula(concat) {
        const concatParts = ["re.++"];
        let dest = concatParts;
        for (let i = 0; i < concat.length; i++) {
            const part = concat[i];
            const formula = part.toRegexFormula();
            if (part instanceof Lookahead) {
                const intersection = ["re.inter", formula]
                dest.push(intersection);
                dest = intersection;
            } else {
                dest.push(formula);
            }
        }
        if (concatParts.length === 2) {
            return concatParts[1];
        }
        return concatParts;
    }

    toRegexFormula() {
        if (this.disjuncts.length === 1) {
            return this._concatToFormula(this.disjuncts[0]);
        }

        const formulas = this.disjuncts.map((x) => {
            return this._concatToFormula(x);
        });
        formulas.unshift("re.union");
        return formulas;
    }
}

class Quantifier {
    constructor(subject = null) {
        this.subject = subject;
    }

    setSubject(subject) {
        this.subject = subject;
    }
}

class Star extends Quantifier {
    toRegexFormula() {
        return ["re.*", this.subject.toRegexFormula()];
    }
}

class Plus extends Quantifier {
    toRegexFormula() {
        return ["re.*", this.subject.toRegexFormula()];
    }
}

class Opt extends Quantifier {
    toRegexFormula() {
        return ["re.opt", this.subject.toRegexFormula()];
    }
}

class Repeat extends Quantifier {
    constructor(min, max, subject = null) {
        super(subject);
        this.min = min;
        this.max = max;
    }

    toRegexFormula() {
        const regex = this.subject.toRegexFormula();
        if (this.max === null) {
            if (this.min === 0) {
                return ["re.star", regex];
            } else if (this.min === 1) {
                return ["re.plus", regex]
            } else {
                return ["re.++", ["re.loop", regex, this.min, this.min], ["re.star", regex]];
            }
        } else {
            return ["re.loop", regex, this.min, this.mix];
        }
    }
}

class Assertion {
}

class StartAnchor extends Assertion {
}

class EndAnchor extends Assertion {
}

class WordBoundary extends Assertion {
}

class NegatedWordBoundary extends WordBoundary {
}

class Lookahead extends Assertion {
    constructor(expr) {
        super();
        this.expr = expr;
    }

    toRegexFormula() {
        return this.expr.toRegexFormula();
    }
}

class NegatedLookahead extends Lookahead {
}

class Dot {
    toRegexFormula() {
        return ["str.range", '"\\x00"', '\\xFF'];
    }
}

class NonCapture {
    constructor(expr) {
        this.expr = expr;
    }
}

class Backref {
    constructor(idx) {
        this.idx = idx;
    }

    toRegexFormula() {
        throw new Error("not implemented");
    }
}

function parseHexChar(h) {
    return String.fromCharCode(parseInt(h, 16));
}

class CharClass {
    constructor(negated, members) {
        this.negated = negated;
        this.members = members;
    }

    toRegexFormula() {
        if (!this.negated) {
            const formula = this.members.map((x) => x.toRegexFormula());
            formula.unshift("re.union");
            return formula;
        } else {
            const formula = this.members.map((x) => x.toRegexFormula(true));
            formula.unshift("re.inter");
            return formula;
        }
    }
}

class CharSet {
    constructor(negated, chars) {
        this.negated = negated;
        this.chars = chars;
    }

    toRegexFormula(negate) {
        if (negate)
            throw new Error("not implemented");

        const formula = ["re.union"];
        for (let i = 0; i < this.chars.length; i++) {
            const c = this.chars[i];
            formula.push(["str.to.re", escapeString(c)]);
        }
        return formula;
    }
}

const DIGIT = "1234567890";
const WHITESPACE = "\t\v\f \u00A0\uFEFF\r\n\u2028\u2029\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200A\u202F\u205F\u3000";
const WORD = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";

class CharRange {
    constructor(start, end) {
        this.start = start;
        this.end = end;
    }

    toRegexFormula(negate) {
        const start = escapeString(this.start);
        const end = escapeString(this.end);
        if (!negate) {
            return ["re.range", start, end];
        } else {
            return ["re.union", ["re.range", '"\\x00"', start], ["re.range", end, '"\\xFF"']];
        }

    }
}

}

Pattern
    = Disjunction

Disjunction
    = head:Alternative rest:("|" part:Alternative { return part; })* {
        head = simplifyConcat(head);
        rest = rest.map(simplifyConcat);
        if (rest.length == 0 && head.length === 1) {
            return head[0];
        }
        rest.unshift(head);
        return new Or(rest);
    }

Alternative
    = Term*

Term
    = Assertion
    / atom:Atom quantifier:(Quantifier ?) { if (quantifier) { quantifier.setSubject(atom); return quantifier; } return atom; }

Assertion
    = "^" { return new StartAnchor(); }
    / "$" { return new EndAnchor(); }
    / "\\b" { return new WordBoundary(); }
    / "\\B" { return new NegatedWordBoundary(); }
    / "(?=" expr:Disjunction ")" { return new Lookahead(expr); }
    / "(?!" expr:Disjunction ")" { return new NegatedLookahead(expr); }

Quantifier
    = prefix:QuantifierPrefix isLazy:("?" ?) { if (isLazy) { prefix.setLazy(true); } return prefix; }

QuantifierPrefix
    = "*" { return new Star(); }
    / "+" { return new Plus(); }
    / "?" { return new Opt(); }
    / "{" min:DecimalDigits "}" { return new Repeat(min, min); }
    / "{" min:DecimalDigits "," max:(DecimalDigits ?) "}" { return new Repeat(min, max); }

DecimalDigits
    = digits:DecimalDigit+ { return parseInt(digits.join(""), 10); }

DecimalDigit
    = [0-9]

Atom
    = c:PatternCharacter { return new Literal(c); }
    / "." { return new Dot(); }
    / "\\" esc:AtomEscape { return esc; }
    / CharacterClass
    / "(" expr:Disjunction ")" { return expr; }
    / "(?:" expr:Disjunction ")" { return NonCapture(expr); }

PatternCharacter
    = [^$\\.*+?^()[\]{}|]

AtomEscape
    = DecimalEscape
    / CharacterEscape
    / CharacterClassEscape

DecimalEscape
    = n:DecimalIntegerLiteral !DecimalDigit { return n === 0 ? new Literal("\0") : new Backref(n); }

DecimalIntegerLiteral
    = "0" { return 0; }
    / n:(NonZeroDigit (DecimalDigits ?)) { return parseInt(n, 10); }

NonZeroDigit
    = [1-9]

CharacterEscape
    = ControlEscape
    / "c" code:[a-z]i { return String.fromCharCode(code.charCodeAt(0) % 32); }
    / HexEscapeSequence
    / UnicodeEscapeSequence
    / IdentityEscape

ControlEscape
    = "f" { return "\f"; }
    / "n" { return "\n"; }
    / "r" { return "\r"; }
    / "t" { return "\t"; }
    / "v" { return "\v"; }

HexEscapeSequence
    = "x" h:(HexDigit HexDigit) { return parseHexChar(h); }

UnicodeEscapeSequence
    = "u" h:(HexDigit HexDigit HexDigit HexDigit) { return parseHexChar(h); }

HexDigit
    = [0-9a-fA-F]

IdentityEscape
    = [^] /* SourceCharacter but not IdentifierPart */
    / "\u200D"
    / "\u200C"

CharacterClassEscape
    = "d" { return new CharSet(false, DIGIT); }
    / "D" { return new CharSet(true, DIGIT); }
    / "s" { return new CharSet(false, WHITESPACE); }
    / "S" { return new CharSet(true, WHITESPACE); }
    / "w" { return new CharSet(false, WORD); }
    / "W" { return new CharSet(true, WORD); }

CharacterClass
    = "[" negated:("^" ?) ranges:ClassRange* "]" { return new CharClass(!!negated, ranges); }

ClassRange
    = start:ClassAtom "-" end:ClassAtom { return new CharRange(start, end); }
    / atom:ClassAtom { return new CharSet(false, atom); }

ClassAtom
    = "-"
    / ClassAtomNoDash

ClassAtomNoDash
    = [^\-\]\\]
    / "\\" esc:ClassEscape { return esc; }

ClassEscape
    = DecimalEscape
    / "b" { return "\b"; }
    / CharacterEscape
    / CharacterClassEscape
