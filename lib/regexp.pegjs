{

const {
    Pattern,
    Literal,
    Assertion,
    StartAnchor,
    EndAnchor,
    WordBoundary,
    NegatedWordBoundary,
    Lookahead,
    NegatedLookahead,
    Or,
    Quantifier,
    Star,
    Plus,
    Opt,
    Repeat,
    Dot,
    Capture,
    NonCapture,
    Backref,
    CharClass,
    CharSet,
    CharRange,
    DigitClass,
    WordClass
} = require("./regexpast");

function simplifyConcat(concat) {
    if (concat.length <= 0)
        return concat;
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

function parseHexChar(h) {
    return String.fromCharCode(parseInt(h, 16));
}

const DIGIT = "1234567890";
const WHITESPACE = "\t\v\f \u00A0\uFEFF\r\n\u2028\u2029\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200A\u202F\u205F\u3000";
const WORD = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";

}

Pattern
    = d:Disjunction { return new Pattern(d); }

Disjunction
    = head:Alternative rest:("|" part:Alternative { return part; })* {
        head = simplifyConcat(head);
        rest = rest.map(simplifyConcat);
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
    / "(" expr:Disjunction ")" { return new Capture(expr); }
    / "(?:" expr:Disjunction ")" { return new NonCapture(expr); }

PatternCharacter
    = [^$\\.*+?^()[\]{}|]

AtomEscape
    = DecimalEscape
    / CharacterClassEscape
    / c:CharacterEscape { return new Literal(c); }

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
    = "x" h:(HexDigit HexDigit) { return parseHexChar(h.join('')); }

UnicodeEscapeSequence
    = "u" h:(HexDigit HexDigit HexDigit HexDigit) { return parseHexChar(h.join('')); }

HexDigit
    = [0-9a-fA-F]

IdentityEscape
    = [^] /* SourceCharacter but not IdentifierPart */
    / "\u200D"
    / "\u200C"

CharacterClassEscape
    = "d" { return new DigitClass(); }
    / "D" { return new CharSet(true, DIGIT); }
    / "s" { return new CharSet(false, WHITESPACE); }
    / "S" { return new CharSet(true, WHITESPACE); }
    / "w" { return new WordClass(); }
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
