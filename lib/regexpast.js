"use strict";

const _ = require("lodash");

const { escapeString } = require("./smtlib");

function union(formulas) {
    if (formulas.length > 1) {
        formulas.unshift("re.union");
        return formulas;
    }
    return formulas[0];
}

function inter(formulas) {
    if (formulas.length > 1) {
        formulas.unshift("re.inter");
        return formulas;
    }
    return formulas[0];
}


class Literal {
    constructor(str) {
        this.str = str;
    }

    toRegexFormula() {
        return ["str.to.re", escapeString(this.str)];
    }
}
exports.Literal = Literal;

class Assertion {
    toRegexFormula() { return "re.allchar"; }
}
exports.Assertion = Assertion;

class StartAnchor extends Assertion {}
exports.StartAnchor = StartAnchor;

class EndAnchor extends Assertion {}
exports.EndAnchor = EndAnchor;

class WordBoundary extends Assertion {}
exports.WordBoundary = WordBoundary;

class NegatedWordBoundary extends WordBoundary {}
exports.NegatedWordBoundary = NegatedWordBoundary;

class Lookahead extends Assertion {
    constructor(expr) {
        super();
        this.expr = expr;
    }

    visit(visitor) {
        visitor(this);
        if (this.expr.visit)
            this.expr.visit(visitor);
    }

    toRegexFormula() {
        return this.expr.toRegexFormula();
    }
}
exports.Lookahead = Lookahead;

class NegatedLookahead extends Lookahead {}
exports.NegatedLookahead = NegatedLookahead;

class Or {
    constructor(disjuncts) {
        this.disjuncts = disjuncts;
    }

    visit(visitor) {
        visitor(this);
        for (const child of this.disjuncts) {
            if (child.visit)
                child.visit(visitor);
        }
    }

    _concatToFormula(concat) {
        // console.log("catting ors", concat, concat.length);
        const concatParts = ["re.++"];
        let dest = concatParts;
        for (let i = 0; i < concat.length; i++) {
            // console.log("iter i=", i);
            const part = concat[i];
//            console.log("part1", part, typeof part, concat.length);
            if (part instanceof StartAnchor || part instanceof EndAnchor || part instanceof WordBoundary || part instanceof NegatedWordBoundary) {
                continue;
            }
            const formula = part.toRegexFormula();
//            console.log("part2", part, typeof part, concat.length);
            if (part instanceof Lookahead) {
                const intersection = ["re.inter", formula];
                dest.push(intersection);
            } else {
                dest.push(formula);
            }
        }
        // console.log("done catting ors");
        if (concatParts.length === 2) {
            return concatParts[1];
        }
        return concatParts;
    }

    toRegexFormula() {
        if (this.disjuncts.length === 1) {
            return this._concatToFormula(this.disjuncts[0]);
        }

        return union(this.disjuncts.map((x) => {
            return this._concatToFormula(x);
        }));
    }
}
exports.Or = Or;

class Quantifier {
    constructor(subject = null) {
        this.subject = subject;
        this.lazy = false;
    }

    visit(visitor) {
        visitor(this);
        if (this.subject.visit)
            this.subject.visit(visitor);
    }

    setSubject(subject) {
        this.subject = subject;
    }

    setLazy(lazy) {
        this.lazy = lazy;
    }
}
exports.Quantifier = Quantifier;

class Star extends Quantifier {
    toRegexFormula() {
        return ["re.*", this.subject.toRegexFormula()];
    }
}
exports.Star = Star;

class Plus extends Quantifier {
    toRegexFormula() {
        return ["re.+", this.subject.toRegexFormula()];
    }
}
exports.Plus = Plus;

class Opt extends Quantifier {
    toRegexFormula() {
        return ["re.opt", this.subject.toRegexFormula()];
    }
}
exports.Opt = Opt;

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
                return ["re.*", regex];
            } else if (this.min === 1) {
                return ["re.plus", regex];
            } else {
                return ["re.++", ["re.loop", regex, this.min, this.max],
                    ["re.*", regex]
                ];
            }
        } else {
            return ["re.loop", regex, this.min, this.max];
        }
    }
}
exports.Repeat = Repeat;

class Dot {
    toRegexFormula() {
        return ["re.range", '"\\x00"', '"\\xFF"'];
    }
}
exports.Dot = Dot;

class Capture {
    constructor(expr) {
        if (expr === undefined)
            throw new Error();
        this.expr = expr;
    }

    visit(visitor) {
        visitor(this);
        if (this.expr.visit)
            this.expr.visit(visitor);
    }

    toRegexFormula() {
        return this.expr.toRegexFormula();
    }
}
exports.Capture = Capture;

class NonCapture {
    constructor(expr) {
        this.expr = expr;
    }

    visit(visitor) {
        visitor(this);
        if (this.expr.visit)
            this.expr.visit(visitor);
    }

    toRegexFormula() {
        return this.expr.toRegexFormula();
    }
}
exports.NonCapture = NonCapture;

class Backref {
    constructor(idx) {
        this.idx = idx;
    }

    toRegexFormula() {
        return "re.allchar";
        // throw new Error("not implemented");
    }
}
exports.Backref = Backref;

class CharClass {
    constructor(negated, members) {
        this.negated = negated;
        this.members = members;
    }

    toRegexFormula() {
        if (!this.negated) {
            return union(this.members.map((x) => x.toRegexFormula()));
        } else {
            return inter(this.members.map((x) => x.toRegexFormula(true)));
        }
    }
}
exports.CharClass = CharClass;

class CharSet {
    constructor(negated, chars) {
        this.negated = negated;
        this.chars = chars;
    }

    toRegexFormula(negate) {
        let chars = this.chars;
        if (negate) {
            const charset = new Set(chars);
            const negated = [];
            for (let i = 0; i < 256; ++i) {
                const c = String.fromCharCode(i);
                if (!charset.has(c)) {
                    negated.push(c);
                }
            }
            chars = negated;
        }

        const codes = _.map(chars, (c) => c.charCodeAt(0));
        codes.sort();
        const ranges = [];
        let lower = codes[0];
        let upper = lower;
        for (let i = 1; i < codes.length; i++) {
            const c = codes[i];
            if (c - upper <= 1) {
                upper = c;
            } else {
                const clower = escapeString(String.fromCharCode(lower));
                if (lower === upper) {
                    ranges.push(["str.to.re", clower]);
                } else {
                    ranges.push(["re.range", clower, escapeString(String.fromCharCode(upper))]);
                }
                lower = upper = c;
            }
        }

        const clower = escapeString(String.fromCharCode(lower));
        if (lower === upper) {
            ranges.push(["str.to.re", clower]);
        } else {
            ranges.push(["re.range", clower, escapeString(String.fromCharCode(upper))]);
        }
        return union(ranges);
    }
}
exports.CharSet = CharSet;

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
            return ["re.union", ["re.range", '"\\x00"', start],
                ["re.range", end, '"\\xFF"']
            ];
        }

    }
}
exports.CharRange = CharRange;

class DigitClass {
    constructor(negated=false) {
        this.negated = negated;
    }

    toRegexFormula() {
        return ["re.range", '"0"', '"9"'];
    }
}
exports.DigitClass = DigitClass;

class WordClass {
    constructor(negated=false) {
        this.negated = negated;
    }

    toRegexFormula() {
        return ["re.union", ["re.range", '"a"', '"z"'],
            ["re.range", '"A"', '"Z"']
        ];
    }
}
exports.WordClass = WordClass;

class CaptureVisitor {
    constructor(genName, genCapture) {
        this._genName = genName;
        this._genCapture = genCapture;
        this.captureNames = [];
        this.captureIdx = 0;
    }

    visit(ast, strName) {
        switch (ast.constructor) {
            case Or: {
                // Disjunctions are matched left-to-right. We represent this using a
                // sequence of nested ite-expressions.
                const result = [];
                let cursor = result;
                for (let i = 0; i < ast.disjuncts.length - 1; ++i) {
                    const alt = ast.disjuncts[i];

                    const beforeCaptureIdx = this.captureIdx;
                    const then = this.visit(alt, strName);
                    const else_ = [];
                    for (let j = beforeCaptureIdx; j < this.captureIdx; ++j) {
                        else_.push(["=", this.captureNames[j], "undefined"]);
                    }
                    else_.unshift("and");

                    cursor.push([
                        "ite",
                        ["str.in.re", strName, ast._concatToFormula(alt)],
                        then,
                        else_
                    ]);
                    cursor = else_;
                }
                cursor.push(this.visit(_.last(ast.disjuncts), strName));
                return result[0];
            }
            case Array: {
                if (ast.length === 1) {
                    return this.visit(ast[0], strName);
                }

                let sum = ["str.++"];
                const result = ["and", ["=", strName, sum]];
                for (const term of ast) {
                    const termName = this._genName();
                    result.push(this.visit(term, termName));
                    if (ast instanceof Lookahead) {
                        const rest = this._genName();
                        sum.push(rest);
                        result.push(["str.prefixof", termName, rest]);
                        sum = ["str.++"];
                        result.push(["=", rest, sum]);
                    } else {
                        sum.push(termName);
                    }
                }
                return result;
            }
            case Star:
            case Plus:
            case Opt:
            case Repeat:
                // FIXME: introduce a new string variable at the end, in order
                // to correctly handle expressions like (a)*, where only the
                // last iteration should be captured.
                return ["and", ["str.in.re", strName, ast.toRegexFormula()],
                    this.visit(ast.subject, strName)
                ];
            case Lookahead:
            case NegatedLookahead:
            case NonCapture:
                return this.visit(ast.expr, strName);
            case Capture: {
                const name = this._nextCaptureName();
                return ["and", ["=", name, ["Str", strName]], this.visit(ast.expr, strName)];
            }
            default:
                return ["str.in.re", strName, ast.toRegexFormula()];
        }
    }

    _nextCaptureName() {
        const capture = this._genCapture();
        this.captureNames.push(capture);
        return capture;
    }
}
exports.CaptureVisitor = CaptureVisitor;
