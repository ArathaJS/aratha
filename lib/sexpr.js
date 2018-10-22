"use strict";

const _ = require("lodash");

exports.Parser = class Parser {
    constructor() {
        this._levels = [];
        this._curtok = null;
        this._parsingString = false;
        this._numQuotes = 0;
    }

    parse(str, cb) {
        for (let i = 0; i < str.length; ++i) {
            const expr = this._feedChar(str[i]);
            if (expr !== null && this._levels.length === 0) {
                cb(expr);
            }
        }
    }

    _feedChar(char) {
        if (this._parsingString) {
            if (char === '"') {
                this._numQuotes++;

                if (this._numQuotes >= 2) {
                    this._numQuotes -= 2;
                    this._curtok += '"';
                }

                return null;
            } else {
                if (this._numQuotes === 0) {
                    this._curtok += char;
                    return null;
                } else if (this._numQuotes === 1) {
                    this._parsingString = false;
                    this._numQuotes = 0;
                    this._finishToken();
                } else {
                    throw new Error("impossible");
                }
            }
        }

        switch (char) {
            case "\r":
            case "\n":
            case "\t":
            case " ":
                return this._finishToken();
            case "(":
                this._levels.push([]);
                break;
            case ")":
                if (this._levels.length >= 1) {
                    this._finishToken();
                    const expr = this._levels.pop();
                    if (this._levels.length > 0) {
                        _.last(this._levels).push(expr);
                    } else {
                        return expr;
                    }
                } else {
                    throw new Error("parse error: too many close-parens");
                }
                break;
            case '"':
                this._parsingString = true;
                this._curtok = "";
                break;
            default:
                if (this._curtok === null) {
                    this._curtok = "";
                }
                this._curtok += char;
                break;
        }

        return null;
    }

    _finishToken() {
        const token = this._curtok;
        if (token === null)
            return null;
        this._curtok = null;

        if (this._levels.length > 0) {
            _.last(this._levels).push(token);
            return null;
        } else {
            return token;
        }
    }
};

class StringifyError extends Error {}

exports.stringify = function stringify(expr) {
    switch (typeof expr) {
        case "undefined":
            return "undefined";
        case "number":
            // NOTE: round because we don't support floating-point on the
            // SMT-LIB side.
            expr = Math.round(expr);
            // FIXME: toFixed() only works up to 20 digits, and SMT-LIB doesn't
            // handle exponential notation.
            return expr >= 0 ? expr.toFixed() : ["-", (-expr).toFixed()];
        case "string":
            return expr;
        case "boolean":
            return expr ? "true" : "false";
        case "object":
            if (_.isArray(expr)) {
                return "(" + _.join(_.map(expr, stringify), " ") + ")";
            }
            if (expr === null)
                return "null";
    }
    throw new StringifyError("cannot stringify " + String(expr));
};
