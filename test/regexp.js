/* global describe it */

"use strict";

const RegExpParser = require("../lib/regexp");

const util = require("util");

const regexps = [
    /abcdef|derp|sdf|(abc){1,}/,
    /(?=abcdef).*/,
    /abc\0/,
    /(abc)\0\1/,
    /[a-zA-Z0-9]*/,
    /\w+/
];

describe("the regex parser", function() {
    for (let i = 0; i < regexps.length; i++) {
        const regexp = regexps[i];
        it("parses " + regexp, function() {
            const parsed = RegExpParser.parse(regexp.source);
            console.log("checking:", regexp);
            console.log(util.inspect(parsed, {depth: null}));
            console.log(util.inspect(parsed.toRegexFormula(), {depth: null}));
        });
    }
});
