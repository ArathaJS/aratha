"use strict";

function asciiToHex(code) {
    return "\\x" + code.toString(16).padStart(2, "0");
}

exports.escapeString = function(s) {
    s = s.replace(/\r/g, "\\r");
    s = s.replace(/\n/g, "\\n");
    //s = s.replace(/\b/g, "\\b");
    s = s.replace(/\f/g, "\\f");
    s = s.replace(/\t/g, "\\t");
    s = s.replace(/\v/g, "\\v");
    s = s.replace(/[^\x20-\x7E]/g, (c) => {
        const code = c.charCodeAt(0);
        if (code <= 255) {
            return asciiToHex(code);
        } else {
            return asciiToHex(code % 256, code >>> 8);
        }
    });
    s = s.replace(/"/g, '""');
    return '"' + s + '"';
};
