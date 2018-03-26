"use strict";

exports.escapeString = function(s) {
    s = s.replace(/\r/g, "\\r");
    s = s.replace(/\n/g, "\\n");
    //s = s.replace(/\b/g, "\\b");
    s = s.replace(/\f/g, "\\f");
    s = s.replace(/\t/g, "\\t");
    s = s.replace(/\v/g, "\\v");
    s = s.replace(/[^\x20-\x7E]/g, (c) => "\\x" + c.charCodeAt(0).toString(16));
    s = s.replace(/"/g, '""');
    return '"' + s + '"';
};
