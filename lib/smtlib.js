"use strict";

function asciiToHex(code) {
    return "\\x" + code.toString(16).padStart(2, "0");
}
// huzi add
function unicodeToHex(code) {
    return "\\u{" + code.toString(16) + "}";
}
exports.escapeString = function(s) {
    // huzi add, for ostrich \\ parse
    s = s.replace(/\\/g, "\\\\");
    s = s.replace(/\r/g, "\\r");
    s = s.replace(/\n/g, "\\n");
    //s = s.replace(/\b/g, "\\b");
    s = s.replace(/\f/g, "\\f");
    s = s.replace(/\t/g, "\\t");
    s = s.replace(/\v/g, "\\v");
    s = s.replace(/[^\x20-\x7E]/g, (c) => {
        const code = c.charCodeAt(0);
        if (code <= 255) {
            // huzi add
            // return asciiToHex(code);
            return unicodeToHex(code);
        } else {
            // huzi add
            // return asciiToHex(code % 256, code >>> 8);
            return unicodeToHex(code);
        }
    });
    s = s.replace(/"/g, '""');
    return '"' + s + '"';
};
