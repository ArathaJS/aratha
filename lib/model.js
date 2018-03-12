"use strict";

const _ = require("lodash");

function parseNumericExpr(expr) {
    if (typeof expr === "string")
        return parseFloat(expr, 10);

    const args = _.map(expr.slice(1), parseNumericExpr);
    switch (expr[0]) {
        case "-":
            return _.reduce(args, (total, x) => total - x, 0);
        case "/":
            return args[0] / args[1];
        default:
            throw new Error("unknown operator " + expr[0]);
    }
}

function parsePrimitive(value) {
    if (value === "undefined") { return undefined; }
    if (value === "null") { return null; }

    const type = value[0];
    let contents = value[1];
    switch (type) {
        case "Boolean":
            return contents === "true";
        case "Num":
            return parseNumericExpr(contents);
        case "Str":
            contents = contents.replace(/\\x([a-fA-F0-9]{2})/g, (a, b) => {
                return String.fromCharCode(parseInt(b, 16));
            });
            contents = contents.replace(/\\b/g, "\b");
            contents = contents.replace(/\\e/g, "\x1B");
            contents = contents.replace(/\\n/g, "\n");
            contents = contents.replace(/\\r/g, "\r");
            contents = contents.replace(/\\f/g, "\f");
            contents = contents.replace(/\\t/g, "\t");
            contents = contents.replace(/\\v/g, "\v");
            return contents;
        default:
            throw new Error("invalid primitive " + value.toString());
    }
}

function isVarName(name) {
    return name.startsWith("var");
}

function parseITEEqualsChain(chain, varName, output) {
    while (chain[0] === "ite") {
        const if_ = chain[1];
        const op = if_[0],
            lhs = if_[1],
            rhs = if_[2];

        if (op !== "=")
            throw new Error(`expected =, got ${op}`);

        let key;
        if (lhs === varName) {
            key = rhs;
        } else if (rhs === varName) {
            key = lhs;
        } else {
            throw new Error(`missing variable name ${varName} in ${if_}`);
        }
        // Output the then clause.
        output[key] = chain[2];

        // Continue down the else clause.
        chain = chain[3];
    }

    // Return the last else clause.
    return chain;
}

function parseMapFunction(fun, output) {
    return parseITEEqualsChain(fun.expr, fun.args[0][0], output);
}

function parseModel(model) {
    const objects = {};

    function parseModelValue(value) {
        if (value[0] === "Obj") {
            const objId = value[1];
            if (!objects.hasOwnProperty(objId)) {
                objects[objId] = {};
            }
            return objects[objId];
        } else {
            return parsePrimitive(value);
        }
    }

    const solution = {};
    const funs = {};
    for (let i = 1; i < model.length; i++) {
        const sentence = model[i];
        if (sentence[0] === "define-fun") {
            const name = sentence[1];
            const value = sentence[4];
            funs[name] = { args: sentence[2], expr: value };
            if (!isVarName(name))
                continue;
            solution[name] = parseModelValue(value);
        } else if (sentence[0] === "declare-datatypes") {
            continue;
        } else {
            console.warn("unknown model sentence", sentence);
        }
    }

    function extractObjectModel(expr) {
        if (expr[0] === "_" && expr[1] === "as-array") {
            const model = {};
            const modelName = expr[2];
            parseMapFunction(funs[modelName], model);
            return model;
        } else if (expr[0] === "store") {
            const base = extractObjectModel(expr[1]);
            base[expr[2]] = expr[3];
            return base;
        } else if (expr[0][0] === "as", expr[0][1] === "const") {
            return {};
        } else {
            console.error(expr);
            throw new Error("invalid object expression " + expr);
        }
    }

    function parseObjectModel(expr) {
        for (const k in expr) {
            if (expr.hasOwnProperty(k)) {
                if (expr[k] === "Nothing") {
                    delete expr[k];
                } else {
                    expr[k] = parseModelValue(expr[k][1]);
                }
            }
        }
        return expr;
    }

    const getProperties = funs.GetProperties;
    if (getProperties) {
        const objModelExprs = {};
        const fallbackExpr = parseMapFunction(getProperties, objModelExprs);

        _.forOwn(objModelExprs, (expr, id) => {
            const objModel = parseObjectModel(extractObjectModel(expr));
            if (!objects.hasOwnProperty(id))
                objects[id] = {};
            Object.assign(objects[id], objModel);
            delete objects[id];
        });

        const fallbackModel = parseObjectModel(extractObjectModel(fallbackExpr));
        _.forOwn(objects, (obj) => {
            Object.assign(obj, fallbackModel);
        });
    }

    return solution;
}

exports.parseModel = parseModel;
