/* global J$ */

(function(sandbox) {
    "use strict";

    // FIXME: Turn into external parameters.
    const CP_OPTS = {
        'mznPath': 'model.mzn',
        'dznPath': 'data.dzn',
        'fznPath': 'model.fzn',
        'mznTimeout': '10',
        'mzn2fznTimeout': '3',
        'fznTimeout': '3',
        'dumpTimeout': false, //timeout.mzn',
        'mznArgs': ['--no-output-ozn'],
        'mzn2fznArgs': ['--no-output-ozn', '-o', 'model.fzn'],
        'fznArgs': [], //['-max-alpha', '65535'], //['-max-length', '1000'],  //'-reverse-regex', 'false',
        'twoSteps': false,
        'solve': 'nobj_len', //'length', 'num_len', 'typs', 'typ_len', 'str_def', 'reps'
        'debug': true, //false, //true,
        'abort': false,
        'verifyModel': false
    }
    
    const path = require("path");
    const process = require("process");
    const fs = require("fs");

    const _ = require("lodash");

    const {
        Concolic,
        isConcolic,
        concolizeObject,
        getConcrete,
        getSymbolic,
        setSymbolic,
        concretize
    } = require("./concolic");
    const { ExecutionPath, DSE } = require("./dse");
    const { doBinaryOp, doUnaryOp } = require("./ops");
    const {
        Constant,
        Variable,
        Binary,
        Unary,
        GetField,
        PutField,
        DeleteField,
        ToString,
        resetNameCounter
    } = require("./symbolic");
    const { getBuiltinShim } = require("./functionmodels");
    const Type = require("./type");
    const Z3 = require("./z3");
    const Z3str = require("./z3str");
    const CVC4 = require("./cvc4");
    const OSTRICH = require("./ostrich");
    const G_Strings = require("./g-strings")
    const { get_cp_pid } = require("./cp")

    let varNameCounter = 0;

    function getDefault(type) {
        if (Type.UNDEFINED & type) {
            return undefined;
        }

        if (Type.NULL & type) {
            return null;
        }

        if (Type.NUMBER & type) {
            return 0;
        }

        if (Type.BOOLEAN & type) {
            return false;
        }

        if (Type.STRING & type) {
            return "";
        }

        if (Type.OBJECT & type) {
            return {};
        }

        throw new Error("can't generate default for bottom type");
    }

    function getVariable(inputs, type) {
        const name = "var" + varNameCounter++;
        const concVal = inputs.hasOwnProperty(name) ? inputs[name] : getDefault(type);
        // FIXME: Check this.
        if (process.env.SOLVER !== "G-Strings" && !new Type(type).valueConforms(concVal)) {
            throw new Error("type error: " + name + " is not of type " + type);
        }
        inputs[name] = concVal;
        const symVal = new Variable(name, type);
        if (_.isObject(concVal)) {
            setSymbolic(concVal, symVal);
            return concVal;
        } else {
            return new Concolic(concVal, symVal);
        }
    }

    class ProcessExitException extends Error {}

    function createSolver(commandLog = null) {
        const SOLVER = process.env.SOLVER || "G-Strings";
        let solver;
        switch (SOLVER) {
            case "z3":
                solver = new Z3(process.env.Z3_PATH || "z3");
                break;
           case "z3str":
                solver = new Z3str(process.env.Z3STR_PATH || "z3");
                break;
            case "cvc4":
                solver = new CVC4(process.env.CVC4_PATH || "cvc4", "QF_AUFBVDTSNIA");
                break;
            case "ostrich":
                solver = new OSTRICH(process.env.OSTRICH_PATH || "ostrich", "ALL");
                break;
            case "G-Strings":
                solver = new G_Strings(CP_OPTS);
                break;
            default:
                throw new Error(`invalid solver ${SOLVER}`);
        }
        if (!solver.isCPSolver()) {
            if (commandLog) {
                solver.logCommands(commandLog);
            }
            const theoryFiles = [SOLVER + "/prelude.smt2", "common.smt2"];
            for (let i = 0; i < theoryFiles.length; i++) {
                theoryFiles[i] = path.resolve(__dirname, "smt2", theoryFiles[i]);
            }
            solver.loadFiles(theoryFiles);
        }

        return solver;
    }

    function isFunctionInstrumented(f) {
        return f.hasOwnProperty(sandbox.Constants.SPECIAL_PROP_IID) ||
            f === sandbox.readInput  || f === sandbox.readString ||
            f === sandbox.readNumber || f === sandbox.readBoolean ||
            f === sandbox.readObject || f === sandbox.check ||
            f === sandbox.assert;
    }

    class Jalangi2DSEAnalysis {
        async runAnalysis(maxIterations, cb) {
            let receivedSigint = false,
                timedOut = false;
            process.on("SIGINT", () => {
                receivedSigint = true;
                console.log("analysis: received SIGINT, terminating");
                console.log(process.kill(-get_cp_pid(), 'SIGINT'));
            });

            const analysisTimeout = parseInt(process.env.ANALYSIS_TIMEOUT, 10) || 0;
            if (analysisTimeout > 0) {
                const analysisTimer = setTimeout(function() { timedOut = true; }, analysisTimeout * 1000);
                analysisTimer.unref(); // Don't let this stall the event loop.
            }

            const dseOptions = {
                unsatCores: process.env.UNSAT_CORES === "1",
                incremental: !(process.env.SOLVER === "G-Strings") && 
                             !(process.env.INCREMENTAL === "0"),
            };

            sandbox.readInput = () => {
                return getVariable(this.inputs, Type.TOP);
            };

            sandbox.readString = () => {
                return getVariable(this.inputs, Type.STRING);
            };

            sandbox.readNumber = () => {
                return getVariable(this.inputs, Type.NUMBER);
            };

            sandbox.readBoolean = () => {
                return getVariable(this.inputs, Type.BOOLEAN);
            };

            sandbox.readObject = () => {
                return getVariable(this.inputs, Type.OBJECT);
            };

            sandbox.check = (cond) => {
                const value = this.conditional(null, cond);
                return value ? value.result : cond;
            };
            
            sandbox.assert = (cond) => {
                if(!sandbox.check(cond)) {
                    throw new ProcessExitException("J$.assert(): failed");
                }
                return cond;
            };

            sandbox.choose = (arr) => {
                arr = getConcrete(arr);
                if (arr.length > 1) {
                    let i;
                    for(i = 0; i < arr.length - 1; i++) {
                        const value = sandbox.check(sandbox.readBoolean());
                        if (getConcrete(value)) {
                            break;
                        }
                    }
                    return arr[i];
                } else {
                    return arr[0];
                }
            };
            let commandLogs = [];
            let solvers = [];
            const solver = process.env.SOLVER || 'G-Strings';
            if (solver.indexOf(',') === -1) {
                const clog = solver === 'G-Strings' ? null :
                        fs.createWriteStream("PCs_" + solver.id + ".smt2");
                solvers.push(createSolver(clog));
                commandLogs.push(clog);
            }
            else {
                for (const s of solver.split(',')) {
                    process.env.SOLVER = s;
                    const clog = s === 'G-Strings' ? null :
                        fs.createWriteStream("PCs_" + solver.id + ".smt2");
                    solvers.push(createSolver(clog));
                    commandLogs.push(clog);
                }   
            }
            try {
                // console.log(solvers)
                const inputLog = fs.openSync("inputlog.json", "w");
                let first = true;
                try {
                    fs.writeSync(inputLog, "[\n");
                    let searchers = {};
                    for (const s of solvers) {
                        searchers[s.id] = new DSE(s, async (newInput) => {
                        while (true) {
                            if (!first) {
                                fs.writeSync(inputLog, ",\n");
                            }
                            first = false;
                            var isCircular = require('is-circular');
                            if (isCircular(newInput)) {
                                console.log("Warning! Circular object detected. Ignored input")
                                newInput = {}
                            }
                            fs.writeSync(inputLog, JSON.stringify(newInput));
                              fs.fsyncSync(inputLog);
                            this.inputs = newInput;
                            this.path = new ExecutionPath();
                            resetNameCounter();
                            try {
                                cb();
                            } 
                            catch (e) {
                              if (e instanceof TypeError) {
                                // FIXME: Workaround for type errors. Better to treat method invocations 
                                //        as type constraints?
                                if (s.isCPSolver() && e instanceof TypeError) {
                                    const { JSTypes, parseSolution } = require("./cp");
                                    let sat = false;
                                    let types = Array.from(JSTypes);                                    
                                    for (let [key, val] of Object.entries(s.solution)) {
                                        if (/var\d/.test(key)) {
                                            const i = val.TYPE - 1;
                                            let t = types[i];
                                            types.splice(i, 1);
                                            while (t) {
                                                console.log("Trying with type != " + t + " for variable " + key)
                                                s.info = undefined;
                                                s.solution = {};
                                                const status = await s.runSolver("constraint TYPE_" + key + " != " + t + ";\n");
                                                if (status === "sat") {
                                                    try {
                                                        var model = parseSolution(s.getSolution());
                                                    }
                                                    catch (e) {                                                    
                                                        continue;
                                                    }
                                                    sat = true;
                                                    break;
                                                }
                                                else {
                                                   t = types[0];
                                                   types.splice(0, 1);                           
                                                }
                                            }
                                        }
                                        if (sat)
                                          break;
                                    }
                                    if (!sat)
                                        console.log("No type matching the CP model!");
                                    else {
                                       varNameCounter = 0;
                                       newInput = model;
                                       continue;
                                    }
                                }
                                else
                                    console.log("run terminated with exception:", e);
                              }
                            }
                            break;                          
                        }
                        // Delete the cached copy of the script so it can be reloaded.
                        const inputFilename = process.argv[1];
                        delete require.cache[require.resolve(inputFilename)];
                        return this.path;
                    }, dseOptions);
                  }
                    for (let i = 0; Object.keys(searchers).length && 
                             i < maxIterations && !receivedSigint && !timedOut; i++) {
                        //Promise.race([...])
                        for (let s in searchers) {
                          varNameCounter = 0;
                          try {
                            const ok = await searchers[s].execute();
                            console.log(s,"finished!",ok);
                            if (ok)
                                break;                            
                          }
                          catch (error) {
                            console.log(error);
                          }
                        }
                        for (let s in searchers)   {
                          if (searchers[s].isDone()) {
                            console.log("finished: no more constraints to solve");
                            delete searchers[s];
                          } else if (i >= maxIterations) {
                            console.log("finished: reached iteration limit");
                            delete searchers[s];
                          } else if (receivedSigint) {
                            console.log("terminated: received SIGINT");
                            delete searchers[s];
                          } else if (timedOut) {
                            console.log("terminated: timed out");
                            delete searchers[s];
                          }
                        }
                    }
                } finally {
                    for (const s of solvers)
                      s.close();
                    fs.writeSync(inputLog, "\n]\n");
                    fs.closeSync(inputLog);
                }
            } finally {
                  for (const c of commandLogs)
                    if (c)
                      c.end();
            }
        }

        conditional(iid, result) {
            if (isConcolic(result)) {
                const concVal = getConcrete(result);
                const symVal = getSymbolic(result);
                this.path.addConstraint(symVal, !!concVal);
                // If a === comparison between a concolic value and a concrete
                // value succeeds (or a !== fails), treat the concolic value as
                // if it was concrete from now on. This reduces the number of
                // constraints and thus avoids unnecessary solver calls, as well
                // as potentially saving some memory.
                if (symVal instanceof Binary &&
                    ((concVal && symVal.op === "===") || (!concVal && symVal.op === "!==")) &&
                    (symVal.left instanceof Constant || symVal.right instanceof Constant)) {
                    if (symVal.left instanceof Constant) {
                        symVal.right.forcedConstant = symVal.left;
                    } else {
                        symVal.left.forcedConstant = symVal.right;
                    }
                }
                return { result: concVal };
            }
        }

        forinObject(iid, val) {
            // NOTE: The ES5 spec leaves the iteration order of for-in
            // statements up to the implementation. Since Jalangi does not allow
            // us to influence the iteration, we must concretize the iterand.
            //
            // A for-in loop will visit every property that existed at the start
            // of the loop exactly once, though properties deleted before they
            // are visited will not be visited at all. Properties added during
            // the iteration may or may not be iterated over.
            //
            // However, the annotation on https://es5.github.io/#x12.6.4 states
            // that all modern browsers iterate in insertion order, so we may be
            // able to do something useful after all.
            if (isConcolic(val)) {
                return { result: getConcrete(val) };
            }
        }

        _with(iid, val) {
            // NOTE: This is the best we can do with the `with` statement. There
            // is no callback to indicate when we exit the `with` body, so even
            // if we tracked what names were introduced, we don't know when we
            // can release them in the same scope.
            if (isConcolic(val)) {
                return { result: getConcrete(val) };
            }
        }

        binaryPre(iid, op, left, right) {
            if (isConcolic(left) || isConcolic(right)) {
                return { op: op, left: left, right: right, skip: true };
            }
        }

        binary(iid, op, left, right) {
            if (isConcolic(left) || isConcolic(right)) {
                if (op === "instanceof") { // We can't handle prototypes, so we have to concretize instanceof.
                    return { result: getConcrete(left) instanceof getConcrete(right) };
                }

                const concResult = doBinaryOp(op, getConcrete(left), getConcrete(right));
                if (op === "delete") {
                    setSymbolic(left, new DeleteField(getSymbolic(left), getSymbolic(right)));
                }
                return { result: new Concolic(concResult, new Binary(op, getSymbolic(left), getSymbolic(right))) };
            }
        }

        unaryPre(iid, op, left) {
            if (isConcolic(left)) {
                return { op: op, left: left, skip: true };
            }
        }

        unary(iid, op, left) {
            if (isConcolic(left)) {
                const concResult = doUnaryOp(op, getConcrete(left));
                return { result: new Concolic(concResult, new Unary(op, getSymbolic(left))) };
            }
        }

        invokeFunPre(iid, f, base, args, isConstructor) {
            if (isConcolic(f)) {
                const symF = getSymbolic(f);
                if (symF instanceof GetField && !(symF.offset instanceof Constant)) {
                    const keyVal = String(symF.offset.eval(this.inputs));
                    if (symF.base instanceof Constant) {
                        this.path.addConstraint(new Binary("in", symF.offset, symF.base), keyVal in symF.base.value);
                        const keys = Object.keys(symF.base.value);
                        keys.sort();
                        for (const k of keys) {
                            this.path.addConstraint(new Binary("===", new ToString(symF.offset), new Constant(k)), k === keyVal);
                            if (k === keyVal)
                                break;
                        }
                    }
                }
            }

            const concF = getConcrete(f);
            if (!_.isFunction(concF) || isFunctionInstrumented(concF) || (!isConcolic(base) && !_.some(args, isConcolic))) {
                return { f: concF, base: base, args: args };
            }

            switch (concF) {
                case console.log:
                    return;
                case process.exit:
                    return {
                        f: function(code = 0) {
                            throw new ProcessExitException(code);
                        },
                        base: base,
                        args: args
                    };
            }

            const shim = getBuiltinShim(concF, isConstructor);
//            console.log(concF, isConstructor, shim)
            if (shim) {
                return { f: shim, base: base, args: args };
            } else if (shim === null) {
                console.warn("concretizing arguments to unmodelled native function", concF);
                return {
                    f: concF,
                    base: concretize(base),
                    args: _.map(args, concretize)
                };
            }

            // console.warn("concretizing globals: call to uninstrumented/unknown function", f);
            // concretize(global);
            console.warn("concretizing arguments to uninstrumented/unknown native function", concF);
            return {
                f: concF,
                base: concretize(base),
                args: _.map(args, concretize)
            };
        }

        getFieldPre(iid, base, offset) {
            if (isConcolic(base)) {
                const baseType = typeof getConcrete(base);
                const isValid = baseType !== "undefined" && baseType !== "null";
                this.path.addTypeConstraint(
                    new Type(~(Type.UNDEFINED | Type.NULL)), getSymbolic(base), isValid);
            }

            if (isConcolic(base) || isConcolic(offset)) {
                return { base: base, offset: offset, skip: true };
            }
        }

        getField(iid, base, offset) {
            if (isConcolic(base) || isConcolic(offset)) {
                const cbase = getConcrete(base);
                const coffset = getConcrete(offset);
                const sbase = getSymbolic(base);
                const soffset = getSymbolic(offset);

                const simplified = GetField.simplify(sbase, soffset);
                if (simplified) {
                    return simplified;
                }

                return { result: new Concolic(cbase[coffset], new GetField(sbase, soffset)) };
            }
        }

        putFieldPre(iid, base, offset, val) {
            if (isConcolic(offset) && !isConcolic(base)) {
                concolizeObject(base);
            }

            if (isConcolic(base)) {
//                console.dir(["putFieldPre", base, offset, val], {depth:null});
                const baseConcVal = getConcrete(base);
                const baseType = typeof baseConcVal;
                const isValid = baseType !== "undefined" && baseType !== "null";
                const baseSymVal = getSymbolic(base);
                this.path.addTypeConstraint(
                    new Type(~(Type.UNDEFINED | Type.NULL)), baseSymVal, isValid);

                // Attach a PutField to our object value chain, and set the base
                // to the concrete object for the assignment.
                setSymbolic(base, new PutField(baseSymVal, getSymbolic(offset), getSymbolic(val)));
                base = baseConcVal;
            }

            return { base: base, offset: getConcrete(offset), val: val };
        }

        onReady(cb) {
            const MAX_ITERATIONS = 1024;
            this.runAnalysis(MAX_ITERATIONS, cb).catch((e) => {
                console.error("analysis terminated with exception:", e);
            });
        }
    }


    sandbox.analysis = new Jalangi2DSEAnalysis();
    // huzi add
    sandbox.isOstrich = true;   // we generate special capture-group syntax for ostrich
    sandbox.isTest = false;     // whether the parser of RegExp is about RegExp.test
    sandbox.isReference = false;   // whether replacement of function replace contains reference
    sandbox.captureNum = 1;      // for ostrich replace_cg_all benchmark generation
})(J$);
