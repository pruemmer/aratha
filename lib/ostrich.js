const child_process = require("child_process");
const { SMTSolver } = require("./smt");

class OSTRICH extends SMTSolver {

    constructor(solverPath, logic) {
        const args = [
            "-inputFormat=smtlib",
            "+incremental",
            "+quiet",
            "-timeoutPer=10000",
            "+stdin",
            "-adtMeasure=relDepth"
        ];
        if (process.env.UNSAT_CORES === "1") {
            args.push("+unsatCore");
        }
        const ostrich = child_process.spawn(solverPath, args);
        super(ostrich);
        this._send(["set-logic", logic]);
        this.id = "ostrich"
    }
}

module.exports = OSTRICH;
