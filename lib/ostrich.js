const child_process = require("child_process");
const { SMTSolver } = require("./smt");

class OSTRICH extends SMTSolver {
    constructor(solverPath, logic) {
        //huzi add
        var ostrichJarPath = "";
        if(process.env.OS !== undefined && process.env.OS === 'Windows_NT'){
            // windows
            ostrichJarPath = "E:/philipp/ostrich/target/scala-2.11/ostrich-assembly-1.0.jar";
        }else{
            // linux
            ostrichJarPath = "/mnt/e/philipp/ostrich/target/scala-2.11/ostrich-assembly-1.0.jar"
            // ostrichJarPath = "/home/hudh/hudh/time_test/ostrich-assembly-1.0.jar";
        }
        const args = [
            "-jar",
            ostrichJarPath,
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
