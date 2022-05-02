import {readFileSync} from 'fs';
import {argv} from 'process';
import * as clvm_tools_rs from './build/clvm_tools_rs.js';

function run_program(program, args, symbols, overrides) {
    let runner = clvm_tools_rs.create_clvm_runner(program, args, symbols, overrides);
    if (runner.error) {
        console.log(runner.error);
        return;
    }

    var ended = null;

    do {
        var result = clvm_tools_rs.run_step(runner);
        if (result !== null) {
            if (result.Final !== undefined) {
                ended = result.Final;
                break;
            }
            if (result.Failure !== undefined) {
                ended = result.Failure;
                break;
            }
        }
    } while (ended === null);

    clvm_tools_rs.remove_clvm_runner(runner);
    return parseInt(ended);
}

var fact_hex = readFileSync('./tests/fact.clvm.hex').toString('utf8');
var fact_sym_txt = readFileSync('./tests/fact.sym').toString('utf8');
var fact_sym = JSON.parse(fact_sym_txt);

let value = run_program(fact_hex, [5], fact_sym, {
    "fact-base": (env) => {
        console.log('fact-base returning 99');
        return 99;
    }
});
if (value !== 11880) {
    throw new Error("Didn't wind up with 99 as the factorial base case");
}
