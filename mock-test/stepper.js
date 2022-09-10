import * as clvm_tools_rs from './build/clvm_tools_rs.js';
import {hexlify, unhexlify} from 'binascii';

export function bytestring(s) {
    return unhexlify(s);
}

export function run_program(program, args, symbols, overrides) {
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

    let finished = clvm_tools_rs.final_value(runner);
    clvm_tools_rs.remove_clvm_runner(runner);
    return finished;
};
