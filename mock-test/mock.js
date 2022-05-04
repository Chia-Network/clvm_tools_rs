import {readFileSync} from 'fs';
import {argv} from 'process';
import {bytestring, run_program} from './stepper';
import {compile, compose_run_function} from './build/clvm_tools_rs.js';

var fact_hex = readFileSync('./tests/fact.clvm.hex').toString('utf8');
var fact_sym_txt = readFileSync('./tests/fact.sym').toString('utf8');
var fact_sym = JSON.parse(fact_sym_txt);

function do_simple_run() {
    let value = run_program(fact_hex, [5], fact_sym, {
        "fact-base": (env) => {
            console.log('fact-base returning 99');
            return 99;
        }
    });
    if (value != 11880) {
        throw new Error("Didn't wind up with 99 as the factorial base case");
    }
}

function do_complex_run() {
    let pwcoin_src = readFileSync('./tests/pwcoin.cl').toString('utf8');
    let pwcoin = compile(pwcoin_src, 'pwcoin.cl', []);
    if (pwcoin.error) {
        throw new Error(pwcoin.error);
    }

    let value = run_program(pwcoin.hex, ["hello", bytestring("5f5767744f91c1c326d927a63d9b34fa7035c10e3eb838c44e3afe127c1b7675"), 2], pwcoin.symbols, {});
    if (value.length != 1) {
        throw new Error("Didn't receive the expected list");
    }
    let cond = value[0];
    if (cond[0] != 51) {
        throw new Error("Didn't get a create condition");
    }
    if (cond[2] != 2) {
        throw new Error("Didn't get 2 mojo");
    }

    let run_check_password = compose_run_function(
        pwcoin.hex,
        pwcoin.symbols,
        "check-password"
    );
    console.log(run_check_password);
    let not_right_password = run_program(
        run_check_password, ["not-right"], pwcoin.symbols, {}
    );
    if (not_right_password) {
        console.log(not_right_password);
        throw new Error("said right password but it was wrong");
    }

    let right_password = run_program(
        run_check_password, ["hello"], pwcoin.symbols, {}
    );
    if (!right_password) {
        console.log(right_password);
        throw new Error("said not right password but it was");
    }
}

do_simple_run();
do_complex_run();
