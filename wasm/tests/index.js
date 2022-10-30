const fs = require("node:fs");
const path = require("node:path");
const wasm = require("../pkg/clvm_tools_wasm");

function unHexlify(str){
  let result = "";
  for (let i=0, l=str.length; i<l; i+=2) {
    result += String.fromCharCode(parseInt(str.substring(i, i+2), 16));
  }
  return result;
}

const fact_hex = fs.readFileSync(path.resolve(__dirname, "./test-data/fact.clvm.hex")).toString("utf8");
const fact_sym_txt = fs.readFileSync(path.resolve(__dirname, "./test-data/fact.sym")).toString("utf8");
const fact_sym = JSON.parse(fact_sym_txt);

function run_program(program, args, symbols, overrides) {
  let runner = wasm.create_clvm_runner(program, args, symbols, overrides);
  let ended = null;
  
  do {
    const result = wasm.run_step(runner);
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
  } while (true);
  
  let finished = wasm.final_value(runner);
  wasm.remove_clvm_runner(runner);
  return finished;
}

function do_simple_run() {
  const value = run_program(fact_hex, [5], fact_sym, {
    "fact-base": (env) => {
      console.log("fact-base returning 99");
      return 99;
    }
  });
  if (value !== 11880n) {
    throw new Error("Didn't wind up with 99 as the factorial base case");
  }
}

function do_complex_run() {
  let pwcoin_src = fs.readFileSync(path.resolve(__dirname, "./test-data/pwcoin.cl")).toString("utf8");
  let pwcoin = wasm.compile(pwcoin_src, "pwcoin.cl", []);
  if (pwcoin.error) {
    throw new Error(pwcoin.error);
  }
  
  const m = unHexlify("5f5767744f91c1c326d927a63d9b34fa7035c10e3eb838c44e3afe127c1b7675");
  const value = run_program(pwcoin.hex, ["hello", m, 2], pwcoin.symbols, {});
  if (value.length !== 1) {
    throw new Error("Didn't receive the expected list");
  }
  let cond = value[0];
  if (cond[0] !== 51n) {
    throw new Error("Didn't get a create condition");
  }
  if (cond[2] !== 2n) {
    throw new Error("Didn't get 2 mojo");
  }
  
  const run_check_password = wasm.compose_run_function(
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
