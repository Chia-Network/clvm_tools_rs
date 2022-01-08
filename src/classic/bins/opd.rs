use clvm_tools_rs::classic::clvm_tools::cmds::opd;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    opd(&args);
}
