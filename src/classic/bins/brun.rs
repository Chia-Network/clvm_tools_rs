use std::env;
use clvm_tools_rs::classic::clvm_tools::cmds::brun;

fn main() {
    let args: Vec<String> = env::args().collect();
    brun(&args);
}
