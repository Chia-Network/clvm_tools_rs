mod classic;
mod compiler;
mod util;

use crate::classic::clvm_tools::log;

#[ctor::ctor]
fn init() {
    log::init();
}
