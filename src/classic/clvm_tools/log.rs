use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

lazy_static! {
    pub static ref LOG_INIT: AtomicUsize = AtomicUsize::new(0);
}

pub fn init() {
    if LOG_INIT.fetch_add(1, Ordering::SeqCst) == 0 {
        env_logger::init();
    }
}
