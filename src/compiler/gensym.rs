use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

lazy_static! {
    pub static ref argname_ctr: AtomicUsize = {
        return AtomicUsize::new(0);
    };
}

pub fn gensym(name: String) -> String {
    let count = argname_ctr.fetch_add(1, Ordering::SeqCst);
    return format!("{}_$_{}", name, count+1);
}
