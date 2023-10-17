#[cfg(feature = "profiling")]
use pprof::ProfilerGuard;
#[cfg(feature = "profiling")]
use std::fs;

#[cfg(feature = "profiling")]
pub struct Profiler<'a> {
    filename: String,
    guard: ProfilerGuard<'a>,
}

#[cfg(not(feature = "profiling"))]
pub struct Profiler {}

#[cfg(feature = "profiling")]
impl<'a> Profiler<'a> {
    pub fn new(filename: &str) -> Self {
        Profiler {
            filename: filename.to_string(),
            guard: pprof::ProfilerGuardBuilder::default()
                .frequency(100)
                .blocklist(&["libc", "libgcc", "pthread", "vdso"])
                .build()
                .unwrap(),
        }
    }
}

#[cfg(not(feature = "profiling"))]
impl Profiler {
    pub fn new(_filename: &str) -> Self {
        Profiler {}
    }
}

#[cfg(feature = "profiling")]
impl<'a> Drop for Profiler<'a> {
    fn drop(self: &mut Profiler<'a>) {
        if let Ok(report) = self.guard.report().build() {
            let file = fs::File::create(&self.filename).unwrap();
            report.flamegraph(file).unwrap();
        };
    }
}

#[cfg(not(feature = "profiling"))]
impl Drop for Profiler {
    fn drop(self: &mut Profiler) {}
}
