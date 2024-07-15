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

#[cfg(feature = "profiling")]
impl<'a> Drop for Profiler<'a> {
    fn drop(self: &mut Profiler<'a>) {
        if let Ok(report) = self.guard.report().build() {
            let file = fs::File::create(&self.filename).unwrap();
            let fg_res = report.flamegraph(file);
            if let Err(e) = fg_res {
                eprintln!("flamegraph failed: {e:?}");
            }
        };
    }
}

#[cfg(not(feature = "profiling"))]
impl Drop for Profiler {
    fn drop(self: &mut Profiler) {}
}

// Smoke test that just invokes the profiler.
#[test]
#[cfg(feature = "profiling")]
fn test_profiler() {
    let testfile = "test.svg";
    {
        let _ = Profiler::new(testfile);
        eprintln!("doing something");
    }
    #[cfg(feature = "profiling")]
    let _ = fs::metadata(testfile).expect("svg should have been written");
}
