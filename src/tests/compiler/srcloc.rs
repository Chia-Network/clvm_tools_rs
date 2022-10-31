use crate::compiler::srcloc::Srcloc;

// _ is the start to end range.
// . is the target range.
// X is an overlap.
// no _.
#[test]
fn test_overlap_1() {
    let start = Srcloc::start(&"*test*");
    let next = Srcloc::start(&"*test*").advance(b' ');
    assert!(!start.overlap(&next));
    assert!(!next.overlap(&start));
}

// no ._
#[test]
fn test_overlap_2() {
    let start = Srcloc::start(&"*test*").advance(b' ');
    let next = Srcloc::start(&"*test*");
    assert!(!start.overlap(&next));
    assert!(!next.overlap(&start));
}

// yes _X_
#[test]
fn test_overlap_3() {
    let start = Srcloc::start(&"*test*");
    let mid = start.advance(b' ');
    let end = start.ext(&mid.advance(b' '));
    assert!(end.overlap(&mid));
    assert!(mid.overlap(&end));
}

// no
// _
// .
#[test]
fn test_overlap_4() {
    let start = Srcloc::start(&"*test*");
    let next = start.advance(b'\n');
    assert!(!next.overlap(&start));
    assert!(!start.overlap(&next));
}

// yes
// _
// X
// _
#[test]
fn test_overlap_5() {
    let start = Srcloc::start(&"*test*");
    let mid = start.advance(b'\n');
    let end = start.ext(&mid.advance(b'\n'));
    assert!(end.overlap(&mid));
    assert!(mid.overlap(&end));
}

// yes
//
//     __XX
// .
#[test]
fn test_overlap_6() {
    let mut start = Srcloc::start(&"*test*").advance(b'\n');
    for _ in 0..4 {
        start = start.advance(b' ');
    }
    let mut end = start.clone();
    for _ in 0..2 {
        end = end.advance(b' ');
    }
    let mut overlapping = end.clone();
    for _ in 0..2 {
        end = end.advance(b' ');
    }
    overlapping = overlapping.ext(&overlapping.advance(b'\n').advance(b' '));
    start = start.ext(&end);
    assert!(start.overlap(&overlapping));
    assert!(overlapping.overlap(&start));
}
