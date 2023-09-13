use crate::util::toposort;
use std::collections::HashSet;

#[derive(Debug, Clone)]
struct TopoSortCheckItem {
    needs: HashSet<String>,
    has: HashSet<String>,
}

impl TopoSortCheckItem {
    pub fn new(needs_s: &[&str], has_s: &[&str]) -> Self {
        let mut needs: HashSet<String> = HashSet::new();
        let mut has: HashSet<String> = HashSet::new();
        for n in needs_s.iter() {
            needs.insert(n.to_string());
        }
        for h in has_s.iter() {
            has.insert(h.to_string());
        }
        TopoSortCheckItem { needs, has }
    }
}

// Given
//
// A B -> X
// X Y -> Z
// A W -> Y
// [] -> A
// [] -> B
// B -> W
//
// We should get something like this:
//
// [] -> A
// [] -> B
// B -> W
// A B -> X
// A W -> Y
// X Y -> Z
//
#[test]
fn test_topo_sort_0() {
    let t = |n, h| TopoSortCheckItem::new(n, h);
    let items = vec![
        t(&["A", "B"], &["X"]),
        t(&["X", "Y"], &["Z"]),
        t(&["A", "W"], &["Y"]),
        t(&[], &["A"]),
        t(&[], &["B"]),
        t(&["B"], &["W"]),
    ];
    let result = toposort(
        &items,
        true,
        |_p, n: &TopoSortCheckItem| Ok(n.needs.clone()),
        |h| h.has.clone(),
    )
    .expect("no deadlocks in this data");

    for (i, item) in result.iter().enumerate() {
        let have_item = &items[item.index];
        for j in 0..i {
            let item_to_check = &result[j];
            let item_to_check_for_dependencies_on_have = &items[item_to_check.index];
            // item_to_check_for_dependencies is an item occurring prior to
            // have_item in the sorted output.
            // If its 'needs' has anything in have_item's 'has', then we failed.
            let mut intersection = item_to_check_for_dependencies_on_have
                .needs
                .intersection(&have_item.has);
            assert!(intersection.next().is_none());
        }
    }
}

#[test]
fn test_topo_sort_1() {
    let t = |n, h| TopoSortCheckItem::new(n, h);
    let items = vec![
        t(&["A", "B"], &["X"]),
        t(&["X", "Y"], &["Z"]),
        t(&["A", "W"], &["Y"]),
        t(&[], &["A"]),
        t(&["Z"], &["B"]),
        t(&["B"], &["W"]),
    ];
    let result = toposort(
        &items,
        true,
        |_p, n: &TopoSortCheckItem| Ok(n.needs.clone()),
        |h| h.has.clone(),
    );

    assert!(result.is_err());
}
