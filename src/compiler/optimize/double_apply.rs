use std::borrow::Borrow;
use std::rc::Rc;
use crate::compiler::prims::primapply;
use crate::compiler::sexp::{AtomValue, NodeSel, SelectNode, SExp, ThisNode};

// Turn:
//
// (a (q 2 X Y) 1)
//
// into
//
// (a X Y)
pub fn change_double_to_single_apply(
    sexp: Rc<SExp>,
) -> (bool, Rc<SExp>) {
    eprintln!("check double apply {sexp}");
    if let Ok(NodeSel::Cons(
        a_loc,
        NodeSel::Cons(
            NodeSel::Cons( // quoted program
                _,
                NodeSel::Cons(
                    _,
                    NodeSel::Cons(
                        inner_program,
                        NodeSel::Cons(
                            inner_env,
                            _
                        )
                    )
                )
            ),
            NodeSel::Cons(
                _,
                _
            )
        )
    )) = NodeSel::Cons(
        AtomValue::Here(&[2]),
        NodeSel::Cons(
            NodeSel::Cons( // quoted program
                AtomValue::Here(&[1]),
                NodeSel::Cons(
                    AtomValue::Here(&[2]),
                    NodeSel::Cons(
                        ThisNode::Here, // inner program
                        NodeSel::Cons(
                            ThisNode::Here, // inner env
                            ThisNode::Here,
                        )
                    )
                )
            ),
            NodeSel::Cons(
                AtomValue::Here(&[1]),
                ThisNode::Here,
            )
        )
    ).select_nodes(sexp.clone()) {
        eprintln!("{sexp} is double apply");
        return (true, Rc::new(primapply(a_loc.clone(), inner_program, inner_env)));
    }

    (false, sexp)
}

pub fn remove_double_apply(
    sexp: Rc<SExp>
) -> (bool, Rc<SExp>) {
    eprintln!("remove_double_apply {sexp}");
    if let SExp::Cons(l, a, b) = sexp.borrow() {
        let (a_changed, new_a) = remove_double_apply(a.clone());
        let (b_changed, new_b) = remove_double_apply(b.clone());
        let (root_transformed, result) = change_double_to_single_apply(Rc::new(SExp::Cons(l.clone(), new_a, new_b)));
        (a_changed || b_changed || root_transformed, result)
    } else {
        (false, sexp)
    }
}
