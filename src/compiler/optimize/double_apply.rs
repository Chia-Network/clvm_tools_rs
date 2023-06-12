use crate::compiler::sexp::{AtomValue, NodeSel, SExp, SelectNode, ThisNode};
use std::borrow::Borrow;
use std::rc::Rc;

// Turn:
//
// (a (q any) 1)
//
// into
//
// any
//
// I now realize this is exactly cons_q_a_optimizer from classic :-)
pub fn change_double_to_single_apply(sexp: Rc<SExp>) -> (bool, Rc<SExp>) {
    if let Ok(NodeSel::Cons(
        _,
        NodeSel::Cons(
            NodeSel::Cons(
                // quoted program
                _,
                inner_program,
            ),
            NodeSel::Cons(_, _),
        ),
    )) = NodeSel::Cons(
        AtomValue::Here(&[2]),
        NodeSel::Cons(
            NodeSel::Cons(
                // quoted program
                AtomValue::Here(&[1]),
                ThisNode::Here
            ),
            NodeSel::Cons(AtomValue::Here(&[1]), ThisNode::Here),
        ),
    )
    .select_nodes(sexp.clone())
    {
        return (true, inner_program);
    }

    (false, sexp)
}

pub fn remove_double_apply(sexp: Rc<SExp>) -> (bool, Rc<SExp>) {
    // Don't descend into quoted expressions.
    if let Ok(NodeSel::Cons(_, _)) =
        NodeSel::Cons(AtomValue::Here(&[1]), ThisNode::Here).select_nodes(sexp.clone())
    {
        return (false, sexp);
    }

    if let SExp::Cons(l, a, b) = sexp.borrow() {
        let (a_changed, new_a) = remove_double_apply(a.clone());
        let (b_changed, new_b) = remove_double_apply(b.clone());
        let (root_transformed, result) =
            change_double_to_single_apply(Rc::new(SExp::Cons(l.clone(), new_a, new_b)));
        (a_changed || b_changed || root_transformed, result)
    } else {
        (false, sexp)
    }
}
