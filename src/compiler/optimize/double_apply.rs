use crate::compiler::prims::primquote;
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
                ThisNode::Here,
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

fn change_apply_double_quote(sexp: Rc<SExp>) -> (bool, Rc<SExp>) {
    if let Ok(NodeSel::Cons(
        _, // apply
        NodeSel::Cons(
            NodeSel::Cons(
                _, // q
                NodeSel::Cons(
                    _, // 1
                    body,
                ),
            ),
            _,
        ),
    )) = NodeSel::Cons(
        AtomValue::Here(&[2]),
        NodeSel::Cons(
            NodeSel::Cons(
                AtomValue::Here(&[1]),
                NodeSel::Cons(AtomValue::Here(&[1]), ThisNode::Here),
            ),
            ThisNode::Here,
        ),
    )
    .select_nodes(sexp.clone())
    {
        return (true, Rc::new(primquote(body.loc(), body.clone())));
    }

    (false, sexp)
}

// Try to lift op out of apply.  We should take this optimization only if we've
// reproduced the environment one or zero times after optimizing the children.
// fn change_apply_op_outside(
//     sexp: Rc<SExp>
// ) -> (bool, Rc<SExp>) {
//     if let Ok(NodeSel::Cons(
//         _, // apply
//         NodeSel::Cons(
//             NodeSel::Cons(
//                 _, // quote
//                 NodeSel::Cons(
//                     op, // op
//                     args, // args (tail)
//                 )
//             ),
//             NodeSel::Cons(
//                 env,
//                 _
//             )
//         )
//     )) = NodeSel::Cons(
//         AtomValue::Here(&[2]), // apply
//         NodeSel::Cons(
//             NodeSel::Cons(
//                 AtomValue::Here(&[1]), // quote
//                 NodeSel::Cons(
//                     AtomValue::Here(()), // op
//                     ThisNode::Here // args (tail)
//                 )
//             ),
//             NodeSel::Cons(
//                 ThisNode::Here,
//                 ThisNode::Here
//             )
//         )
//     ).select_nodes(sexp.clone()) {
//         // No quote.
//         if op.1 == vec![1] || op.1 == vec![b'q'] {
//             return (false, sexp);
//         }

//         eprintln!("sexp {sexp} got op {} args {args} env {env}", decode_string(&op.1));
//         let args_list =
//             if let Some(alist) = args.proper_list() {
//                 alist
//             } else {
//                 return (false, sexp);
//             };

//         let applied_ops: Vec<Rc<SExp>> =
//             args_list.into_iter().map(|a| {
//                 let child = Rc::new(primapply(a.loc(), Rc::new(primquote(a.loc(), Rc::new(a.clone()))), env.clone()));
//                 let (_, opt_child) = remove_double_apply(child, true);
//                 opt_child
//             }).collect();

//         let op_outside = Rc::new(SExp::Cons(
//             sexp.loc(),
//             Rc::new(SExp::Atom(op.0.clone(), op.1.clone())),
//             Rc::new(enlist(sexp.loc(), &applied_ops))
//         ));
//         eprintln!("op outside {op_outside}");
//         todo!();

//         return (true, op_outside);
//     }

//     (false, sexp)
// }

// Recognize some optimizations:
//
// specific: (a (q 1 . x) _) => (q . x)
// classic optimizer: (a (op SEXP) ENV) => (op (a SEXP ENV)) <- wip
// classic optimizer: (a (q SEXP) 1) => SEXP
pub fn remove_double_apply(mut sexp: Rc<SExp>, spine: bool) -> (bool, Rc<SExp>) {
    // Don't descend into quoted expressions.
    if spine {
        if let Ok(NodeSel::Cons(_, _)) =
            NodeSel::Cons(AtomValue::Here(&[1]), ThisNode::Here).select_nodes(sexp.clone())
        {
            return (false, sexp);
        }
    }

    let mut any_transformation = true;
    let mut was_transformed = false;

    while any_transformation {
        if let SExp::Cons(l, a, b) = sexp.borrow() {
            // These transformations play on each other but finalize together.
            let (a_changed, new_a) = remove_double_apply(a.clone(), true);
            let (b_changed, new_b) = remove_double_apply(b.clone(), false);

            let result = Rc::new(SExp::Cons(l.clone(), new_a, new_b));
            if spine {
                let (root_transformed_dq, result_dq) = change_apply_double_quote(result);
                let (root_transformed_unapply, result_end) =
                    change_double_to_single_apply(result_dq);

                any_transformation =
                    a_changed || b_changed || root_transformed_dq || root_transformed_unapply;
                was_transformed |= any_transformation;
                sexp = result_end;
            } else {
                any_transformation = a_changed || b_changed;
                was_transformed |= any_transformation;
                sexp = result;
            }
        } else {
            break;
        }
    }

    (was_transformed, sexp)
}
