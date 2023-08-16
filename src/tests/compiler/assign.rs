use crate::tests::classic::run::{do_basic_brun, do_basic_run};
use std::rc::Rc;

trait TestCompute {
    fn compute(&self, x: i64, y: i64) -> (i64, i64);
}

#[derive(Default, Clone)]
struct ComposedComputation {
    to_run: Vec<Rc<dyn TestCompute>>,
}
impl TestCompute for ComposedComputation {
    fn compute(&self, mut x: i64, mut y: i64) -> (i64, i64) {
        for entry in self.to_run.iter() {
            let (new_x, new_y) = entry.compute(x, y);
            x = new_x;
            y = new_y;
        }
        (x, y)
    }
}

struct XPlus1 {}
impl TestCompute for XPlus1 {
    fn compute(&self, x: i64, y: i64) -> (i64, i64) {
        (x + 1, y)
    }
}

struct YPlus1 {}
impl TestCompute for YPlus1 {
    fn compute(&self, x: i64, y: i64) -> (i64, i64) {
        (x, y + 1)
    }
}

struct FFunc {}
impl TestCompute for FFunc {
    fn compute(&self, x: i64, y: i64) -> (i64, i64) {
        let divxy = x / y;
        let modxy = x % y;
        (divxy, modxy)
    }
}

struct GFunc {}
impl TestCompute for GFunc {
    fn compute(&self, x: i64, _y: i64) -> (i64, i64) {
        let v = 1 + (3 * x);
        (v, v)
    }
}

struct HFunc {}
impl TestCompute for HFunc {
    fn compute(&self, x: i64, y: i64) -> (i64, i64) {
        let v = x * y;
        (v, v)
    }
}

struct IFunc {}
impl TestCompute for IFunc {
    fn compute(&self, x: i64, _y: i64) -> (i64, i64) {
        (x - 1, x * 2)
    }
}

struct UseTestFunction {
    name: String,
    args: usize,
    outputs: usize,
    text: String,
    compute: Rc<dyn TestCompute>,
}

struct AssignTestMatrix {
    functions: Vec<UseTestFunction>,
}

#[test]
#[ignore]
fn test_assign_matrix() {
    let inline_kwds = vec!["assign", "assign-lambda", "assign-inline"];
    let matrix = AssignTestMatrix {
        functions: vec![
            UseTestFunction {
                name: "F".to_string(),
                args: 2,
                outputs: 2,
                text: "(defun F (X Y) (divmod X Y))".to_string(),
                compute: Rc::new(FFunc {}),
            },
            UseTestFunction {
                name: "F-inline".to_string(),
                args: 2,
                outputs: 2,
                text: "(defun-inline F-inline (X Y) (divmod X Y))".to_string(),
                compute: Rc::new(FFunc {}),
            },
            UseTestFunction {
                name: "G".to_string(),
                args: 1,
                outputs: 1,
                text: "(defun G (X) (+ 1 (* 3 X)))".to_string(),
                compute: Rc::new(GFunc {}),
            },
            UseTestFunction {
                name: "G-inline".to_string(),
                args: 1,
                outputs: 1,
                text: "(defun-inline G-inline (X) (+ 1 (* 3 X)))".to_string(),
                compute: Rc::new(GFunc {}),
            },
            UseTestFunction {
                name: "H".to_string(),
                args: 2,
                outputs: 1,
                text: "(defun H (X Y) (* X Y))".to_string(),
                compute: Rc::new(HFunc {}),
            },
            UseTestFunction {
                name: "H-inline".to_string(),
                args: 2,
                outputs: 1,
                text: "(defun-inline H-inline (X Y) (* X Y))".to_string(),
                compute: Rc::new(HFunc {}),
            },
            UseTestFunction {
                name: "I".to_string(),
                args: 1,
                outputs: 2,
                text: "(defun I (X) (c (- X 1) (* X 2)))".to_string(),
                compute: Rc::new(IFunc {}),
            },
            UseTestFunction {
                name: "I-inline".to_string(),
                args: 1,
                outputs: 2,
                text: "(defun-inline I-inline (X) (c (- X 1) (* X 2)))".to_string(),
                compute: Rc::new(IFunc {}),
            },
        ],
    };

    // The program will take X, Y

    let mut starter_program = vec!["(mod (X Y) (include *standard-cl-21*) ".to_string()];
    for func in matrix.functions.iter() {
        starter_program.push(func.text.clone());
    }

    let assert_program_worked = |program: &[String], to_compute: &ComposedComputation| {
        let joined = program.join("\n").to_string();
        let compiled = do_basic_run(&vec!["run".to_string(), joined]);
        let executed = do_basic_brun(&vec![
            "brun".to_string(),
            "-n".to_string(),
            compiled,
            "(13 19)".to_string(),
        ]);
        let (ex, ey) = to_compute.compute(13, 19);
        let expected = do_basic_brun(&vec![
            "brun".to_string(),
            "-n".to_string(),
            format!("(1 . ({ex} . {ey}))"),
        ]);
        assert_eq!(expected, executed);
    };

    let finish_program = |program: &mut Vec<String>, main_or_function: usize, assign_expr: &str| {
        if main_or_function == 0 {
            program.push(assign_expr.to_string());
        } else {
            if main_or_function == 1 {
                program.push(format!("(defun Q (X Y) {})", assign_expr));
            } else {
                program.push(format!("(defun-inline Q (X Y) {})", assign_expr));
            }
            program.push("(Q X Y)".to_string());
        }
        program.push(")".to_string());
    };

    let test_triple_nesting =
        |to_compute: &ComposedComputation, main_or_function: usize, assign_expr_list: &[String]| {
            let assign_expr = assign_expr_list.join("\n").to_string();
            let mut program = starter_program.clone();
            finish_program(&mut program, main_or_function, &assign_expr);
            assert_program_worked(&program, &to_compute);
        };

    let test_third_level_nestings = |to_compute_x: &ComposedComputation,
                                     fourth_var: &str,
                                     y: &UseTestFunction,
                                     main_or_function: usize,
                                     assign_expr: &str,
                                     second_assign: &str,
                                     end_parens: &str| {
        // Put on a third level on the stack.
        for z in matrix.functions.iter() {
            let assign_call_z = if z.args == 1 {
                format!("({} V2)", z.name)
            } else {
                format!("({} V2 (+ 1 {fourth_var}))", z.name)
            };

            let (third_assign, sixth_var) = if z.outputs == 1 {
                (format!("V4 {assign_call_z}"), "V4")
            } else {
                (format!("(V4 . V5) {assign_call_z}"), "V5")
            };

            let final_expr = format!("(c V4 {sixth_var}))");
            let mut to_compute = to_compute_x.clone();
            to_compute.to_run.push(y.compute.clone());
            to_compute.to_run.push(Rc::new(YPlus1 {}));
            to_compute.to_run.push(z.compute.clone());

            // Try with z in the same assign.
            test_triple_nesting(
                &to_compute,
                main_or_function,
                &[
                    assign_expr.to_string(),
                    second_assign.to_string(),
                    third_assign.clone(),
                    final_expr.clone(),
                    end_parens.to_string(),
                ],
            );

            // Try with z nested.
            test_triple_nesting(
                &to_compute,
                main_or_function,
                &[
                    assign_expr.to_string(),
                    second_assign.to_string(),
                    "(assign".to_string(),
                    third_assign,
                    final_expr,
                    ")".to_string(),
                    end_parens.to_string(),
                ],
            );
        }
    };

    for x in matrix.functions.iter() {
        let main_expr = if x.args == 1 {
            format!("({} X)", x.name)
        } else {
            format!("({} X Y)", x.name)
        };

        // Depth 1.
        for inline_choice in inline_kwds.iter() {
            let mut to_compute_x = ComposedComputation::default();
            to_compute_x.to_run.push(x.compute.clone());
            for main_or_function in 0..=2 {
                let (assign_expr, second_var) = if x.outputs == 1 {
                    (format!("({inline_choice} V0 {main_expr}"), "V0")
                } else {
                    (format!("({inline_choice} (V0 . V1) {main_expr}"), "V1")
                };

                {
                    let mut program = starter_program.clone();
                    let finished_assign_expr =
                        vec![assign_expr.clone(), format!("(c V0 {second_var}))")]
                            .join("\n")
                            .to_string();
                    finish_program(&mut program, main_or_function, &finished_assign_expr);
                    assert_program_worked(&program, &to_compute_x);
                }

                // Second set of assignments.
                for y in matrix.functions.iter() {
                    // Use both arguments in one more function call.
                    let second_var = if x.outputs == 1 { "V0" } else { "V1" };
                    let assign_call_y = if y.args == 1 {
                        format!("({} V0)", y.name)
                    } else {
                        format!("({} V0 {second_var})", y.name)
                    };
                    let (second_assign, fourth_var) = if y.outputs == 1 {
                        (format!("V2 {assign_call_y}"), "V2")
                    } else {
                        (format!("(V2 . V3) {assign_call_y}"), "V3")
                    };

                    {
                        let assign_expr = vec![
                            assign_expr.clone(),
                            second_assign.clone(),
                            format!("(c V2 {fourth_var}))"),
                        ]
                        .join("\n")
                        .to_string();
                        let mut program = starter_program.clone();
                        let mut to_compute = to_compute_x.clone();
                        to_compute.to_run.push(y.compute.clone());
                        finish_program(&mut program, main_or_function, &assign_expr);
                        assert_program_worked(&program, &to_compute);
                    }

                    test_third_level_nestings(
                        &to_compute_x,
                        fourth_var,
                        y,
                        main_or_function,
                        &assign_expr,
                        &second_assign,
                        "",
                    );
                }

                // Nested
                for y in matrix.functions.iter() {
                    for inline_choice_y in inline_kwds.iter() {
                        // Use both arguments in one more function call.
                        let second_var = if x.outputs == 1 { "V0" } else { "V1" };
                        let assign_call_y = if y.args == 1 {
                            format!("({} V0)", y.name)
                        } else {
                            format!("({} V0 {second_var})", y.name)
                        };
                        let (second_assign, fourth_var) = if y.outputs == 1 {
                            (format!("({inline_choice_y} V2 {assign_call_y}"), "V2")
                        } else {
                            (
                                format!("({inline_choice_y} (V2 . V3) {assign_call_y}"),
                                "V3",
                            )
                        };

                        {
                            let assign_expr = vec![
                                assign_expr.clone(),
                                second_assign.clone(),
                                format!("(c V2 {fourth_var})))"),
                            ]
                            .join("\n")
                            .to_string();

                            let mut program = starter_program.clone();
                            let mut to_compute = to_compute_x.clone();
                            to_compute.to_run.push(y.compute.clone());
                            finish_program(&mut program, main_or_function, &assign_expr);
                            assert_program_worked(&program, &to_compute);
                        }

                        test_third_level_nestings(
                            &to_compute_x,
                            fourth_var,
                            y,
                            main_or_function,
                            &assign_expr,
                            &second_assign,
                            ")",
                        );
                    }
                }
            }
        }
    }
}
