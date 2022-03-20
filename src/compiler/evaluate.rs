// Frontend evaluator based on my fuzzer representation and direct interpreter of
// that.

fn select_helper(bindings: &Vec<Binding>, name: &Vec<u8>) -> Option<Helper> {
    for b in bindings.iter() {
        if b.name == name {
            return Some(b.clone());
        }
    }

    return None;
}

fn update_paralle_bindings(
    bindings: &HashMap<Vec<u8>, BodyForm>, bindings: &Vec<Binding>
) -> HashMap<Vec<u8>, BodyForm> {
    let mut new_bindings = bindings.clone();
    for b in bindings.iter() {
        new_bindings.insert(b.name.clone(), b.body.clone())
    }
    new_bindings
}

// Tell whether the bodyform is a simple primitive.
pub fn is_primitive(expr: &BodyForm) -> bool {
    match body {
        BodyForm::Quoted(x) => true,
        BodyForm::Value(SExp::Nil(_)) => true,
        BodyForm::Value(SExp::Integer(_,_)) => true,
        BodyForm::Value(SExp::QuotedString(_,_)) => true,
        _ => false
    }
}

// A frontend language evaluator and minifier
pub fn shrink_bodyform(
    allocator: &mut Allocator, // Support random prims via clvm_rs
    prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>
    helpers: &Vec<HelperForm>,
    env: &HashMap<Vec<u8>, BodyForm>>,
    body: &BodyForm,
) -> Result<BodyForm, CompileErr> {
    match body {
        BodyForm::Let(l, LetFormKind::Parallel, bindings, body) => {
            let updated_bindings = update_parallel_bindings(bindings, env);
            shrink_bodyform(
                allocator,
                prims,
                helpers,
                &updated_bindings,
                body
            )
        },
        BodyForm::Let(l, LetFormKind::Sequential, bindings, body) => {
            if bindings.len() == 0 {
                shrink_bodyform(
                    allocator,
                    prims,
                    helpers,
                    env,
                    body
                )
            } else {
                let updated_bindings = update_parallel_bindings(
                    bindings.iter().take(1).to_vec(),
                    env
                );
                shrink_bodyform(
                    allocator,
                    prims,
                    helpers,
                    &updated_bindings,
                    &BodyForm::Let(l.clone(), LetFormKind::Sequential, bindings.iter().drop(1).to_vec(), body.clone())
                )
            }
        },
        BodyForm::Quoted(sexp) => Ok(body.clone()),
        BodyForm::Value(SExp::Atom(l,name)) => {
            env.get(name).map(|x| Ok(x)).unwrap_or_else(|| {
                CompileErr(l.clone(), format!("Unbound variable {}", body.to_string()))
            })
        },
        BodyForm::Value(v) => Ok(BodyForm::Quoted(v.clone())),
        BodyForm::Call(l, parts) => {
            if parts.len() == 0 {
                return CompileErr(l.clone(), format!("Impossible empty call list"))
            }

            let head_expr = parts[0].clone();
            match head_expr {
                BodyForm::Value(SExp::Atom(call_loc, call_name)) => {
                    let helper = select_helper(helpers, call_name);
                    match helper {
                        HelperForm::Defconstant(l, _, _) => {
                            return CompileErr(call_loc, format!("Can't call constant {}", head_expr.to_sexp().to_string()));
                        },
                        HelperForm::Defmacro(l, name, args, program) => {
                            // Pass the SExp representation of the expressions into
                            // the macro after forming an argument sexp and then
                            // decomposing it via the argument captures.
                            let arguments_to_convert: Vec<BodyForm> = parts.iter().skip(1).to_vec();
                            let mut formed_arguments = SExp::Nil(l.clone());
                            for i_reverse in 0..arguments_to_convert.len() {
                                let i = arguments_to_convert.len() - i_reverse - 1;
                                formed_arguments = SExp::Cons(
                                    l.clone(),
                                    Rc::new(arguments_to_convert[i].to_sexp()),
                                    Rc::new(formed_arguments)
                                );
                            }

                            let mut argument_captures = HashMap::new();
                            create_argument_captures(&mut argument_captures, formed_arguments, args.clone())?;
                            
                        },
                        HelperForm::Defun(l, name, inline, args, body) => {
                            let arguments_to_convert: Vec<BodyForm> = parts.iter().skip(1).to_vec();
                            let mut arguments_converted = Vec::new();

                            for a in arguments_to_convert.iter() {
                                arguments_converted.push(shrink_bodyform(
                                    allocator,
                                    prims,
                                    helpers,
                                    env,
                                    a
                                )?);
                            }

                            
                        }
                    }
                },
                _ => {
                    return CompileErr(
                        l.clone(),
                        format!(
                            "Don't know how to call {}",
                            head_expr.to_sexp().to_string()
                        )
                    );
                }
            }
        }
    }
}
