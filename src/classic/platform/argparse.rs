use std::cmp::PartialEq;
use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::Record;
use crate::util::{
    index_of_match,
    skip_leading
};

#[derive(PartialEq)]
#[derive(Debug)]
pub enum TArgOptionAction {
    Store,
    StoreTrue,
    Append
}

#[derive(PartialEq)]
pub enum NArgsSpec {
    KleeneStar,
    Plus,
    Optional,
    Definite(usize)
}

#[derive(Clone)]
pub enum ArgumentValue {
    ArgString(String),
    ArgInt(i64),
    ArgBool(bool),
    ArgArray(Vec<ArgumentValue>)
}

pub trait ArgumentValueConv {
    fn convert(&self, s: &String) -> Result<ArgumentValue, String>;
}

struct EmptyConversion { }
impl ArgumentValueConv for EmptyConversion {
    fn convert(&self, s: &String) -> Result<ArgumentValue, String> {
        return Ok(ArgumentValue::ArgString(s.to_string()));
    }
}

struct IntConversion {
    helpMessager: fn() -> String
}

impl ArgumentValueConv for IntConversion {
    fn convert(&self, v: &String) -> Result<ArgumentValue, String> {
        match v.parse::<i64>() {
            Ok(n) => return Ok(ArgumentValue::ArgInt(n)),
            _ => {
                let usage = (self.helpMessager)();
                return Err(
                    format!("{}\n\nError: Invalid parameter: {}", usage, v)
                );
            }
        }
    }
}

pub struct Argument {
    action: TArgOptionAction,
    typeofarg: Rc<dyn ArgumentValueConv>,
    default: Option<ArgumentValue>,
    help: String,
    nargs: Option<NArgsSpec>
}

impl Argument {
    pub fn new() -> Self {
        return Argument {
            action: TArgOptionAction::Store,
            typeofarg: Rc::new(EmptyConversion {}),
            default: None,
            help: "".to_string(),
            nargs: None
        };
    }

    pub fn setAction(self, a: TArgOptionAction) -> Self {
        let mut s = self;
        s.action = a;
        return s;
    }
    pub fn setType(self, t: Rc<dyn ArgumentValueConv>) -> Self {
        let mut s = self;
        s.typeofarg = t;
        return s;
    }
    pub fn setDefault(self, v: ArgumentValue) -> Self {
        let mut s = self;
        s.default = Some(v);
        return s;
    }
    pub fn setHelp(self, h: String) -> Self {
        let mut s = self;
        s.help = h;
        return s;
    }
    pub fn setNArgs(self, n: NArgsSpec) -> Self {
        let mut s = self;
        s.nargs = Some(n);
        return s;
    }
}

pub struct Arg {
    names: Vec<String>,
    options: Argument
}

pub fn isOptional(arg: String) -> bool {
    return arg.starts_with("-");
}

pub struct TArgumentParserProps {
    pub description: String,
    pub prog: String
}

pub struct ArgumentParser {
    prog: String,
    desc: String,
    positional_args: Vec<Arg>,
    optional_args: Vec<Arg>
}

impl ArgumentParser {
    pub fn new(props: Option<TArgumentParserProps>) -> ArgumentParser {
        let mut start = ArgumentParser {
            prog: "prog".to_string(),
            desc: "".to_string(),
            positional_args: vec!(),
            optional_args: vec!()
        };

        match props {
            None => { },
            Some(props) => {
                start.add_argument(
                    vec!("-h".to_string(), "--help".to_string()),
                    Argument::new().
                        setHelp("Show help message".to_string()).
                        setAction(TArgOptionAction::StoreTrue)
                );
            }
        }

        return start;
    }

    pub fn add_argument(&mut self, argName: Vec<String>, options: Argument) {
        self.positional_args.push(Arg { names: argName, options: options });
    }

    pub fn parse_args(&mut self, args: &Vec<String>) -> Result<HashMap<String, ArgumentValue>, String> {
        let normalizedArgs = self.normalizeArgs(args);
        let mut params: Record<String, ArgumentValue> = HashMap::new();

        // Set default value
        for k in 0..self.optional_args.len()-1 {
            let optional_arg_k = &self.optional_args[k];
            let defaultValue = &optional_arg_k.options.default;

            match defaultValue {
                Some(dv) => {
                    match self.getOptionalArgName(optional_arg_k) {
                        Ok(name) => {
                            params.insert(name, dv.clone());
                        },
                        Err(e) => { return Err(e); }
                    }
                },
                _ => {}
            }
        }

        let mut input_positional_args: Vec<String> = vec!();
        let mut ioff = 0;

        for i in 0..normalizedArgs.len()-1 {
            let arg = &normalizedArgs[i + ioff];

            // positional argument
            if !isOptional(arg.to_string()) {
                input_positional_args.push(arg.clone());
                continue;
            }

            let optional_arg_idx =
                index_of_match(
                    |a: &Arg| index_of_match(|a: &String| a == arg, &a.names) >= 0,
                    &self.optional_args
                );

            if optional_arg_idx < 0 {
                let usage = self.compileHelpMessages();
                return Err(format!("{}\n\nError: Unknown option: {}", usage, arg));
            }

            let optional_arg = &self.optional_args[optional_arg_idx as usize];
            let mut name : String = "".to_string();

            match self.getOptionalArgName(&optional_arg) {
                Ok(n) => { name = n; },
                Err(e) => { return Err(e); }
            }

            if optional_arg.options.action == TArgOptionAction::StoreTrue {
                params.insert(name, ArgumentValue::ArgBool(true));
                continue;
            }

            let converter =
                self.getConverter(Some(optional_arg.options.typeofarg.clone()));

            ioff += 1;

            let value = &normalizedArgs[i];
            if value == "" && optional_arg.options.default.is_none() {
                let usage = self.compileHelpMessages();
                return Err(format!("{}\n\nError: {} requires a value", usage, name));
            }
            if optional_arg.options.action == TArgOptionAction::Store {
                match converter.convert(&value) {
                    Ok(c) => {
                        params.insert(name, c);
                    },
                    _ => {
                        match &optional_arg.options.default {
                            Some(v) => {
                                params.insert(name, v.clone());
                            },
                            _ => { }
                        }
                    }
                }
            }
            else if optional_arg.options.action == TArgOptionAction::Append {
                match params.get(&name) {
                    Some(ArgumentValue::ArgArray(l)) => {
                        match converter.convert(&value) {
                            Ok(v) => {
                                let mut lcopy = l.clone();
                                lcopy.push(v);
                                params.insert(name, ArgumentValue::ArgArray(lcopy));
                            },
                            _ => {
                                match &optional_arg.options.default {
                                    Some(v) => {
                                        let mut lcopy = l.clone();
                                        lcopy.push(v.clone());
                                        params.insert(name, ArgumentValue::ArgArray(lcopy));
                                    },
                                    None => { }
                                }
                            }
                        }
                    },
                    _ => {
                        match converter.convert(&value) {
                            Ok(v) => {
                                params.insert(name, ArgumentValue::ArgArray(vec!(v)));
                            },
                            _ => {
                                match &optional_arg.options.default {
                                    Some(v) => {
                                        params.insert(
                                            name,
                                            ArgumentValue::ArgArray(vec!(v.clone()))
                                        );
                                    },
                                    None => { }
                                }
                            }
                        }
                    }
                }
            } else {
                let usage = self.compileHelpMessages();
                return Err(format!("{}\n\nError: Unknown action: {:?}", usage, optional_arg.options.action));
            }
        }

        let mut i = 0;
        for k in 0..self.positional_args.len()-1 {
            let positional_arg_k = &self.positional_args[k];
            let mut input_arg = &input_positional_args[i];

            let name = &positional_arg_k.names[0];
            let nargs = &positional_arg_k.options.nargs;
            let converter = self.getConverter(Some(positional_arg_k.options.typeofarg.clone()));

            match nargs {
                None => {
                    match converter.convert(&input_arg) {
                        Ok(v) => {
                            params.insert(name.to_string(), v);
                            i += 1;
                        },
                        _ => {}
                    }
                },
                Some(NArgsSpec::Definite(nargs)) => {
                    for j in 0..nargs-1 {
                        if i >= input_positional_args.len() {
                            let usage = self.compileHelpMessages();
                            return Err(format!("{}\n\nError: Requires {} positional arguments but got {}", usage, nargs, i));
                        }

                        let input_arg = &input_positional_args[i];
                        match params.get(name) {
                            Some(ArgumentValue::ArgArray(l)) => {
                                match converter.convert(&input_arg) {
                                    Ok(v) => {
                                        let mut lcopy = l.clone();
                                        lcopy.push(v);
                                        params.insert(name.to_string(), ArgumentValue::ArgArray(lcopy));
                                    },
                                    _ => {}
                                }
                            },
                            _ => {
                                match converter.convert(&input_arg) {
                                    Ok(v) => { params.insert(name.to_string(), ArgumentValue::ArgArray(vec!(v))); },
                                    _ => {}
                                }
                            },
                        }
                        i += 1;
                    }
                },
                Some(Optional) => {
                    if i >= input_positional_args.len() {
                        match &positional_arg_k.options.default {
                            None => {
                                match converter.convert(&"".to_string()) {
                                    Ok(v) => { params.insert(name.to_string(), v); },
                                    _ => { }
                                }
                            },
                            Some(l) => {
                                match converter.convert(&"".to_string()) {
                                    Ok(v) => { params.insert(name.to_string(), v); },
                                    _ => { },
                                }
                            }
                        }

                        i += 1;
                    } else {
                        match converter.convert(&input_arg) {
                            Ok(v) => { params.insert(name.to_string(), v); },
                            _ => { }
                        }

                        i += 1;
                    }
                }
                /*
                
                _ => {
                    if i >= input_positional_args.len() {
                        if nargs == &Some(NArgsSpec::Plus) {
                            let usage = self.compileHelpMessages();
                            return Err(format!("{}\n\nError: The following arguments are required: {}", usage, name));
                        }

                        params.insert(name.to_string(), ArgumentValue::ArgArray(vec!()));

                        i += 1;
                        continue;
                    }

                    for i in 0..input_positional_args.len() {
                        input_arg = &input_positional_args[i];
                        match params.get(name) {
                            Some(ArgumentValue::ArgArray(l)) => {
                                match converter.convert(&input_arg) {
                                    Ok(v) => {
                                        let mut lcopy = l.clone();
                                        lcopy.push(v);
                                        params.insert(name.to_string(), ArgumentValue::ArgArray(lcopy));
                                    },
                                    _ => { },
                                }
                            },
                            _ => {
                                match converter.convert(&input_arg) {
                                    Ok(v) => {
                                        params.insert(name.to_string(), ArgumentValue::ArgArray(vec!(v)));
                                    },
                                    _ => { }
                                }
                            },
                        }
                    }
                }
*/
            }
        }

        match params.get(&"help".to_string()) {
            Some(_) => {
                let usage = self.compileHelpMessages();
                return Err(usage);
            },
            _ => { }
        }

        return Ok(params);
    }

    fn compileHelpMessages(&self) -> String {
        let iterator = |a: &Arg| {
            let mut msg = " ".to_string() + &a.names.join(", ");
            let default_value =
                match &a.options.default {
                    Some(ArgumentValue::ArgString(s)) => s.to_string(),
                    _ => "".to_string()
                };

            if a.options.help != "" {
                msg += &("  ".to_string() + &a.options.help);
                msg = msg.replace("%(prog)", &self.prog);
                msg = msg.replace("%(default)", &default_value);
            }
            return msg;
        };

        let mut arg_conversions = vec!();

        for arg in &self.optional_args {
            arg_conversions.push(format!("[{}]", arg.names[0]));
        }

        let mut messages = vec!(
            format!("usage: {}, {}", self.prog, arg_conversions.join(" "))
        );

        if self.positional_args.len() > 0 {
            messages.push("".to_string());
            messages.push("positional arguments:".to_string());
            for a in &self.positional_args {
                messages.push(iterator(a.clone()));
            }
        }
        if self.optional_args.len() > 0 {
            messages.push("".to_string());
            messages.push("optional arguments:".to_string());
            for a in &self.optional_args {
                messages.push(iterator(a.clone()));
            }
        }

        return messages.join("\n");
    }

    /**
     * Separate short form argument which doesn't have space character between name and value.
     * For example, turn:
     *   "-x1" => ["-x", "1"]
     *   "-x 1" => ["-x", "1"]
     *   "-xxxxx" => ["-x", "xxxx"]
     * @param args - arguments passed
     */
    pub fn normalizeArgs(&self, args: &Vec<String>) -> Vec<String> {
        if self.optional_args.len() < 1 {
            return args.to_vec();
        }

        let mut norm: Vec<String> = vec!();

        for i in 0..args.len()-1 {
            let mut optionalArgWithoutSpaceFound = false;
            let arg = &args[i];

            // Only short form args like '-x' are targets.
            if arg.starts_with("-") &&
                !arg.starts_with("--") {
                norm.push(arg.to_string());
                continue;
            }

            for k in 0..self.optional_args.len()-1 {
                let index =
                    index_of_match(|n: &String| {
                        return n.starts_with(&"-".to_string()) &&
                            !n.starts_with(&"--".to_string()) &&
                            n != arg && arg.starts_with(n);
                    }, &self.optional_args[k].names);

                if index < 0 {
                    continue;
                }

                let name = &self.optional_args[k].names[index as usize];
                let index2 =
                    match arg.find(name) {
                        Some(i) => i,
                        _ => 0
                    } + name.len();
                let value = &arg[index2..].to_string();

                norm.push(name.to_string());
                norm.push(value.to_string());
                optionalArgWithoutSpaceFound = true;
                break;
            }

            if !optionalArgWithoutSpaceFound {
                norm.push(arg.to_string());
            }
        }

        return norm;
    }

    pub fn getOptionalArgName(&self, arg: &Arg) -> Result<String,String> {
        let names = &arg.names;
        let doubleHyphenArgIndex =
            index_of_match(|n: &String| n.starts_with("--"), &names);

        if doubleHyphenArgIndex > -1 {
            let name = &names[doubleHyphenArgIndex as usize];
            let first_non_dash = skip_leading(&name, "-").replace("-", "_");
            return Ok(first_non_dash);
        }

        let singleHyphenArgIndex =
            index_of_match(
                |n: &String|
                n.starts_with("-") &&
                    !n.starts_with("--"),
                &names
            );
        if singleHyphenArgIndex > -1 {
            let name = &names[singleHyphenArgIndex as usize];
            let first_non_dash = skip_leading(&name, "-").replace("-", "_");
            return Ok(first_non_dash);
        }
        return Err("Invalid argument name".to_string());
    }

    fn getConverter(&self, typeofarg: Option<Rc<dyn ArgumentValueConv>>) -> Rc<dyn ArgumentValueConv> {
        match typeofarg {
            None => return Rc::new(EmptyConversion {}),
            Some(ty) => return ty
        }
    }
}

