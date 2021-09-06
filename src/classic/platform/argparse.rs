use std::collections::HashMap;

pub enum TArgOptionAction {
    Store,
    StoreTrue,
    Append
}

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
    ArgBool(bool)
}

pub trait ArgumentValueConv {
    fn convert(&self, s: &String) -> ArgumentValue;
}

struct EmptyConversion { }
impl ArgumentValueConv for EmptyConversion {
    fn convert(&self, s: &String) -> ArgumentValue {
        return ArgumentValue::ArgString(s.to_string());
    }
}

pub struct Argument {
    action: TArgOptionAction,
    typeofarg: Box<ArgumentValueConv>,
    default: Option<ArgumentValue>,
    help: String,
    nargs: NArgsSpec
}

impl Argument {
    pub fn new() -> Self {
        return Argument {
            action: TArgOptionAction::Store,
            typeofarg: Box::new(EmptyConversion {}),
            default: None,
            help: "".to_string(),
            nargs: NArgsSpec::KleeneStar
        };
    }

    pub fn setAction(self, a: TArgOptionAction) -> Self {
        let mut s = self;
        s.action = a;
        return s;
    }
    pub fn setType(self, t: Box<ArgumentValueConv>) -> Self {
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
        s.nargs = n;
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

    pub fn parse_args(&mut self, args: &Vec<String>) -> HashMap<String, Vec<ArgumentValue>> {
        // XXX
        return HashMap::new();
    }

//     const normalizedArgs = this.normalizeArgs(args);
//     const params: Record<string, unknown> = {};
    
//     // Set default value
//     for(let k=0;k<this._optional_args.length;k++){
//       const optional_arg_k = this._optional_args[k];
//       const defaultValue = optional_arg_k.options.default;
//       if(typeof defaultValue === "undefined"){
//         continue;
//       }
  
//       const name = this._getOptionalArgName(optional_arg_k);
//       params[name] = defaultValue;
//     }
    
//     const input_positional_args: string[] = [];
//     for(let i=0;i<normalizedArgs.length;i++){
//       const arg = normalizedArgs[i];
      
//       // positional argument
//       if(!isOptional(arg)){
//         input_positional_args.push(arg);
//         continue;
//       }
      
//       const optional_arg = this._optional_args.find(a => a.names.includes(arg));
//       if(!optional_arg){
//         const usage = this.compileHelpMessages();
//         throw `${usage}\n\nError: Unknown option: ${arg}`;
//       }
  
//       const name = this._getOptionalArgName(optional_arg);
//       if(optional_arg.options.action === "store_true"){
//         params[name] = true;
//         continue;
//       }
  
//       const converter = this._getConverter(optional_arg.options.type);
  
//       ++i;
//       const value = normalizedArgs[i];
//       if(!value && !optional_arg.options.default){
//         const usage = this.compileHelpMessages();
//         throw `${usage}\n\nError: ${name} requires a value`;
//       }
//       if(!optional_arg.options.action || optional_arg.options.action === "store"){
//         params[name] = converter(value) || optional_arg.options.default;
//       }
//       else if(optional_arg.options.action === "append"){
//         const param_value = (params[name] || []) as unknown[];
//         params[name] = param_value.concat(converter(value) || optional_arg.options.default);
//       }
//       else{
//         const usage = this.compileHelpMessages();
//         throw `${usage}\n\nError: Unknown action: ${optional_arg.options.action}`;
//       }
//     }
    
//     let i = 0;
//     for(let k=0;k<this._positional_args.length;k++){
//       const positional_arg_k = this._positional_args[k];
//       let input_arg = input_positional_args[i];
  
//       const name = positional_arg_k.names[0];
//       const nargs = positional_arg_k.options.nargs;
//       const converter = this._getConverter(positional_arg_k.options.type);
  
//       if(typeof nargs === "undefined"){
//         params[name] = converter(input_arg);
//         i++;
//       }
//       else if(typeof nargs === "number"){
//         for(let j=0;j<nargs;j++){
//           if(i >= input_positional_args.length){
//             const usage = this.compileHelpMessages();
//             throw `${usage}\n\nError: Requires ${nargs} positional arguments but got ${i}`;
//           }
//           input_arg = input_positional_args[i];
//           const param_value = (params[name] || []) as unknown[];
//           params[name] = param_value.concat(converter(input_arg));
//           i++;
//         }
//       }
//       else if(nargs === "?"){
//         if(i >= input_positional_args.length){
//           if(typeof positional_arg_k.options.default === "undefined"){
//             params[name] = converter("");
//             i++;
//             continue;
//           }
//           params[name] = positional_arg_k.options.default;
//           i++;
//         }
//         else{
//           params[name] = converter(input_arg);
//           i++;
//         }
//       }
//       else if(nargs === "*" || nargs === "+"){
//         if(i >= input_positional_args.length){
//           if(nargs === "+"){
//             const usage = this.compileHelpMessages();
//             throw `${usage}\n\nError: The following arguments are required: ${name}`;
//           }
//           params[name] = [];
//           i++;
//           continue;
//         }
        
//         for(;i<input_positional_args.length;i++){
//           input_arg = input_positional_args[i];
//           const param_value = (params[name] || []) as unknown[];
//           params[name] = param_value.concat(converter(input_arg));
//         }
//       }
//       else{
//         throw `Unknown nargs: ${nargs}. It is a program bug. Contact a developer and report this error.`;
//       }
//     }
    
//     if(params["help"]){
//       const usage = this.compileHelpMessages();
//       throw `${usage}`;
//     }
    
//     return params;
//   }
}

//   protected _getConverter(type?: "str"|"int"|((v: string) => unknown)){
//     if(!type || type === "str"){ // string
//       return (v: string) => v;
//     }
//     else if(type === "int"){
//       return (v: string) => {
//         const n = +v;
//         if(isNaN(n) || !isFinite(n)){
//           const usage = this.compileHelpMessages();
//           throw `${usage}\n\nError: Invalid parameter: ${v}`;
//         }
//         return n;
//       };
//     }
//     else if(typeof type === "function"){
//       return type as (v: string) => unknown;
//     }
//     else{
//       const usage = this.compileHelpMessages();
//       throw `${usage}\n\nError: Unknown type: ${type}`;
//     }
//   }
  
//   protected _getOptionalArgName(arg: Arg){
//     const names = arg.names;
//     const doubleHyphenArgIndex = names.findIndex(n => /^[-]{2}/.test(n));
//     if(doubleHyphenArgIndex > -1){
//       const name = names[doubleHyphenArgIndex];
//       return name.replace(/^[-]+/, "").replace(/[-]/g, "_");
//     }
//     const singleHyphenArgIndex = names.findIndex(n => /^[-][^-]/.test(n));
//     if(singleHyphenArgIndex > -1){
//       const name = names[singleHyphenArgIndex];
//       return name.replace(/^[-]/, "").replace(/[-]/g, "_");
//     }
//     throw new Error("Invalid argument name");
//   }
  
//   public compileHelpMessages(){
//     const iterator = (a: Arg) => {
//       let msg = " " + a.names.join(", ");
//       if(a.options.help){
//         msg += `  ${a.options.help}`;
//         msg = msg.replace(/%\(prog\)s/, this._prog);
//         msg = msg.replace(/%\(default\)s/, (a.options.default as string) || "");
//       }
//       return msg;
//     };
    
//     const messages = [
//       `usage: ${this._prog} ` + this._optional_args.concat(this._positional_args).map(a => `[${a.names[0]}]`).join(" "),
//     ];
    
//     if(this._positional_args.length > 0){
//       messages.push("");
//       messages.push("positional arguments:");
//       messages.push(...this._positional_args.map(iterator));
//     }
//     if(this._optional_args.length > 0){
//       messages.push("");
//       messages.push("optional arguments:");
//       messages.push(...this._optional_args.map(iterator));
//     }
    
//     return messages.join("\n");
//   }
  
//   /**
//    * Separate short form argument which doesn't have space character between name and value. 
//    * For example, turn:
//    *   "-x1" => ["-x", "1"]
//    *   "-x 1" => ["-x", "1"]
//    *   "-xxxxx" => ["-x", "xxxx"]
//    * @param args - arguments passed
//    */
//   public normalizeArgs(args: string[]) {
//     if(this._optional_args.length < 1){
//       return args;
//     }
    
//     const norm: string[] = [];
//     for(let i=0;i<args.length;i++){
//       const arg = args[i];
//       // Only short form args like '-x' are targets.
//       if(!/^[-][^-]/.test(arg)){
//         norm.push(arg);
//         continue;
//       }
      
//       let optionalArgWithoutSpaceFound = false;
//       for(let k=0;k<this._optional_args.length;k++){
//         const opt = this._optional_args[k];
//         const index = opt.names.findIndex(n => /^[-][^-]$/.test(n) && n !== arg && new RegExp(`^${n}`).test(arg));
//         if(index < 0){
//           continue;
//         }
//         const name = opt.names[index];
//         const index2 = arg.indexOf(name) + name.length;
//         const value = arg.substring(index2);
//         norm.push(name, value);
//         optionalArgWithoutSpaceFound = true;
//         break;
//       }
      
//       if(!optionalArgWithoutSpaceFound){
//         norm.push(arg);
//       }
//     }
    
//     return norm;
//   }
// }
