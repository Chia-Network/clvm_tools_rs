Compiler theory of operation
= 

The modern compiler operates on just a few exposed types, and describes any
program using these (forming a rough hierarchy).

CompileForm   (src/compiler/comptypes.rs)
  HelperForm
    BodyForm
    
HelperForm and BodyForm are sum types which contain elements of the various kinds
of things the compiler understands as distinct forms the user can use.  At this
time, HelperForm is one of:

    Defconstant(DefconstData)
    Defmacro(DefmacData)
    Defun(bool, DefunData) // true = inline
    
Which spans the kinds of declarations that chialisp can contain.  Having a well
defined frontend type serves as a proof of sorts (in the vein of the curry-howard
corresponence) that the code has been fully read and understood.  In the frontend
form, we can perform transformations on the code without worrying about breaking
its more primitive representation.  Since we've extracted the code's meaning we 
can more easily substitute runtime compatible forms of the code from the
perspective of the code's meaning.

The BodyForm is more diverse and things like Lambdas add alternatives.  Since
these are cleanly separated from a meaning perspective, it's possible to think
of groups of later alternatives as being layered on top of earlier ones without
affecting their meaning or how they're processed.

These are the current BodyForm alternatives:

    Let(LetFormKind, LetData) --
    
      Represents let forms and anything that's expressible through let forms,
      such as the 'assign' form here:
      
  [https://github.com/Chia-Network/clvm_tools_rs/pull/103](assign form pr)
        
    Quoted(SExp) --
      
      Represents literal data in whatever form.  In particular, Quoted ensures
      that the semantic meaning of the value is always as a constant as opposed
      to being treated as a reference to something or a variable name.
      
    Value(SExp) --
    
      Value has a couple of meanings based on the content.  It can represent
      a self quoting value type such as a quoted string or integer if it contains
      a value in those domains or if it contains an atom, the atom is treated
      a reference to a constant or environment binding.
      
    Call(Srcloc, Vec<Rc<BodyForm>>) --
    
      Represents any kind of invocation in an expression position in the code,
      whether it's a macro invocation, invocation of a function or a primtive.
      The vector contains the top-level spine arguments of the notional cons
      form that will be given as arguments.  This language disallows tail
      improper call forms because, while identifiers work in tail position,
      there's no easy way to identify the user's intention to place a more
      complex form at the improper tail.  An 'apply' form as in lisp

   [http://clhs.lisp.se/Body/f_apply.htm](chialisp apply)
   
       honoring the convention that the final argument is properly bound according
       to the structure of the called functions arguments, allowing functions with
       tail-improper arguments to be called without having to manfacture a tail
       improper syntax for the call site.
    
    Mod(Srcloc, CompileForm) --
    
       Chialisp allows (mod () ...) as an expression yielding the
       compiled code in the form.  Naturally, its analog in the compiler
       contains a CompileForm, which allows it to be a full program of
       its own.

These are built from and often contain elements of SExp, which is also a sum type.
The sexp type is intended to reflect user intention, but keep the ability to treat
each value as plain clvm when required.  This places a greater burden on the
implementation when using these as values in a program, but allows all parts of
compilation (including code generation output) to remain associated with sites
and atoms in the source text when those associations make sense.  It contains:

    Nil(Srcloc) -- Represents a literal Nil in the source text.
    
      It may be useful for this to be distinct from 0 and "", at the very
      least to remember how the user spelled this particular value, but
      also (for example) it's possible to type Nil as a kind of list,
      but reject "" or 0 in the same scenario.
      
    Cons(Srcloc,Rc<SExp>,Rc<SExp>) -- The cons value.
    
    Integer(Srcloc,Number) -- An integer.
    
       Since the value system contains integers as a first class kind,
       it's possible to positively differentiate atoms from integers
       unless something disrupts them.  I am in the process of
       introducing a macro system that treats user input gently.
       
    QuotedString(Srcloc, u8, Vec<u8>) -- A quoted string.
    
       Since different kinds of quotes are possible, the QuotedString
       also remembers which quotation mark was used in the source text.
       Since its representation is distinct it can't be confused with
       an identifier.
       
    Atom(Srcloc,Vec<u8>) -- An atom or identifier.

Its job is to process programs so it doesn't implement compilation the same way
(by running a program that emits a mod form), but instead is purpose built to
read and process a program.  As such it doesn't rely on populating a clvm
environment with special operators or on running anything necessarily in the VM,
although it does that for constant folding and a few other things.

Compilation can be done in a few ways.  There is a 

  CompilerOpts (src/compiler/compiler.rs)
  
Type which serves as connection between the consumer's settings for the compiler
and the compilation process.  Its method compile\_file takes a few objects it will
need in case it must run clvm code: an Allocator (clvmr) and a runner 
(TRunProgram from src/classic/stages/stage_0.rs).

It's used this way in 'run':

        let opts = Rc::new(DefaultCompilerOpts::new(&use_filename))
            .set_optimize(do_optimize)
            .set_search_paths(&search_paths)
            .set_frontend_opt(dialect > 21);
        let unopt_res = compile_file(
            &mut allocator,
            runner.clone(),
            opts.clone(),
            &input_program,
            &mut symbol_table,
        );
        let res = if do_optimize {
            unopt_res.and_then(|x| run_optimizer(&mut allocator, runner, Rc::new(x)))
        } else {
            unopt_res.map(Rc::new)
        };

This the the full lifecycle of chialisp compilation from an outside perspective.

If you want to parse the source file yourself, you can use parse_sexp from 
src/compiler/sexp, which yields a result of Vec&lt;Rc&lt;SExp&gt;&gt;, a vector
of refcounted pointers to s-expression objects.  These are richer than clvm
values in that atoms, strings, hex values,integers and nils are distinguishable
in what's read.  This is similar to the code in src/classic/clvm/type.rs but
since these value distinctions are first-class in SExp, all values processed
by the compiler, starting with the preprocessor (src/compiler/preprocessor.rs), 
going through the frontend (src/compile/frontend.rs) and to code generation
(src/compiler/codegen.rs) use these values.  Every expression read from the
input stream has a Srcloc (src/compiler/srcloc.rs) which indicates where it
was read from in the input, and as long as the srcloc is copied from form to
form, it allows the compiler to maintain known associations between input and
results.  For example, you can implement syntax coloring by simply using
parse\_sexp (src/compiler/sexp.rs) to parse a file, run it through the
preprocessor and frontend, and then decorate the locations present in the
HelperForms accessible from the CompilerForm that results.  If an error is
returned, it contains a srcloc that's relevant.

You can break down the basics of how chialisp compilation functions like this:

        let mut allocator = Allocator::new();
        let mut symbol_table = HashMap::new();
        let runner = Rc::new(DefaultProgramRunner::new());
        let opts = Rc::new(DefaultCompilerOpts::new(&use_filename))
            .set_optimize(do_optimize)
            .set_search_paths(&search_paths)
            .set_frontend_opt(dialect > 21);
        let parsed = parse_sexp(Srcloc::start(&use_filename), file_content.bytes())?;
        let compileform = frontend(opts.clone(), &parsed)?;
        let generated_code = codegen(&mut allocator, runner, opts, &compileform, &mut symbol_table)?;
        // generated_code.1 is an Rc<SExp> which contains the output
        // code.

Everything before code generation is uninteresting, but I'll note at a high level
how functions on PrimaryCodegen function.

codegen starts by running start_codegen to introduce each helper to the
PrimaryCodegen and based on their types, bin them into the appropriate parts
of the code generator to lookup later:

    Defconstants are turned into mods and run, unlike classic chialisp.
    The result is stored in the PrimaryCodegen's constant set.
    
    The new defconst form is evaluated by putting all Helpers into an Evaluator
    and asking it to shrink the constant's expression (resulting in constant
    folding).  The folded value must reduce to a constant, and if it does,
    it's stored in the constant set.
    
    Defmacros are converted to programs and compiled using the
    CompilerOpts' compile_program method.  These methods on CompilerOpts
    provide this kind of recursion with an eye to allowing the generation
    of program code to be used during compilation.  The resulting code
    is stored in the macro set.
    
Next, let desugaring takes place (my intention is to lift this out of codegen to
a separate pass).
    
Let desugaring inspects each defun (because they appear in the compiled code) for
let forms and produces a list of new forms that must be re-inspected.  When no
new forms are generated for any helper form, the full set of generated helpers
and the original are introduced to either the defun set or the inline set in
the PrimaryCodegen based on their type.  This will be a bit more flexible when
desugaring has its own definite pass as we'll have freedom to rearrange the
inlining without disturbing codegen itself.

Once all helpers are processed in this way, let desugaring takes place on the
main expression of the program in the same way.  The PrimaryCodegen has a special
field for the main expression.

After start_codegen, the PrimaryCodegen is transformed by generating the dummy
environment via the dummy\_functions internal function.  For each non-inlined
defun and tabled constant, it extracts the name and generates an envrionment
shape from the names.  This is also where multiple definitions are detected.
As a result of this process, InlineFunction objects are generated for each inline
function and the PrimaryCodegen has its "parentfns" member popluated.

Each surviving helper is then passed through the codegen_ and given an opportunity
to transform the PrimaryCodegen.  The bodies of all functions are placed in the
PrimaryCodegen in the appropriate bin.  Defuns are turned into mods and code
generation is individually performed for them.  The representation placed in the
PrimaryCodegen is of compiled code.  During the process of generating code for
each live defun, the compiler is configured with the parent module's PrimaryCodegen
so that they observe the containing program's left environment and therefore can
request the code to make sibling function calls from it.

A few things about this are tricky; PrimaryCodegen uses a type called Callable to
lookup invocations and recognizes a few types:

    CallMacro
      
      Expands a macro and then treats the resulting output as the SExp
      representation of a BodyForm, so parses it and does expr code
      generation on it.
      
    CallInline
    
      Contains a literal body that is woven into the code via either the evaluator
      or src/compiler/inline.rs.
    
    CallDefun
    
      Contains recorded code indicating how to look up the function as
      well as the shape of its right env.
    
    CallPrim
    
      Contains a specification that a primitive is called, so outputs a primitive
      form directly after doing codegen on the arguments.
        
    RunCompiler
    
      This is exactly the "com" operator in classic chialisp.  When it is
      encountered, the expression evaluator creates a mod, prepares CompilerOpts
      to override the environment, provide this PrimaryCodegen for code generation
      and change other defaults and then uses it to compile the mod.  The result
      is code that "takes place" in the current context by sharing the environment
      shape and using the current PrimaryCodegen as a starting point.
        
    EnvPath
    
      As a compromise to allowing certain expressions to become environment lookups
      when that might not be expected, I provide a dedicated env-lookup form, 
      (@ n), where n is a constant integer only.  This desugars to a single 
      environment lookup in the generated code.

macro expansions require transformation of the user's code into clvm values and
back because the macro program is run as a clvm program (when this was written,
src/compiler/clvm wasn't fully mature and I hadn't written the evaluator yet).
A table of user supplied trees by treehash is made (src/compiler/debug.rs, 
build\_swap\_table\_mut), and the macro output is "rehydrated" by greedily
replacing each matching subtree with the one taken from the pre-expansion macro
callsite (src/compiler/debug.rs, relabel).  In this way, the code mostly preserved
distinctions between atoms and strings, etc in the source text through macro
invocation assuming things weren't too intrusive.

When running the "com" operator, which is used in macros to give the 

After all live defuns have been treated, the compiler uses final\_codegen to
generate the code for its main expression and then finalize\_env is called to
match each identifier stored in the left environment with a form for which it
has generated code recorded and build the env tree.
