Compiler theory of operation
==

Code
--

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
(by running a program that emits a mod form), but instead is purpose-built to
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

How CLVM code carries out programs
--

0. _The basics of CLVM from a compilation perspective_

One can think of CLVM as a calculator with 1 tricky operator, which is called 'a'
(apply).  The calculator's state can be thought of as a CLVM value like this:

  ((+ 2 5) . (99 101))
  
You can imagine the CLVM machine doing this on each evaluation step:

    Find the rightmost index (described well here: [https://github.com/Chia-Network/clvm_tools_rs/blob/a660ce7ce07064a6a81bb361f169f6de195cba10/src/classic/clvm_tools/node_path.rs#L1](clvm paths) ) in the left part of the state that is not in the form of a quoted value
    (q . <something>) and:
   
     - if it's a number, enquote the correspondingly indexed value from
       the right part and replace the number with that.
       
     - otherwise, it must be an operator applicable to some constants so
       evaluate it.
       
    In this case,
    
      ((+ 2 3) . (99 . 101)) -> ((+ 2 (q . 101)) . (99 . 101))
      ((+ 2 (q . 101)) . (99 . 101)) -> ((+ (q . 99) (q . 101)) . (99 101))
      ((+ (q . 99) (q . 101)) . (99 . 101)) -> 200
      
    Of course, CLVM evaluators try to be more efficient than searching subtrees
    like this but at a theoretical level that's all one needs.
    
    The 'a' operator is actually not very exceptional in this, but you can think
    of its properties like this:
    
    1. It conceptually ignores one level of quoting from its first argument.
    2. It returns (q . X) when its first argument matches the pattern
       (q . (q . X)).
    3. When traversed during the search for the next rightmost element to
       transform, the right hand part of the machine state transforms into
       the dequoted form of its right hand argument:

            Nothing special happened yet, we just simplified a's second argument -.
                                                                                  v
      ((+ (q . 1) (a (q . (* (q . 3) 1)) 2)) . (10)) -> ((+ (q . 1) (a (q . (* (q . 3) 1) (q . 10)))) (10)))

                                      ,--- Here we traverse a and notice that we're entering the quoted code with a's env
                                      |                                                                  |
                                      v                                                                  v
      ((+ (q . 1) (a (q . [(* (q . 3) 1) . 10]) (q . 10)) . (10)) -> ((+ (q . 1) (a (q . (* (q . 3) (q . 10))) (q . 10))) . (10))

            The inner expression multiplied 3 by 10 and now matches (q . (q . X)) --.
                                                                                    v
      ((+ (q . 1) (a (q . (* (q . 3) (q . 10))))) . (10)) -> ((+ (q . 1) (a (q . (q . 30)) . (q . 10))) . (10))

        A disappears because we reached its end state of (q . (q . X)) --.
                                                                         v
      ((+ (q . 1) (a (q . (q . 30)) (q . 10))) . (10)) -> ((+ (q . 1) (q . 30)) . (10))

                                          Done

      ((+ (q . 1) (q . 30)) . (10)) -> 31

Thinking conceptually like this, we can construct any program we want by computing
a suitable environment (right side) and suitable code (left side), and letting
CLVM evaluate them until its done.  There are pragmatic things to think about in
how CLVM is evaluated:

 - If we have a program with functions that know about each other, their code has
   to be available to the program as quoted expressions to give to some 'a'
   operator.
   
 - If we have flow control, we have to model it by using some kind of computation
   and pass through code to an 'a' operator.
   
 - If we want to remember anything, we have to make an environment that contains it
   and then use it in some other code via an 'a' operator.
   
If one thinks of everything in these terms, then it isn't too difficult to generate
code from chialisp.

1. _The basic units of CLVM execution are env lookup and function application_

Because there is no memory other than the environment in CLVM, a basic building
block of CLVM code is an environment lookup.  If you consider the arguments to
a function to be some kind of mirror of the program's current environment:

    (defun F (X Y Z) (+ X Y Z))
    
    brun '(+ 2 5 11)' '(10 11 12)' -> 33
    
Then you can see that there's nothing keeping references to the function's
argument list from just becoming references.

You can do the same thing with functions in the environment:

    brun '(+ (a 2 (c 5 ())) (q . 3))' '((* (q . 2) 2) 9)' -> 21
    
But we don't want to make the user send in another copy of the program when
running the program, and even more, if it needs that function more than once,
we'll have to explicitly carry it around.

Richard's answer and the generallly accepted one is to let the environment usually
be a cons whose first part is the full set of constants and functions the program
can use and the rest part is the arguments to the current function.  Optimization
may in the future make this more complicated but thinking about it in this way
makes a lot of things pretty easy to reason about.

The program starts by putting its arguments with all its functions and applying
the main expression:

    (a main-expression (c (env ...) 1))

The main-expression expects the functions it has access to to be in the left
part of the environment:

                              .-- Reference to the left env.
                              |    .-- An argument
                              v    v
    (a (a some-even-number (c 2 (c 5 ()))) (c (env ...) 1))

And those functions expect the same thing, so if they generate code in the same
way, for example, in this program, the function could call itself recursively:

    (a (i 5 (q . (a some-even-number (c 2 (c (r 5) ())))) ()) 1)
    
some-even-number refers to the same subpart of the environment because we've
promised ourselves that the part of the environment containing ourselves is at
the same place in the environment 

Because the 'a' operator shares a lot of properties with a function call in a
purely functional language, chialisp compilers tend to rely heavily on "desugaring"
various language features into function calls so that they can use the code
generation tools they already have (hopefully) that implements functions.

This isn't uncommon in language compilers, but converting things to functions is
a higher percentage of what chialisp has to do.

The second thing chialisp compilers have to do is synthesize ("reify") the
environment to fit the shape that code it's calling is expected.  Consider this:

   (let ((X (+ Y 1))) (* X 2))
   
In chialisp, there are only a few choices you can make:

- Replace X with (+ Y 1) everywhere it appears in the body and return that.

    (* (+ Y 1) 2)
  
- Make some anonymous function for the binding like 
   
    (defun let_binding_11234 (Y) (+ Y 1))
    
  and replace every X with (let_binding_11234 Y)
   
- Make a function for the let body like:

    (defun let_body_11234 (Y and_X?) (* and_X? 2))
    
  And replace the original site with:
  
    (let_body_11234 Y (+ Y 1))
    
This takes on complication, but isn't really any worse, if let bindings can nest
in various ways.  The goal of the chialisp compiler and its optimization are to
make decent choices for these and improve the degree to which they produce the
smallest possible equivalent code over time.  Each of these can be the right choice
under some circumstances.
    
2. _CLVM Heap is simiar to other eager functional languages_

    In CLVM, there are conses and atoms.  Atoms act as numbers and
    strings and conses act as boxes of size 2.
    
    (7 8 . 9) =
      
          (  .  )
           /   \
          7   (8 . 9)

    
    In cadmium, there are pointers and words.  Words act as numbers
    and pointers act as boxes of a size determined by their tag word.
        
    (7,(8,9)) =
    
      [size:2,7,*0x331110] 
                      \
                  [size:2,8,9]

    $ ocaml
    # let x = (7,(8,9));;
    val x : int * (int * int) = (7, (8, 9))
    # let a = Obj.repr x;;
    val a : Obj.t = <abstr>
    # Obj.size a;;
    - : int = 2
    # let b = Obj.field a 1;;
    val b : Obj.t = <abstr>
    # Obj.size b;;
    - : int = 2

