Compiler theory of operation
==

Basic structure and where to look for specific things
--

### About compilers in general

Software developers who wish to create a new compiler will typically begin by writing their code in a text editor. The files that contain this source code are then stored on disk. When executed, the program reads in some text, and outputs code in another language. This process is known by different terms, depending on the output:

* **translation** / **transpiliation** - the output is a higher-level language that humans might write
* **compilation** -- the output is a lower-level language that humans typically would not write

These two terms have some overlap -- humans sometimes do write assembler code, and some compilers treat JavaScript as a Virtual Machine on which to execute source code.

### Chialisp and CLVM

Chia has two separate languages that follow this high-low level paradigm -- Chialisp and CLVM (ChiaLisp Virtual Machine):
* **Chialisp** - a mid-level language in the vein of C++. Most of Chia's puzzles (smart coin code) are initially written in Chialisp
* **CLVM** - the low-level language into which Chialisp compiles. Chia nodes use this language to evaluate puzzles. Humans typically do not write code directly in CLVM

### Chialisp structure

A compiler has two basic structural options:

* Read all inputs, write output (e.g. golang)
* Read input a bit at a time and possibly produce output a bit at a time (e.g. C)

Chialisp compilers read the whole input first. The language allows the programmer to include external libraries. As in C, this is accomplished with a list of file paths. The Chialisp compiler reads the include files one at a time and treats them as if they had been included in the current program. Chialisp forms are allowed to appear in any order.

### Functions

In C, code is generated separately for each function. In Chialisp, the situation is similar -- each top-level function must exist as a quoted CLVM value in the program's invariant environment.

Note that the word _invariant_ is used here for two reasons:
1. CLVM code generation generally encodes these paths into multiple parts of the code
2. The representation of this information is consistent throughout the program's run

### Classic Chialisp

Some definitions:
* **primitive** -- an operator installed in the CLVM runtime system which is implemented in non-CLVM code
* **com operator** -- a CLVM primitive
* **constant folding** -- the compile-time process of inputting expressions that involve constants, and computing their results
* **pass** -- a traversal of the complete program in some representation to transform it into
another representation, even when both are internal to the compilation process
* **s-expression** -- the kinds of values held in lisp and lisp-like languages

The classic Chialisp compiler does not work in usefully separable passes. Instead, it produces a CLVM request to run a special primitive that runs one step of the Chialisp compilation. The compiler then wraps this primitive in a CLVM primitive that engages in optimization and constant folding.

In classic Chialisp, compilation is performed by constant folding, as that is what causes a CLVM primitive to be evaluated to a value when the argument is constant. There is a guarantee that the entire S-expression held during compilation in the classic compiler is completely transformed into CLVM. This is the only time of such a guarantee, so only one pass is needed.

### Modern Chialisp

Some definitions:

* **frontend** - the part of compilation that occurs directly after the user's source code is parsed. This is needed for ergonomic reasons. It is normal for users to write parts of the language that don't translate directly to the data structures used to generate code. Because of this, _frontend_ processing first translates the user's text into a more convenient representation for further processing.
* **intermediate representation** - a data structure that is built and used during compilation, and discarded afterward. It contains some essential or extract meaning from the source program. It relates to either the program's meaning, its code generation, or some other process the compiler must perform.
* **high-level intentions** - signaled by the user and translated into the frontend's intermediate representation of the program
* **desugaring** - the process of translating high-level intentions into a program with targeted elements. These elements are closely related to the final environment for which the code is being generated
* **declaration** - a name given to a reusable part of a program. In many languages it is synonymous with -- or at least co-located with -- a _definition_
* **definition** - the site where a named object in a user's program is given a concrete form
* **left environment** - the invariant part of the CLVM environment which is given to the program when its main expression is run. It provides a consistent pool of sibling functions and constant data that the program is able to draw from
* **symbols** - a parallel set of information about a program regarding user-understandable names and locations that can be associated with landmarks in the generated code
* **sha256tree** - a standard process by which CLVM values are given a fixed-length hash identifier based on their content. It has nearly zero possibility of generating collisions

Modern Chialisp is compiled in several distinct phases:

#### Frontend processing

* Before any frontend work is done, the first file, as well as all include files, are completely parsed
* At the beginning of the compiler frontend, preprocessing in the new compiler takes place in [preprocessor.rs](/src/compiler/preprocessor.rs). This can (and probably should) be broken out into a pipeline at the same level as the frontend eventually
* [frontend.rs](/src/compiler/frontend.rs) contains the compiler frontend. It currently calls preprocess at [line 718](/src/compiler/frontend.rs#L718) in `frontend_start`.

#### Intermediate representation

The main intermediate representation used by the modern compiler is a CompileForm, which contains a complete representation of the input program expressed in a set of HelperForm objects and a BodyForm object.

CompileForm depends on HelperForm, which in turn depends on BodyForm. All three are defined in [comptypes.rs](/src/compiler/comptypes.rs), currently in the following locations:

1. **BodyForm** -- [line 122](/src/compiler/comptypes.rs#L122)

  BodyForm contains every type of expression the Chialisp language allows. Because the frontend is still in the process of collecting information when it converts the user's code into these data structures, it does not necessarily know (for example) what function is being referred to by a function call. It therefore does not make any claim that the program is self-consistent when exiting the compiler frontend.
  
  However, at the end of that pass it's possible to make additional checks. For for example, [usecheck.rs](/src/compiler/usecheck.rs) consumes a CompileForm yielded from the compiler frontend in order to check for unused mod arguments.

2. **HelperForm** -- [line 218](/src/compiler/comptypes.rs#L218)

  HelperForm concerns representing the kinds of declarations.

3. **CompileForm** -- [line 255](/src/compiler/comptypes.rs#L255)

  CompileForm provides a single object that encapsulates the entire meaning of a Chialisp program. It is the only thing that is passed on to code generation.

#### Desugaring

The next phase is desugaring. This phase will likely be moved out of codegen to be done fully first. However, it still will count as a full compiler pass because it is completed before any code generation activities take place.
  
#### Frontend optimizer

The frontend optimizer is intended to be run after the desugaring phase. However, it is currently still being developed in a branch. It performs higher level transformations on the code that result in simpler or smaller code that has the same meaning as the original, but in a form that facilitates better code generation.

For example, in Chialisp the frontend optimizer notes when a stack of `(f` and `(r` primitive invocations exist, and translating them into a numeric path, saving space.

#### Code generation

In the code generation phase, the _left environment_ shape is produced. This results in `SExp`, the data structure that represents S-expressions in this compiler. It is currently defined at line 33 of [sexp.rs](/src/compiler/sexp.rs).

In both the classic and modern compilers, the parsed source code and emitted code are represented by their respective views of S-expressions.

The full power of the modern S-expression isn't required in the emitted CLVM code, but it's convenient because it carries some useful information from the user's perspective. Its `Srcloc` (defined in [srcloc.rs](/src/compiler/srcloc.rs) contains a record of what part of the source code it was generated from. These are collected into the _symbols_.

In the case of Chialisp, landmarks are identified by _sha256tree_. Because of this, the symbols can refer to code by its sha256tree hash, as well as give names to sites in the generated code.

---

### Dive into the code from start to compiler

#### History

A brief history of the Chialisp compiler:
* First iteration was in Python
* Ported to Typescript
* Ported to Rust in the [clvm_rs](https://github.com/Chia-Network/clvm_rs) repository

The Rust compiler started in ocaml as a sketch of how the structure of a Chialisp compiler could improve some weaknesses of the original Chialisp compiler:
* Reporting exact coordinates of errors in ways that were more understandable to users
* Preserving more information from the source text throughout compilation (the ability to do something like source maps in Javascript)
* Adding the ability to provide new forms with a reduced risk of changing the form of code that already compiled

In order to keep existing code working and ensure that existing processes didn't break, a conservative approach was taken. The Rust code supports compiling an advanced form of the original Chialisp dialect, while maintaining
the shape and structure of the original code. Since it was in a python style to begin with, that may make some of it difficult to navigate.

#### Major functions

The python code started with entry points into two major functions, `call_tool` and `launch_tool`, of which `launch_tool` was the one that exposed code compilation and is the more complex. Here's a guide to navigating it.

The python code included [cmds.py](https://github.com/Chia-Network/clvm_tools/blob/main/clvm_tools/cmds.py). The structure of the rust code is similar -- [cmds.rs](/src/classic/clvm_tools/cmds.rs) contains the code for all the tools that historically existed, such as `run`, `brun`, `opc`, `opd`, and `launch_tool`. This is exactly as in the python code.

Similarly to the python code, the rust code starts by decoding arguments using an analog of argparse. The arguments are stored in a HashMap with type tags determining what the stored data is. In the case of PathOrCode conversion type, it has been extended slightly to remember the filename that was read in. That's useful so that the returned string can inform compilation of the filename it's compiling, and it can in turn inform the source locations what file name they belong to.

A few other things are similar. Since classic Chialisp compilation mixes code in the compiler's source language with expressions written in Chialisp and stores state in the CLVM runtime environment, a runtime environment is prepared for it containing the search paths for include files.

The classic compiler reads include files via an imperative CLVM operator, `_read`, installed at the time when the interpreter is created. This interpreter was called `stage_2` in the Python code so a function, `run_program_for_search_paths` was included in [operators.py](/src/classic/clvm_tools/stages/stage_2/operators.py).
The normal operation of a CLVM environment is usually immutable. This stance is further encouraged by the lack of lifetime variables decorating the callbacks to the CLVM runner in `clvmr`. Because of that, the code downstream uses a C++ like approach to enriching the runtime environment with mutable state. The actual call to `run_program_for_search_paths` is currently located at [line 798](/src/classic/clvm_tools/cmds.rs#L798) of `cmds.rs`.

At [line 901](/src/classic/clvm_tools/cmds.rs#L901) of `cmds.rs` (currently), `detect_modern` is called. This function returns information regarding whether the user requested a specific Chialisp dialect. This is important because modern and classic Chialisp compilers don't accept precisely the same language and will continue to diverge. Due to the demands of long-term storage of assets on the blockchain, it is necessary for code that compiles in a specific form today retains that form forever. The dialect then tells the compiler which of the different forms compilation could take among compatible alternatives. This allows us to make better choices later on, and to grow the ways in which the compiler can benefit users over time. It also enables HelperForm and BodyForm to support a clean separation between generations of features.

The result of this choice is taken at line 940, where in the case of a modern dialect, a short-circuit path is taken that bypasses the more complicated external interface of the classic compiler (below). Since classic compilation closely mirrors the form the python code takes (and should not be as new to readers), I'll skip it for now and focus on modern compilation.

The python compilation interface used by `chia-blockchain` is information-poor, so cl21's basic optimization is enabled when called from python. However, it requires a traditional style `-O` flag on the command line (line 358). When called this way, python and command line compilation are the same. This will be fixed in the cl22 dialect, which will override the cl21 optimization flag entirely.

A pure dynamic interface called `CompilerOpts` implements a set of toggles and settings that are global to the compilation process. It also provides information during compilation. One of these is required for compilation
in modern Chialisp; the one currently used is generated at line 946.

A main entry point to modern compilation that does all the needed work is in the `compile_file` interface of [compiler.rs](/src/compiler/compiler.rs). It's called at line 952 (currently). Given a collection of prerequisite objects, it produces SExp using `parse_sexp` in [sexp.rs](/src/compiler/sexp.rs) (line 817 currently) to parse the source, then it gives the resulting list of parsed forms to `compile_pre_forms` (line 170 of `compiler.rs` currently). `compile_pre_forms` first runs the frontend at line 177 of `compiler.rs` by calling the `frontend` function at line 747 of [frontend.rs](/src/compiler/frontend.rs). This yields a CompileForm, which represents the full semantics of the user's program.

It calls `codegen` (currently) at line 189 of `compiler.rs`, which yields the compiled code in the way that has been outlined above and is detailed below.

When called in this way, the `launch_tool` method of [cmds.rs](/src/classic/clvm_tools/cmds.rs) terminates early, yielding the compiled program or error from the modern compiler process. This is true whether the error was encountered while parsing, preprocessing, doing frontend transformation, code generation or any other part of the modern compiler that
can produce an error. Every error from the modern compiler has a `Srcloc`, which refers to something relevant in the source code. These errors have a relevant source of information through the process via the pervasive use
of `Srcloc` in the various compiler data structures.

---

### Code

The modern compiler operates on just a few exposed types, and describes any program using these (forming a rough hierarchy).

* CompileForm ([comptypes.rs](/src/compiler/comptypes.rs))
  * HelperForm
    * BodyForm

Things referred to as "helpers" are some kind of HelperForm. These are the definitions of things programs use as building blocks (as outlined below), broadly the out-of-line constant, macro and function definitions that are used to provide abstractions and parts of programs.

HelperForm and BodyForm are sum types which contain elements of the various kinds
of things the compiler understands as distinct forms the user can use.

#### HelperForm

HelperForm is one of:
* Defconstant(DefconstData)
* Defmacro(DefmacData)
* Defun(bool, DefunData) (where true = inline)
    
This spans the kinds of declarations that Chialisp can contain. Having a well-defined frontend type serves as a proof of sorts that the code has been fully read and understood. In the frontend form, we can perform transformations on the code without worrying about breaking its more primitive representation. Since we've extracted the code's meaning, we can more easily substitute runtime compatible forms of the code from the perspective of the code's meaning.

#### BodyForm

The BodyForm is more diverse and things like Lambdas add alternatives. Since these are cleanly separated from a meaning perspective, it's possible to think of groups of later alternatives as being layered on top of earlier ones without affecting their meaning or how they're processed.

These are the current BodyForm alternatives:

    Let(<LetFormKind>, <LetData>) --
    
      Represents let forms and anything that's expressible through let forms, such as the 'assign' form here:
      
  [assign form pr](https://github.com/Chia-Network/clvm_tools_rs/pull/103)
        
    Quoted(SExp) --
      
      Represents literal data in any form. In particular, Quoted ensures that the semantic meaning of the value is always as a constant as opposed to being treated as a reference to something or a variable name.
      
    Value(SExp) --
    
      Value has a couple of meanings based on the content.
        * If it contains a value in those domains, it represents a self-quoting value type such as a quoted string or integer.
        * if it contains an atom, the atom is treated a reference to a constant or environment binding.
      
    Call(Srcloc, Vec<Rc<BodyForm>>) --
    
      Represents any kind of invocation in an expression position in the code, whether it's a macro invocation, invocation of a function or a primitive.

      The vector contains the top-level spine arguments of the notional cons form that will be given as arguments. This language disallows tail improper call forms because, while identifiers work in tail position, there's no easy way to identify the user's intention to place a more
      complex form at the improper tail.
      
      An 'apply' form as in [lisp](http://clhs.lisp.se/Body/f_apply.htm) honoring the convention that the final argument is properly bound according to the structure of the called functions arguments, allowing functions with tail-improper arguments to be called without having to manufacture a tail improper syntax for the call site.
    
    Mod(Srcloc, CompileForm) --
    
       Chialisp allows (mod () ...) as an expression yielding the compiled code in the form. Naturally, its analog in the compiler contains a CompileForm, which allows it to be a full program of its own.

These are built from,and often contain, elements of SExp, which is also a sum type. The sexp type is intended to reflect user intention, while keeping the ability to treat each value as plain CLVM when required. This places a greater burden on the implementation when using these as values in a program, but allows all parts of
compilation (including code generation output) to remain associated with sites and atoms in the source text when those associations make sense. It contains:

    Nil(Srcloc) -- Represents a literal Nil in the source text.
    
      It may be useful for this to be distinct from 0 and "", at the very least to remember how the user spelled this particular value, but also (for example) it's possible to type Nil as a kind of list, but reject "" or 0 in the same scenario.
      
    Cons(Srcloc,Rc<SExp>,Rc<SExp>) -- The cons value.
    
    Integer(Srcloc,Number) -- An integer.
    
       Since the value system contains integers as a first-class kind, it's possible to positively differentiate atoms from integers, unless something disrupts them. I am in the process of introducing a macro system that treats user input gently.
       
    QuotedString(Srcloc, u8, Vec<u8>) -- A quoted string.
    
       Since different kinds of quotes are possible, the QuotedString also remembers which quotation mark was used in the source text. Since its representation is distinct, it can't be confused with an identifier.
       
    Atom(Srcloc,Vec<u8>) -- An atom or identifier.

Its job is to process programs so it doesn't implement compilation the same way (by running a program that emits a mod form), but instead is purpose-built to read and process a program. As such, it doesn't rely on populating a CLVM environment with special operators, or on running anything necessarily in the VM, although it does that for constant folding and a few other things.

Compilation can be done in a few ways. There is a [CompilerOpts](src/compiler/compiler.rs) type which serves as a connection between the consumer's settings for the compiler and the compilation process. Its `compile_file` method takes a few objects it will need in case it must run CLVM code: an Allocator (clvmr) and a runner 
(`TRunProgram` from [stage_0.rs](/src/classic/clvm_tools/stages/stage_0.rs)).

It's used this way in 'run':

```
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
```

This is the full life cycle of Chialisp compilation from an outside perspective.

If you want to parse the source file yourself, you can use `parse_sexp` from [sexp.rs](/src/compiler/sexp.rs), which yields a result of `Vec<Rc<SExp>>`, a vector of refcounted pointers to s-expression objects. These are richer than CLVM values in that atoms, strings, hex values, integers and nils are distinguishable in what's read. This is similar to the code in `src/classic/clvm/type.rs`, but since these value distinctions are first-class in SExp, all values processed by the compiler, starting with the preprocessor ([preprocessor.rs](/src/compiler/preprocessor.rs)), going through the frontend ([frontend.rs](/src/compiler/frontend.rs)) and to code generation ([codegen.rs](/src/compiler/codegen.rs)) use these values. Every expression read from the input stream has a Srcloc ([srcloc.rs](/src/compiler/srcloc.rs)) which indicates where it was read from in the input. As long as the Srcloc is copied from form to form, it allows the compiler to maintain known associations between input and results.

For example, you can implement syntax coloring by simply using `parse_sexp` to parse a file, run it through the preprocessor and frontend, and then decorate the locations present in the HelperForms accessible from the CompilerForm that results. If an error is returned, it contains a Srcloc that's relevant.

You can break down the basics of how Chialisp compilation functions like this:

```
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
// generated_code.1 is an Rc<SExp> which contains the output code.
```

PrimaryCodegen is the object where the code generation stores and updates information it needs and what gets collected during code generation. It's defined in [comptypes.rs](/src/compiler/comptypes.rs) (line 281 at present). Many of the functions in [codegen.rs](/src/compiler/codegen.rs) take a PrimaryCodegen, and most also return a PrimaryCodegen. During this process, the compilation state is updated by each of them.

#### PrimaryCodegen functions

Codegen starts by running `start_codegen` to introduce each helper to the PrimaryCodegen. Based on their types, it bins them into the appropriate parts of the code generator to lookup later:
* Defconstants are turned into mods and run. The result is stored in the PrimaryCodegen's constant set.
* The defconst form is evaluated by putting all Helpers (objects of HelperForm type) into an Evaluator and asking it to shrink the constant's expression (resulting in constant folding). The folded value must reduce to a constant, and if it does, it's stored in the constant set.
* Defmacros are converted to programs and compiled using the CompilerOpts' `compile_program` methods, which provide recursion, with an eye to allowing the generation of program code to be used during compilation. The resulting code is stored in the macro set.
* Next, let desugaring takes place (it is intended that this will be lifted out of
codegen to a separate pass). Let desugaring inspects each defun (because they appear in the compiled code) for
let forms, and produces a list of new forms that must be re-inspected. When no new forms are generated for any helper form, the full set of generated helpers and the original are introduced to either the defun set or the inline set in the PrimaryCodegen, based on their type. This will be a bit more flexible when desugaring has its own definite pass, as we'll have freedom to rearrange the inlining without disturbing codegen itself.
* Once all helpers are processed in this way, let desugaring takes place on the main expression of the program in the same way. The PrimaryCodegen has a special field for the main expression.

After start_codegen, the PrimaryCodegen is transformed by generating the dummy environment via the `dummy_function`'s internal function. For each non-inlined defun and tabled constant, it extracts the name and generates an environment shape. This is also where multiple definitions are detected. As a result of this process, InlineFunction objects are generated for each inline function and the PrimaryCodegen has its "parentfns" member populated.

Each surviving helper is then passed through the codegen_ and given an opportunity to transform the PrimaryCodegen. The bodies of all functions are placed in the PrimaryCodegen in the appropriate bin. Defuns are turned into mods and code generation is individually performed for them. The representation placed in the
PrimaryCodegen is of compiled code. During the process of generating code for each live defun, the compiler is configured with the parent module's PrimaryCodegen. This is done so that they observe the containing program's left environment, and therefore can request the code to make sibling function calls from it.

#### Invocation types

A few things about this are tricky; PrimaryCodegen uses a type called `Callable` to look up invocations. It recognizes a few types:
* **CallMacro** -- expands a macro and then treats the resulting output as the SExp representation of a BodyForm -- parses it and does expr code generation on it
* **CallInline** -- contains a literal body that is woven into the code via either the evaluator or [inline.rs](/src/compiler/inline.rs)
* **CallDefun** -- contains recorded code indicating how to look up the function, as well as the shape of its right env
* **CallPrim** -- contains a specification that a primitive is called; outputs a primitive form directly after doing codegen on the arguments
* **RunCompiler** -- This is exactly the "com" operator in classic Chialisp. When it is encountered, the expression evaluator creates a mod, prepares CompilerOpts to override the environment, provides this PrimaryCodegen for code generation, and changes other defaults to be used to compile the mod. The result is code that "takes place" in the current context by sharing the environment shape and using the current PrimaryCodegen as a starting point.
* **EnvPath** -- As a compromise to allowing certain expressions to become environment lookups when that might not be expected, I provide a dedicated env-lookup form, (@ n), where _n_ is a constant integer only. This desugars to a single environment lookup in the generated code.

#### Macro expansions

Macro expansions require transformation of the user's code into CLVM values and back. This is because the macro program is run as a CLVM program (when this was written, `src/compiler/clvm` wasn't fully mature and I hadn't written the evaluator yet).

A table of user supplied trees by treehash is made (the `build_swap_table_mut` function in [debug.rs](/src/compiler/debug.rs)), and the macro output is "rehydrated" by greedily replacing each matching subtree with the one taken from the pre-expansion macro callsite (the `relabel` function in `debug.rs`). In this way, the code mostly preserved distinctions between atoms and strings, etc in the source text through macro invocation assuming things weren't too intrusive.

After all live defuns have been treated, the compiler uses `final_codegen` to generate the code for its main expression and then `finalize_env` is called to match each identifier stored in the left environment with a form for which it has generated code recorded and build the env tree.

How CLVM code carries out programs

---

### CLVM compilation basics

One can think of CLVM as a calculator with 1 tricky operator, which is called `a` (apply). The calculator's state can be thought of as a CLVM value like this:

`((+ 2 5) . (99 101))`
  
The CLVM machine does this on each evaluation step:

* Find the rightmost index (described well here: [CLVM paths](https://github.com/Chia-Network/clvm_tools_rs/blob/a660ce7ce07064a6a81bb361f169f6de195cba10/src/classic/clvm_tools/node_path.rs#L1) ) in the left part of the state that is not in the form of a quoted value `(q . <something>)` and:
  * If it's a number, enquote the correspondingly indexed value from the right part and replace the number with that
  * Otherwise, it must be an operator applicable to some constants, so evaluate it
       
    In this case,
    
    `((+ 2 3) . (99 . 101)) -> ((+ 2 (q . 101)) . (99 . 101)) ((+ 2 (q . 101)) . (99 . 101)) -> ((+ (q . 99) (q . 101)) . (99 101)) ((+ (q . 99) (q . 101)) . (99 . 101)) -> 200`
      
Of course, CLVM evaluators try to be more efficient than searching subtrees like this, but at a theoretical level that's all one needs.
    
The `a` operator is actually not very exceptional, but you can think of its properties like this:
1. It conceptually ignores one level of quoting from its first argument
2. It returns `(q . X)` when its first argument matches the pattern `(q . (q . X))`
3. When traversed during the search for the next rightmost element to transform, the right-hand part of the machine state transforms into the dequoted form of its right hand argument:

```
      Nothing special happened yet, we just simplified a's second argument -.
                                                                            v
((+ (q . 1) (a (q . (* (q . 3) 1)) 2)) . (10)) -> ((+ (q . 1) (a (q . (* (q . 3) 1) (q . 10)))) (10)))
```

```
                                ,--- Here we traverse a and notice that we're entering the quoted code with a's env
                                |                                                                  |
                                v                                                                  v
((+ (q . 1) (a (q . [(* (q . 3) 1) . 10]) (q . 10)) . (10)) -> ((+ (q . 1) (a (q . (* (q . 3) (q . 10))) (q . 10))) . (10))
```

```
      The inner expression multiplied 3 by 10 and now matches (q . (q . X)) --.
                                                                              v
((+ (q . 1) (a (q . (* (q . 3) (q . 10))))) . (10)) -> ((+ (q . 1) (a (q . (q . 30)) . (q . 10))) . (10))
```

```
  A disappears because we reached its end state of (q . (q . X)) --.
                                                                   v
((+ (q . 1) (a (q . (q . 30)) (q . 10))) . (10)) -> ((+ (q . 1) (q . 30)) . (10))
```

```
                                    Done

((+ (q . 1) (q . 30)) . (10)) -> 31
```

Thinking conceptually like this, we can construct any program we want by computing a suitable environment (right side) and suitable code (left side), and letting CLVM evaluate them until its done. There are pragmatic things to think about in how CLVM is evaluated:

 - If we have a program with functions that know about each other, their code has to be available to the program as quoted expressions to give to some `a` operator.
   
 - If we have flow control, we have to model it by using some kind of computation and pass through code to an `a` operator.
   
 - If we want to remember anything, we have to make an environment that contains it and then use it in some other code via an `a` operator.
   
If one thinks of everything in these terms, then it isn't too difficult to generate code from Chialisp.

### CLVM execution basics

Because there is no memory other than the environment in CLVM, a basic building block of CLVM code is an environment lookup. If you consider the arguments to a function to be some kind of mirror of the program's current environment:

```
(defun F (X Y Z) (+ X Y Z))
    
brun '(+ 2 5 11)' '(10 11 12)' -> 33
```

Then you can see that there's nothing keeping references to the function's
argument list from just becoming references.

You can do the same thing with functions in the environment:

```
brun '(+ (a 2 (c 5 ())) (q . 3))' '((* (q . 2) 2) 9)' -> 21
```

But we don't want to make the user send in another copy of the program when running the program, and even more, if it needs that function more than once, we'll have to explicitly carry it around.

The generally accepted answer is to let the environment usually be a cons where:
1. The first part is the full set of constants and functions the program can use, and
2. The rest part is the arguments to the current function

Optimization may in the future make this more complicated, but thinking about it in this way makes a lot of things pretty easy to reason about.

The program starts by putting its arguments with all its functions and applying the main expression:

```
(a main-expression (c (env ...) 1))
```

The main-expression expects the functions it has access to to be in the left part of the environment:

```
                          .-- Reference to the left env.
                          |    .-- An argument
                          v    v
(a (a some-even-number (c 2 (c 5 ()))) (c (env ...) 1))
```

And those functions expect the same thing, so if they generate code in the same
way, for example, in this program, the function could call itself recursively:

```
(a (i 5 (q . (a some-even-number (c 2 (c (r 5) ())))) ()) 1)
```

`some-even-number` refers to the same subpart of the environment because we've promised ourselves that the part of the environment containing ourselves is at the same place in the environment.

Because the `a` operator shares a lot of properties with a function call in a purely functional language, Chialisp compilers tend to rely heavily on "desugaring" various language features into function calls so that they can use the code generation tools they already have (hopefully) that implements functions.

This isn't uncommon in language compilers, but converting things to functions is a higher percentage of what Chialisp has to do.

The second thing Chialisp compilers have to do is synthesize ("reify") the environment to fit the shape that code it's calling is expected. Consider this:

```
(let ((X (+ Y 1))) (* X 2))
```

In Chialisp, there are only a few choices you can make:

- Replace `X` with `(+ Y 1)` everywhere it appears in the body and return that:
  
  `(* (+ Y 1) 2)`
  
- Make some anonymous function for the binding like:
   
  `(defun let_binding_11234 (Y) (+ Y 1))`
    
  and replace every `X` with (`let_binding_11234 Y`)
   
- Make a function for the let body like:

  `(defun let_body_11234 (Y and_X?) (* and_X? 2))`
    
  And replace the original site with:
  
  `(let_body_11234 Y (+ Y 1))`
    
In each of these cases except the pure inline one, extra new arguments were fitted into the argument list of some function, and the function was called. In this way, we dreamed up an environment shape and then had to match it to call the function.

This takes on complication, but isn't really any worse, if let bindings can nest in various ways. The goals of the Chialisp compiler and its optimization are to:
1. Make decent choices for these, and
2. Improve the degree to which they produce the smallest possible equivalent code over time.

Each of these can be the right choice under some circumstances.

Along other lines, this example:

Imagine this program:

```
(mod (X)
    (defun list-length (N L) (if L (list-length (+ N 1) (r L)) N))
    (defun-inline QQQ (A . B) (+ A (list-length 0 B)))
    (QQQ X 4 5 6)
    )
```

The inline here destructures its arguments. The arguments aren't strictly aligned to the elements that are used to call it; `B` captures `(4 5 6)`. Because `QQQ` isn't really "called" with an apply atom, the shape of its environment is purely theoretical and yet the program *observes* that shape at runtime. We must, when required, aggregate or dis-aggregate arguments given by the user by figuring their positions with respect to landmarks we know. Best case, we can apply `first`, `rest` or `paths` to values we have as arguments if arguments in standard positions are destructured, worst case we have to `cons` values together as though the environment was being built for an `apply`.
    
### CLVM structure

CLVM Heap representation isn't dissimilar to other eager functional languages.

How CLVM compares to other functional languages in structure is a topic that is talked about occasionally, and many of its decisions are fairly alike what's out there:

In CLVM, there are conses and atoms. Atoms act as numbers and strings and conses act as boxes of size 2.

```
(7 8 . 9) =
  
      ( 7 .  )
           \
          (8 . 9)
```

In cadmium (the name some use for the ocaml bytecode vm), there are pointers and words. Words act as numbers and pointers act as boxes of a size determined by their tag word.

```
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
```