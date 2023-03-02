Using this repo:

This repo can be installed via cargo

    cargo install clvm_tools_rs
    
The most current version of the language is in the rollup branch:

    20221005-rollup
    
To install the current release:

    cargo install clvm_tools_rs
    
To install from a specific branch:

    
    cargo install --no-default-features --git 'https://github.com/Chia-Network/clvm_tools_rs' --branch 20221005-rollup
    
To install a git checkout into your current python environment (must be in some kind of venv or conda environment):

    git clone https://github.com/Chia-Network/clvm_tools_rs
    cd clvm_tools_rs
    maturin develop
    
Most people still compile chialisp via python.  One way to set up compilation
in that way is like this:

    import json
    from clvm_tools_rs import compile_clvm

    def compile_module_with_symbols(include_paths,source):
        path_obj = Path(source)
        file_path = path_obj.parent
        file_stem = path_obj.stem
        target_file = file_path / (file_stem + ".clvm.hex")
        sym_file = file_path / (file_stem + ".sym")
        compile_result = compile_clvm(source, str(target_file.absolute()), include_paths, True)
        symbols = compile_result['symbols']
        if len(symbols) != 0:
            with open(str(sym_file.absolute()),'w') as symfile:
                symfile.write(json.dumps(symbols))

The command line tools provided:

    - run -- Compiles CLVM code from chialisp

    Most commonly, you'll compile chialisp like this:

      ./target/debug/run -O -i include_dir chialisp.clsp
    
    'run' outputs the code resulting from compiling the program, or an error.
    
    - repl -- Accepts chialisp forms and expressions and produces results
              interactively.
              
    Run like:
    
      ./target/debug/repl
      
    Example session:
    
    >>> (defmacro assert items
       (if (r items)
           (list if (f items) (c assert (r items)) (q . (x)))
         (f items)
         )
       )
    (q)
    >>> (assert 1 1 "hello")
    (q . hello)
    >>> (assert 1 0 "bye")
    failed: CompileErr(Srcloc { file: "*macros*", line: 2, col: 26, until: Some(Until { line: 2, col: 82 }) }, "clvm raise in (8) (())")
    >>> 

    - cldb -- Stepwise run chialisp programs with program readable yaml output.
    
      ./target/debug/cldb '(mod (X) (x X))' '(4)'
      ---
      - Arguments: (() (4))
        Operator: "4"
        Operator-Location: "*command*(1):11"
        Result-Location: "*command*(1):11"
        Row: "0"
        Value: (() 4)
      - Env: "4"
        Env-Args: ()
        Operator: "2"
        Operator-Location: "*command*(1):11"
        Result-Location: "*command*(1):13"
        Row: "1"
        Value: "4"
      - Arguments: (4)
        Failure: clvm raise in (8 5) (() 4)
        Failure-Location: "*command*(1):11"
        Operator: "8"
        Operator-Location: "*command*(1):13"

    - brun -- Runs a "binary" program.  Instead of serving as a chialisp
      compiler, instead runs clvm programs.
    
    As 'brun' from the python code:
    
    $ ./target/debug/run '(mod (X) (defun fact (N X) (if (> 2 X) N (fact (* X N) (- X 1)))) (fact 1 X))'
    (a (q 2 2 (c 2 (c (q . 1) (c 5 ())))) (c (q 2 (i (> (q . 2) 11) (q . 5) (q 2 2 (c 2 (c (* 11 5) (c (- 11 (q . 1)) ()))))) 1) 1))
    $ ./target/debug/brun '(a (q 2 2 (c 2 (c (q . 1) (c 5 ())))) (c (q 2 (i (> (q . 2) 11) (q . 5) (q 2 2 (c 2 (c (* 11 5) (c (- 11 (q . 1)) ()))))) 1) 1))' '(5)'
    120
    
    - opc -- crush clvm s-expression form to hex.
    
    As 'opc' from the python code.
    
    opc '(a (q 2 2 (c 2 (c (q . 1) (c 5 ())))) (c (q 2 (i (> (q . 2) 11) (q . 5) (q 2 2 (c 2 (c (* 11 5) (c (- 11 (q . 1)) ()))))) 1) 1))'
    ff02ffff01ff02ff02ffff04ff02ffff04ffff0101ffff04ff05ff8080808080ffff04ffff01ff02ffff03ffff15ffff0102ff0b80ffff0105ffff01ff02ff02ffff04ff02ffff04ffff12ff0bff0580ffff04ffff11ff0bffff010180ff808080808080ff0180ff018080
    
    - opd -- disassemble hex to s-expression form.
    
    As 'opd' from the python code.
    
    opd 'ff02ffff01ff02ff02ffff04ff02ffff04ffff0101ffff04ff05ff8080808080ffff04ffff01ff02ffff03ffff15ffff0102ff0b80ffff0105ffff01ff02ff02ffff04ff02ffff04ffff12ff0bff0580ffff04ffff11ff0bffff010180ff808080808080ff0180ff018080'
    (a (q 2 2 (c 2 (c (q . 1) (c 5 ())))) (c (q 2 (i (> (q . 2) 11) (q . 5) (q 2 2 (c 2 (c (* 11 5) (c (- 11 (q . 1)) ()))))) 1) 1))
