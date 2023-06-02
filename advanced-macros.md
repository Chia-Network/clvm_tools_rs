Advanced Macros
==

Macros in chialisp used to be self contained programs running on the bare CLVM.
This gave it decent power with little code but also caused some problems due to
the narrowness of the value representation in CLVM.  In a larger scheme or lisp
homoiconicity is taken literally; each of the inputs the user can give is
representend as a distinct kind of value in the VM so it's possible for programs
in the language to translate to programs in the VM that can fulfill user
expectations, such as that identifiers and quoted strings are different kinds of
things; one is a variable binding and one represents a constant value.  In the
language of CLVM, these have no distinction with each other or with integers;
the only scalar values CLVM understands are sequences of bytes.  Coupling this
into chialisp's macro system unfortunately robs it of power for this reason.

From a language perspective, chialisp's classic macros don't have access to
functions in the host program.  It's a very conservative choice in that extra
bytes in a program would be expensive if the extra functions appeared in the
finished program.  This however makes macros strange at a language level, being
self contained programs that can be used to transform each other and the host
program but that can't refer to ordinary functions from the host program.

A new keyword, `defmac`, is introduced which supercedes `defmacro`.  It works
similarly except for a few things:

- It has access to functions and constants that appear before it in lexical order.

- It is evaluated in a context where operators that can observe the user's
  lexical inputs more faithfully.
  
- It can intentionally produce objects of the same types as the user's lexical
  inputs, such as symbols, strings and numbers.
  
- It can surface errors via thrown exceptions.

Consider this classic chialisp program that contains a typo:

    (mod (W) (list W (+ W 1) (+ W2)))
    
The compiled form of this program is:

    (c 2 (c (+ 2 (q . 1)) (q 22322)))
    
Due to its use of native CLVM values, chialisp guesses at how to represent atoms,
representing the short atom X2 as 22578, which is bitwise equivalent at the CLVM
level.  Compare to this correct classic chialisp program:

    (mod (W) (list W (+ W 1) 22322))
    
The compiled form of this program is the same:

    (c 2 (c (+ 2 (q . 1)) (q 22322)))
    
Because of this, it's very difficult, once macros are in play which do the same
transformations, to distinguish what the user meant.  Once the macro has run, we
have no idea whether the user typed an identifier or a number.  I've written an
appendix that explores this at the end (Appendix: The problem of strictness in
chialisp in depth).

So what do modern `defmac` macros do?

In short, they run in a VM environment where "X" is a different value from W and
87.  Some operators treat them equivalently, but they aren't the same.  We also
introduce new operators in this environment that allow us to query and act on these
values.

Let's start with a simple program that's familiar.
--
    (mod (W) (include *strict-cl-21*) (list "W" W))

We can run this program and get the output from `brun prog.clvm '(13)'`:

    (87 13)
    
This is very similar to the classic program:

    (mod (W) (list "W" W))
    
But the output is different from `brun prog.clvm '(13)'`:

    (strlen 13)

Already, this is an improvement from the user's perspective; while the classic
program output 13 twice (because it wasn't able to distinguish "W" and W).  It
should hopefully show what motivates this, because changing the argument name
in classic would not cause any kind of obvious problem:

    (mod (WW) (list "W" W))
    
Outputs:

    (87 87)
    
But with the value aware macro system preserving the distinctions between kinds
of scalar values, the compiler can stop making the assumption that integers,
strings and identifiers are interchangable:

    (mod (WW) (include *strict-cl-21*) (list "W" W))

Leads to:

    *command*(1):46: Unbound use of W as a variable name
    
We introduced a bug and the compiler was able to catch it.  All uses of variable
names are required to match a binding when strict mode is on.  Because macros used
to make it difficult to determine whether the user actually used an identifier with
the classic macro system, there was ambiguity which meant that the compiler still
had to eventually accept misuses and couldn't distinguish mistakes from ambiguity.
The user's exact inputs are now passed through the list macro.

These new primitives are available now in defmac macros, taken from scheme:

- string? -- returns 1 if its argument is a quoted string of some kind.
- number? -- returns 1 if its argument is an integer.
- symbol? -- returns 1 if its argument is an identifier.
- string->symbol -- converts a string to a symbol
- symbol->string -- converts a symbol to a string (so it can be concatenated, etc)
- string->number -- given a decimal number represented as a string, convert it to
    a number value.
- number->string -- get the string representation of a number.
- string-append  -- string aware append function.
- string-length  -- get the length of a string.
- substring      -- get a substring of a string (as a string).

More may be on the way.

Because we now have a set of operators that can distinguish and convert the various
kinds of values the user is allowed to type as input in chialisp, we have a broader
range of things macros can do.

Imagine that we have this function:
   
   (defun quadratic (A B C X) (+ (* A X X) (* B X) C))
   
And we want something that
- Passes arguments in the "right" order by name
- Distributes any interspersed integers over the remaining arguments

So this:

   (sloppy quadratic (A B C X) X 65 A 44)
   
expands to:

   (quadratic A 65 44 X)
   
We can start simply by just making a list of the numbers:

    (mod (A X)
      (include *strict-cl-21*)
    
      (defun quadratic (A B C X) (+ (* A X X) (* B X) C))
    
      (defun make-list-of-numbers (rest)
        (if rest
          (if (number? (f rest))
            (c (f rest) (make-list-of-numbers (r rest)))
            (make-list-of-numbers (r rest))
            )
          ()
          )
        )
    
      (defmac sloppy (fun args . rest) (c 1 (make-list-of-numbers rest)))
      (sloppy quadratic (A B C X) X 65 A 44)
      )


Then we can make a list of variables too:

    (mod (A X)
      (include *strict-cl-21*)
    
      (defun quadratic (A B C X) (+ (* A X X) (* B X) C))
    
      (defun make-list-of-numbers (rest)
        (if rest
          (if (number? (f rest))
            (c (f rest) (make-list-of-numbers (r rest)))
            (make-list-of-numbers (r rest))
            )
          ()
          )
        )
    
      (defun make-list-of-variables (rest)
        (if rest
          (if (symbol? (f rest))
            (c (f rest) (make-list-of-variables (r rest)))
            (make-list-of-variables (r rest))
            )
          ()
          )
        )
    
      (defmac sloppy (fun args . rest)
        (let ((ln (make-list-of-numbers rest))
              (lv (make-list-of-variables rest)))
          (c 1 (list ln lv))
          )
        )

      (sloppy quadratic (A B C X) X 65 A 44)
      )

Then we can match the variables to the given args and substitute numbers otherwise:

    (mod (A X)
      (include *strict-cl-21*)
    
      (defun quadratic (A B C X) (+ (* A X X) (* B X) C))
    
      (defun make-list-of-numbers (rest)
        (if rest
          (if (number? (f rest))
            (c (f rest) (make-list-of-numbers (r rest)))
            (make-list-of-numbers (r rest))
            )
          ()
          )
        )
    
      (defun make-list-of-variables (rest)
        (if rest
          (if (symbol? (f rest))
            (c (f rest) (make-list-of-variables (r rest)))
            (make-list-of-variables (r rest))
            )
          ()
          )
        )
    
      (defun var-if-present (want have)
        (if have
          (if (= want (f have))
            want
            (var-if-present want (r have))
            )
          ()
          )
        )
    
      (defun sub-var-or-number (args vars nums)
        (if args
          (let ((vp (var-if-present (f args) vars)))
            (if vp
              (c vp (sub-var-or-number (r args) vars nums))
              (c (f nums) (sub-var-or-number (r args) vars (r nums)))
              )
            )
          ()
          )
        )

      ;; Given a function, its arguments and a set of arguments to call
      ;; the function with consisting of identifiers and numbers, use
      ;; in the positions that correspond with arguments that match and
      ;; use a number from the list for any argument that doesn't have
      ;; a corresponding match.
      ;;
      ;; so 
      ;;   (sloppy quadratic (A B C X) X 65 A 44)
      ;; expands to
      ;;   (quadratic A 65 44 X)
      (defmac sloppy (fun args . rest)
        (let ((ln (make-list-of-numbers rest))
              (lv (make-list-of-variables rest)))
          (c fun (sub-var-or-number args lv ln))
          )
        )

      ;; Note: chr(65) == A so if confusion was arising, we'd be creating
      ;; a conflict.
      (sloppy quadratic (A B C X) X 65 A 44)
      )
    
And we can run that `brun macro_prog.clsp '(99 77)'`:

    0x090894
    
What should happen:

    >>> A = 99
    >>> X = 77
    >>> B = 65
    >>> C = 44
    >>> hex(A * X * X + B * X + C)
    '0x90894'

So we did a lot: given some sensible input the user gave us, the name of the
function and a collection of arguments, some integers, some identifiers, we
separated out the identifiers and passed them through to the matching arguments
and took the remaining arguments from the numbers that were given.  Assuming
someone wanted this for some reason, We've enhanced the programmer's experience.

Macros can now do more
--

Consider this program:

    (mod (X)
      (include *strict-cl-21*)
    
      ;; A macro-level function to pass through only real integers.
      (defun pass-through-integers (X)
        (if (not (number? X))
          (x "not a number given to only-integers" X)
          X
          )
        )
    
      ;; A macro which at preprocessing time throws if the given argument
      ;; wasn't a lexical integer.
      (defmac only-integers (X) (pass-through-integers X))
    
      ;; Note: when macro expanding, N is the N argument to the body of
      ;; the double macro, not the integer literal, so we use the function
      ;; version of pass-through-integers in the macro body.
      (defmac double (N) (* 2 (pass-through-integers N)))
    
      ;; Here the macro form of only-integers can determine whether the
      ;; double macro produced an integer or some other expression.
      (only-integers (double 99))
      )

The macro double multiplies its argument by 2, and the function `pass-through-integers` passes the value through only if it's a number (otherwise it throws).

    ;; Compiler output
    (2 (1 1 . 198) (4 (1) 1))
    
Now let's change the last line to (double "hithere")

    ;; Error.
    *macros*(3):7-*macros*(3):63: clvm raise in (8 5 11) (() "not a number given to only-integers" "hithere")

In the future I'll make the source location available so the error can identify
the token it's throwing the exception on behalf of, but to note here is that
the macro was able to check what kind of value it got and act accordingly.

Appendix: The problem of strictness in chialisp in depth
==

We partly mitigated this in modern chialisp to preserve the locations of tokens
in the input by first saving and then swapping back hash-eqivalent subtrees of the
user's input.  So it went something like this:

We first record every subtree by its hash, which is a compatible hash with the
CLVM representation:

    Hash Table:
    0xaaabbb111 - W      (at line 1, character 16)
    0xfffccc222 - 1      (at line 1, character 23)
    0xccc333aaa - W2     (at line 1, characters 28-30)
    0x999888777 - (+ W2) (at line 1, character 25-31)
    ...
    
We run the macro:

    (list W (+ W 1) (+ W2))
    -----------------------
    (c 87 (c (+ 87 1) (c (+ 22322) ())))
    
Then we swap every item for the equivalent object from the table, if it exists:

    (c W (c (+ W 1) (c (+ W2) ())))
    
This works for the majority of uses of simple macros acceptably, to be able to
report diagnostics and such.  The more complex the subexpressions, and the more
likely they are to be reported correctly.  One can see that this is just a hack
and that there are ways in which it obviously fails spectacularly:

    (list "value" "of" "W" "is" W)
    ------------------------------
    (c "value" (c 28518 (c 87 (c 26995 (c 87 ())))))
    
Notice that "W" and W both have the same bytewise representation as the integer
constant 87.  Without the swapping reconstruction we're just left with integers
we can try to guess should be treated as identifiers in context, but with the
swapping, we're not better off since we'll get only one of "W" or W, and still not
know whether the user wanted it to be a constant or not.  In short we can't
reassemble this accurately because our table will never contain both "W" and W.
Anything we do is a guess, therefore the code that produces the executable CLVM
from this needs to accept either 87 or "W" or W as an identifier _or_ as a numeric
constant.  If a number we wanted to use happened to render as an identifier or a
string, we'd have to allow that use as a number.  This is the crux of what kept
us from having a strict mode in chialisp.
