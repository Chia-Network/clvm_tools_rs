# Types in Chialisp

Types in chialisp will add a fairly modest subset of the type system described
in and based on an implementation of the algorithms described in these papers:

## Sound and Complete Bidirectional Typechecking for Higher-Rank Polymorphism with Existentials and Indexed Types
- JANA DUNFIELD, Queen’s University, Canada
- NEELAKANTAN R. KRISHNASWAMI, University of Cambridge, United Kingdom

## Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism
- Jana Dunfield
- Neelakantan R. Krishnaswami

## Chialisp's history

Chialisp is unusual in the space of functional languages due to its history and
attempts to adhere closely to the structure of low level clvm.  Classic clvm is
unityped (having a single Atom|Pair type) and did not provide any kind of language
level wrapping for function values.  In addition, due to lisp-style argument blob
destructuring, many functions cannot fit neatly into a specific arity with each
argument in a separate arrow.  Combining all the various historical uses in
chialisp with its freewheeling nature led to idiomatic choices that, despite
everything, fit the model state of the art type theory when viewed through the
right lens.

Necessary goals for adding types to chialisp are to allow as much code to fly
under the radar of the type scheme as possible so to not disrupt much higher
cadence and higher stakes work going on above.  Like a welder working suspended
from belts below the L as trains go by above (and like the first iterations of
typescript), chialisp's type system should be able to be completely stripped out,
should be able to be ignored as only suggestions and should be able to avoid
putting more burdens than those specifically asked on typed code.

## Reasons for adding types to chialisp

The final reason chialisp is getting a type system is beacuse of momentum gained
after the audit report, but several people were thinking about it before that.
My expectation from the past year of experience is that uptake of typing in
chialisp will take place extremely gradually, probably too gradually to be
tolerable for traditional project management or tracking to tolerate.  It will
probably first be used as a diagnostic and forensic tool and debugging aid and
escape into use in real contract slowly as the feedback loop between chialisp
and authors of chialisp code reach an equlibrium on the ergonomics of both the
syntactic elements and type system as a whole.

A few things that will likely provide early benefit are synthesis of helper
functions for accessing members of fixed structures, helpers surrounding "Nullable"
objects and basic internal checking of arithmetic operators and their inputs and
outputs which can be taken ad-hoc if desired.

## Details

Chialisp's type system will evolve as users provide feedback and request ergonomic
changes, but the foundation is likely to remain very close to this:

### Primitive Types

- Functions: defuns in chialisp all have arity-1 since partial application at the
type level isn't necesarily meaningful and some types would be inexpressible
anyway.  Choosing arity-1 for all chialisp functions makes typing variable argument
lists (as in +, *, logand etc operators) easy:

    (+ : ((Atom List) -> Atom))

As such, functions cannot appear in argument lists or normal values such as pairs.
We provide an abstraction wrapper that allows us to talk about code that can be
run by the 'a' operator (consider this hypothetical addition function):

    (Exec ((Pair Atom (Pair Atom Unit)) -> Atom))

We can properly type a curry function that operates on this executable code:

    ((Pair (Exec ((Pair a b) -> x)) a) -> (Exec (b -> x)))

So it is possible to use this to let to chialisp do the vast majority of what's
expected now under a sound typing model.

- Any -- When nothing is typed in chialisp, all functions appear as 

- Unit, Atom {n} -- The unit type and an atom type with optional length.

- Pair x y -- A pair type that is the 

- Nullable x -- Without changing the representation, makes () a legal value and
requires use of some operator for extraction.  Since () is a kind of atom,
Nullable Atom should degrade properly to Atom for use in conditions and arithmetic.
Macros will be provided that serve the use of pattern matching in more commmon
functional languages in order to make Nullable practical.

- Exec x -- A simple "holder" for abstract values that prevents destructuring by
normal operators.  We can use it for various purposes.

Exec with a function type can represent executable clvm code and be used by the
'a' operator and currying functions to preserve the "executable-ness" in type
space.

Exec with a pair type can represent user data structures to the type system under
the hood.  My expectation is that Exec and Pair will be teamed up with unique
type variables to control what structures are treated as unique from each other
and which ones work with structural subtyping.  In the future, a sum type will
use this facility as well, allowing user code to have proven-exhaustive pattern
matches like in ocaml, haskell, rust etc.

## User types

The user will be able to define type aliases:

    ;; A requested feature is separating Atoms from hash-sized atoms
    ;; (Atom n) degrades to Atom but not vice versa.
    (deftype Hash (Atom 32))

    ;; The list type is defined a bit like this
    (deftype List x (Nullable (Pair x (x List))))

    ;; A HAMT is a data structure that can simulate a mutable array
    ;; in languages that don't have mutability.
    (deftype Tree x ((left : (Nullable (x Tree))) . (right : (Nullable (x Tree)))))
    
    ;; An abstract object.
    (deftype HiddenState)

These will emit accessor functions that are correctly typed for the user to use
in accessing their structs.

Escape hatches are provided that will be useful in library code when operating
directly on the underlying data of typed objects is desired.  This allows libraries
implementing any kind of data structure to provide a well type facade to user code
while not burdeing the implementation.

    ;; ('a -> 'b)
    (coerce x)
    ;; (Exec 'a -> 'a)
    (explode x)
    ;; ('a -> Exec 'a)
    (bless x)
    ;; ((Pair (Exec b) a) -> (Exec (Pair a b)))
    (lift x v)
    ;; ((Exec (Pair a b)) -> (Exec b))
    (unlift x)

Not every detail is known at this point, because engagement with users and ongoing
shaping of the ergonimics of typing in chialisp will be required.  The goal of
this stage of this is to provide a system that is maximally capable and that is
properly connected to chialisp so that it can evolve into something chialisp
authors can use with comfort to increase productivity.
