Refined Remora
--------------------------------------------------------------------------------

[Remora](https://github.com/jrslepak/Remora) is a self-described
*dependently-typed language with Iverson-style implicit lifting*.

This project aims to add conservative refinements to the dependent types, in
hopes of being able to safely type functions such as `filter` or `select`.

In `Remora.hs`, you'll find data types representing Remora's indexes, sorts, and
types. You'll also find well-formedness checkers and some examples.

In `RefinedRemora.hs`, you'll find data types representing our new type system.
You'll also find a function `convert` which transforms a Remora type into a
Refined Remora type (the only refinement added is that for a natural number being
an integer greater that or equal to 0). And of course, there are well-formedness
checkers and some examples.

We use Haskell's pretty-printer; for most data types, using the function `pp` in
the repl will pretty-print for easier reading.

TODO
--------------------------------------------------------------------------------

- Finish the well-formedness checkers in `RefinedRemora.hs`.
- Write a type checker.
- Prove the usual type soundness theorems.

References
--------------------------------------------------------------------------------
- *An array-oriented language with static rank polymorphism*:
[1](http://www.ccs.neu.edu/home/jrslepak/typed-j-full.pdf)
- *Eliminating Array Bound Checking Through Dependent Types*:
[2](https://www.cs.cmu.edu/~fp/papers/pldi98dml.pdf)