# MLPolyR

This is a ML dialect with first-class cases (first-class pattern matching) and row-polymorphism
that solves the expression problem directly with language features.

## Build

Install SML/NJ, tested with v110.75 and v110.87 on Linux (make sure it has ML-lex)
and build with this command:

```
make
```

and that's it.

## Usage

There's a LaTeXed PDF manual is in `doc/`, which is excatly the same as [language spec][spec].

There are also a [compiler overview][c--], a [paper][fc-c], and a [PhD thesis][tse] about MLPolyR.

 [spec]: https://people.cs.uchicago.edu/~blume/classes/spr2005/cmsc22620/docs/langspec.pdf
 [c--]: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.210.2810&rep=rep1&type=pdf
 [tse]: https://arxiv.org/abs/0910.2654
 [fc-c]: https://people.cs.uchicago.edu/~blume/papers/icfp06.pdf

For code editing, we've created an [IntelliJ plugin][ij-p] for MLPolyR.

 [ij-p]: https://github.com/owo-lang/intellij-dtlc

## Current Status

It builds and produce PPC assembly code, which cause failure upon linking phase.

Call `mlpolyrc` with command line switch `-S` emits assembly code without linking, which is a viable option if you
only want typechecking programs. Other switches all requires linking.

Now you can call with `-t` to typecheck without doing codegen.

Now you use `-e` to eval. However, I/O operation is not yet supported, which means
all you can do is integer arith stuff.
