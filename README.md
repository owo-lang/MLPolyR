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

a PDF manual is in `doc/`.

There are also a [language spec][spec], a [paper][fc-c] and a [PhD thesis][tse] about MLPolyR.

 [spec]: https://people.cs.uchicago.edu/~blume/classes/spr2005/cmsc22620/docs/langspec.pdf
 [tse]: https://arxiv.org/abs/0910.2654
 [fc-c]: https://people.cs.uchicago.edu/~blume/papers/icfp06.pdf
 
 ## Current State
 
It builds and produce PPC assembly code, which cause failure upon linking pharse.

Call `mlpolyrc` with ommand line switch `-S` emits assembly code without linking, which is a viable option if you
only want typechecking programs. Other switches all requires linking.
