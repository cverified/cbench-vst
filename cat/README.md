This directory contains solutions to some of the C verification benchmarks
in the paper [A benchmark for C program verification](http://www.cs.ru.nl/~freek/cbench/cbench.pdf).

For cat1, there is a choice of three solutions.
`cat1.c` and `verif_cat1.v` use the code as written, but the spec isn't what we might expect: because `putchar` may fail, the program may drop input characters arbitrarily.
`cat1a.c` and `verif_cat1a.v` modify the code to check for failing `putchar`, and guarantee correct cat behavior.
`verif_cat1b.v` uses the code as written, but assumes that the OS has guaranteed that all the `putchar`s will succeed. It's not yet clear what the OS will need to do to guarantee this.

## BUILD INSTRUCTIONS:

Notes:
- Unlike all the sibling directories (fac,qsort,malloc,sqrt), which work in the standard opam installation of VST 2.13, this one requires components of VST 2.13 that are not in the standard opam distribution.  So you'll have to build a special installation of VST 2.13.
- VST 2.13's Makefile requires CompCert 3.12, but if you have CompCert 3.13 it will work fine, you just need to set IGNORECOMPCERTVERSION
- at the moment, verif_cat2.v does not build

1. Install VST at some  path/to/VST
 cd path/to/VST
 git submodule update --init --recursive
 make IGNORECOMPCERTVERSION=true depend  
 make IGNORECOMPCERTVERSION=true floyd floyd/io_events.vo floyd/printf.vo progs64/io_specs.vo

2. Choice:
  * If you are in an opam switch with CompCert clightgen installed, no action necessary, the Makefile will find it in the right place
  *  Install CompCert/clightgen at some   path/to/CompCert/clightgen (CompCert 3.12 or 3.13)
  *  Or, don't install clightgen, just use the parsed ASTs in cat*.v

3. In this directory, create a CONFIGURE file 
    VST_LOC= path/to/VST
    COMPCERT_LOC= path/to/CompCert    (optional)

4.  "make -j"
