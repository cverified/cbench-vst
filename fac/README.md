This directory contains solutions to some of the C verification benchmarks
in the paper [A benchmark for C program verification](http://www.cs.ru.nl/~freek/cbench/cbench.pdf).

## BUILD INSTRUCTIONS:

1. Install VST at some  path/to/VST
  (VST github master branch 1903b03 of May 24th, 2019 works fine)

2. Choice:
  *  Install CompCert/clightgen at some   path/to/CompCert/clightgen (CompCert 3.5 or CompCert master branch)
  *  Or, don't install clightgen, just use the parsed ASTs in fac[1-6].v

3. In this directory, create a CONFIGURE file 
    VST_LOC= path/to/VST
    COMPCERT_LOC= path/to/CompCert    (optional)

4.  "make -j"
