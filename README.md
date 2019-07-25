These are verifications by [Andrew Appel](https://www.cs.princeton.edu/~appel/) and [William Mansky](https://www.cs.uic.edu/~mansky/) of programs from the [cbench](https://github.com/cverified/cbench) benchmark
using [VST](https://vst.cs.princeton.edu).

BUILD INSTRUCTIONS:  see in each subdirectory.

POINTS CLAIMED:

|            | [VST](https://vst.cs.princeton.edu) |
|------------|----:|
| **Total**  |  35 |
| `fac1.c`   |   4 |
| `fac2.c`   |   4 |
| `fac3.c`   |   4 |
| `fac4.c`   |   4 |
| `fac6.c`   |   4 |
| `qsort1.c` |   4 |  [see note]
| `qsort3.c` |   4 |
| `qsort4.c` |   3 |  [see note]
| `cat1.c`   |   4 |  [see note]

Notes:

`qsort1.c` contains a main() with calls to printf().  At the moment, VST cannot do printf.  However, the chart in the [paper](https://arxiv.org/abs/1904.01009) lists qsort1.c as "not containing standard library calls, not containing I/O", so I assume that main() is not part of the task in qsort1.c.

`qsort4.c` uses "variable length arrays", a feature of C not supported by CompCert or by VST.  We modified one line of the program to avoid using them.

`qsort4.c` has a bug: it can call memcpy with overlapping source and destination arguments.  This is "undefined behavior" in the C standard.  Therefore our verification of qsort4 has one admitted lemma, for the case where we must assume that memcpy(dest,src,size) has no effect when dest=src.

`cat1.c` has a bug: it calls putchar() without checking the return code, and therefore its output can be lacking arbitrary missing subsequence of the intended output.  We worked around this bug by proving it to this weaker specification.
