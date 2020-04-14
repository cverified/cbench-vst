These are verifications by [Andrew Appel](https://www.cs.princeton.edu/~appel/) and [William Mansky](https://www.cs.uic.edu/~mansky/) of programs from the [cbench](https://github.com/cverified/cbench) benchmark
using [VST](https://vst.cs.princeton.edu).  Functional model of sqrt1 program proved correct by [Yves Bertot](https://www-sop.inria.fr/members/Yves.Bertot/).

BUILD INSTRUCTIONS:  see in each subdirectory.

POINTS CLAIMED:

|            | [VST](https://vst.cs.princeton.edu) | |
|:-----------|----:|:--------|
| **Total**  |  47 |         |
| `fac1.c`   |   4 | (Appel) |
| `fac2.c`   |   4 | (Appel) |
| `fac3.c`   |   4 | (Appel) |
| `fac4.c`   |   4 | (Appel) |
| `fac6.c`   |   4 | (Appel) |
| `qsort1.c` |   4 | (Appel) [see note] |
| `qsort3.c` |   4 | (Appel) |
| `qsort4.c` |   3 | (Appel) [see note] |
| `cat1.c`   |   4 | (Mansky) [see note] |
| `cat2.c`   |   4 | (Mansky) |
| `malloc1.c`|   4 | (Appel) |
| `sqrt1.c`  |   4 | (Appel & Bertot) [see note] |

Notes:

`qsort1.c` contains a main() with calls to printf().  At the moment, VST cannot do printf.  However, the chart in the [paper](https://arxiv.org/abs/1904.01009) lists qsort1.c as "not containing standard library calls, not containing I/O", so I assume that main() is not part of the task in qsort1.c.

`qsort4.c` uses "variable length arrays", a feature of C not supported by CompCert or by VST.  We modified one line of the program to avoid using them.

`qsort4.c` has a bug: it can call memcpy with overlapping source and destination arguments.  This is "undefined behavior" in the C standard.  Therefore our verification of qsort4 has one admitted lemma, for the case where we must assume that memcpy(dest,src,size) has no effect when dest=src.

`qsort4.c` has calls to printf in main(); these are not verified, since the paper lists 
 qsort4.c as "not containing standard library calls, not containing I/O".

`cat1.c` has a bug: it calls putchar() without checking the return code, and therefore its output can be lacking arbitrary missing subsequence of the intended output.  We worked around this bug by proving it to this weaker specification.

`sqrt1.c` verification is just for newton_sqrt(), not for main().  Still need to link the C-to-functional-model proof to the correctness-of-functional-model proof, but this should not be difficult.

