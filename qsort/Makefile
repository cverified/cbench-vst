CLIGHTGEN ?= clightgen

target: _CoqProject verif_qsort1.vo verif_qsort3.vo verif_qsort4.vo
_CoqProject: Makefile
	@echo $(VSTFLAGS) > _CoqProject

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

qsort1.v: qsort1.c
	$(CLIGHTGEN) -normalize $<

qsort2.v: qsort2.c
	$(CLIGHTGEN) -normalize $<

qsort3.v: qsort3.c
	$(CLIGHTGEN) -normalize $<

qsort4a.v: qsort4a.c
	$(CLIGHTGEN) -normalize $<

qsort5.v: qsort5.c
	$(CLIGHTGEN) -normalize $<

verif_qsort1.vo: verif_qsort1.v qsort1.vo float_lemmas.vo
spec_qsort3.vo: spec_qsort3.v qsort3.vo float_lemmas.vo
qsort3_aux.vo: qsort3_aux.v spec_qsort3.vo 
verif_qsort3_part1.vo: verif_qsort3_part1.v qsort3_aux.vo spec_qsort3.vo 
verif_qsort3_part2.vo: verif_qsort3_part2.v verif_qsort3_part1.vo spec_qsort3.vo 
verif_qsort3.vo: verif_qsort3.v qsort3_aux.vo verif_qsort3_part1.vo verif_qsort3_part2.vo
verif_qsort4_aux1.vo: verif_qsort4_aux1.v spec_qsort4.vo
verif_qsort4_qsort.vo: verif_qsort4_qsort.v verif_qsort4_aux1.vo spec_qsort4.vo
verif_qsort4_main.vo: verif_qsort4_main.v verif_qsort4_aux1.vo spec_qsort4.vo
verif_qsort4.vo: verif_qsort4.v spec_qsort4.vo verif_qsort4_qsort.vo verif_qsort4_main.vo
spec_qsort4.vo: spec_qsort4.v qsort4a.vo float_lemmas.vo


clean:
	rm -f *.vo *.vo? *.o .*.aux *.glob

