ifeq ($(ls CONFIGURE),"")
  $(error Please create a CONFIGURE file defining VST_LOC and COMPCERT_LOC)
else
  include CONFIGURE
endif

CLIGHTGEN= $(COMPCERT_LOC)/clightgen

VST_DIRS= msl sepcomp veric floyd
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d)) -I . 


target: _CoqProject verif_qsort1.vo verif_qsort2.vo verif_qsort3.vo verif_qsort4.vo verif_qsort6.vo
_CoqProject: Makefile CONFIGURE
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

qsort4.v: qsort4.c
	$(CLIGHTGEN) -normalize $<

qsort5.v: qsort5.c
	$(CLIGHTGEN) -normalize $<

verif_qsort1.vo: verif_qsort1.v qsort1.vo float_lemmas.vo


clean:
	rm -f *.vo *.o .*.aux *.glob
