ifeq ($(ls CONFIGURE),"")
  $(error Please create a CONFIGURE file defining VST_LOC and COMPCERT_LOC)
else
  include CONFIGURE
endif

CLIGHTGEN= $(COMPCERT_LOC)/clightgen

VST_DIRS= msl sepcomp veric floyd progs
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d)) -Q $(VST_LOC)/InteractionTrees/theories ITree -I .


target: _CoqProject verif_cat1.vo
_CoqProject: Makefile CONFIGURE
	@echo $(VSTFLAGS) > _CoqProject

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

cat1.v: cat1.c
	$(CLIGHTGEN) -normalize $<

verif_cat1.vo: verif_cat1.v cat1.vo


clean:
	rm -f *.vo *.o .*.aux *.glob

