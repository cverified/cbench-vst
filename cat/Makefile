ifeq ($(ls CONFIGURE),"")
  $(error Please create a CONFIGURE file defining VST_LOC and COMPCERT_LOC)
else
  include CONFIGURE
endif

CLIGHTGEN= $(COMPCERT_LOC)/clightgen

VST_DIRS= msl sepcomp veric floyd progs
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d)) -Q $(VST_LOC)/paco/src Paco -Q $(VST_LOC)/InteractionTrees/theories ITree -Q . Top


target: _CoqProject verif_cat1.vo verif_cat1a.vo verif_cat2.vo
_CoqProject: Makefile CONFIGURE
	@echo $(VSTFLAGS) > _CoqProject

%.vo: %.v
	@echo COQC $*.v
	$(COQBIN)coqc $(VSTFLAGS) $*.v

cat1.v: cat1.c
	$(CLIGHTGEN) -normalize $<

cat1a.v: cat1a.c
	$(CLIGHTGEN) -normalize $<

cat2.v: cat2.c
	$(CLIGHTGEN) -normalize $<

verif_cat1.vo: verif_cat1.v cat1.vo io_specs_rollback.vo
verif_cat1a.vo: verif_cat1a.v cat1a.vo
verif_cat1b.vo: verif_cat1b.v cat1.vo io_specs_cap.vo
verif_cat2.vo: verif_cat2.v cat2.vo fio_specs.vo


clean:
	rm -f *.vo *.vo? *.o .*.aux *.glob

