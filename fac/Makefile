ifeq ($(ls CONFIGURE),"")
  $(error Please create a CONFIGURE file defining VST_LOC and COMPCERT_LOC)
else
  include CONFIGURE
endif

CLIGHTGEN= $(COMPCERT_LOC)/clightgen

VST_DIRS= msl sepcomp veric floyd
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d)) -I . 


target: _CoqProject verif_fac1.vo verif_fac2.vo verif_fac3.vo verif_fac4.vo verif_fac6.vo
_CoqProject: Makefile CONFIGURE
	@echo $(VSTFLAGS) > _CoqProject

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

fac1.v: fac1.c
	$(CLIGHTGEN) -normalize $<

fac2.v: fac2.c
	$(CLIGHTGEN) -normalize $<

fac3.v: fac3.c
	$(CLIGHTGEN) -normalize $<

fac4.v: fac4.c
	$(CLIGHTGEN) -normalize $<

fac5.v: fac5.c
	$(CLIGHTGEN) -normalize $<

fac6.v: fac6.c
	$(CLIGHTGEN) -normalize $<

fac_facts.vo: fac_facts.v

verif_fac1.vo: verif_fac1.v fac1.vo fac_facts.vo
verif_fac2.vo: verif_fac2.v fac2.vo fac_facts.vo
verif_fac3.vo: verif_fac3.v fac3.vo fac_facts.vo
verif_fac4.vo: verif_fac4.v fac4.vo fac_facts.vo
verif_fac6.vo: verif_fac6.v fac6.vo fac_facts.vo


clean:
	rm -f *.vo *.o .*.aux *.glob

