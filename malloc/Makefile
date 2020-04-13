ifeq ($(ls CONFIGURE),"")
  $(error Please create a CONFIGURE file defining VST_LOC and COMPCERT_LOC)
else
  include CONFIGURE
endif

CLIGHTGEN= $(COMPCERT_LOC)/clightgen

VST_DIRS= msl sepcomp veric floyd
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d)) -I . 


target: _CoqProject verif_malloc1.vo verif_malloc2.vo # verif_malloc3.vo verif_malloc4.vo
_CoqProject: Makefile CONFIGURE
	@echo $(VSTFLAGS) > _CoqProject

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

malloc1.v: malloc1.c
	$(CLIGHTGEN) -normalize $<

malloc2.v: malloc2.c
	$(CLIGHTGEN) -normalize $<

malloc3.v: malloc3.c
	$(CLIGHTGEN) -normalize $<

malloc4.v: malloc4.c
	$(CLIGHTGEN) -normalize $<

verif_malloc1.vo: verif_malloc1.v malloc1.vo
verif_malloc2.vo: verif_malloc2.v malloc2.vo
verif_malloc3.vo: verif_malloc3.v malloc3.vo
verif_malloc4.vo: verif_malloc4.v malloc4.vo


clean:
	rm -f *.vo *.vo? *.o .*.aux *.glob

