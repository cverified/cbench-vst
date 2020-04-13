ifeq ($(ls CONFIGURE),"")
  $(error Please create a CONFIGURE file defining VST_LOC and COMPCERT_LOC)
else
  include CONFIGURE
endif

CLIGHTGEN= $(COMPCERT_LOC)/clightgen

VST_DIRS= msl sepcomp veric floyd
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d)) -I . 


target: _CoqProject verif_sqrt1.vo # verif_sqrt2.vo verif_sqrt3.vo verif_sqrt4.vo
_CoqProject: Makefile CONFIGURE
	@echo $(VSTFLAGS) > _CoqProject

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

sqrt1.v: sqrt1.c
	$(CLIGHTGEN) -normalize $<

sqrt2.v: sqrt2.c
	$(CLIGHTGEN) -normalize $<

sqrt3.v: sqrt3.c
	$(CLIGHTGEN) -normalize $<

sqrt4.v: sqrt4.c
	$(CLIGHTGEN) -normalize $<

model_sqrt1.vo: model_sqrt1.v

verif_sqrt1.vo: verif_sqrt1.v sqrt1.vo model_sqrt1.vo
verif_sqrt2.vo: verif_sqrt2.v sqrt2.vo
verif_sqrt3.vo: verif_sqrt3.v sqrt3.vo
verif_sqrt4.vo: verif_sqrt4.v sqrt4.vo


clean:
	rm -f *.vo *.vo? *.o .*.aux *.glob

