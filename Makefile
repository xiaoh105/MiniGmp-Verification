CURRENT_DIR=.
SETS_DIR = sets
COMPCERT_DIR = compcert_lib
PV_DIR = pv
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

PV_FLAG = -R $(PV_DIR) PV -R $(SETS_DIR) SetsClass -R $(COMPCERT_DIR) compcert.lib

SETS_FLAG = -R $(SETS_DIR) SetsClass

COMPCERT_FLAG = -R $(COMPCERT_DIR) compcert.lib

GMP_FLAG = $(shell grep -E '^-([RQ])' _CoqProject)

DEP_FLAG = $(GMP_FLAG)

SETS_FILE_NAMES = \
   SetsClass.v SetsDomain.v SetElement.v RelsDomain.v SetElementProperties.v SetProd.v SetsClass_AxiomFree.v SetsDomain_Classic.v
   
SETS_FILES=$(SETS_FILE_NAMES:%.v=$(SETS_DIR)/%.v)
   
COMPCERT_FILE_NAMES = \
    Coqlib.v Integers.v Zbits.v
    
COMPCERT_FILES=$(COMPCERT_FILE_NAMES:%.v=$(COMPCERT_DIR)/%.v)

PV_FILE_NAMES = \
  Intro.v SimpleProofsAndDefs.v InductiveType.v \
  Syntax.v RecurProp.v ExprIntDenotation.v ExprBoolDenotation.v BuiltInNat.v \
  Logic.v RelsAsDenotations.v FixedPoint.v \
  HoareLogic.v Monad.v BuiltInList.v

PV_FILES=$(PV_FILE_NAMES:%.v=$(PV_DIR)/%.v)

GMP_FILES = \
	./projects/lib/GmpAux.v ./projects/lib/GmpNumber.v \
	./projects/lib/gmp_goal.v

FILES = $(PV_FILES) \
  $(GMP_FILES)
			
$(PV_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(GMP_FLAG) $<

$(GMP_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(GMP_FLAG) $<

all: $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob
	@rm -f *.vo */*.vo
	@rm -f *.vok */*.vok
	@rm -f *.vos */*.vos 
	@rm -f .*.aux */.*.aux
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend
