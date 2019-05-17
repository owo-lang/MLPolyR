all: compiler
	@echo all done

runtime:
	(cd rt; $(MAKE); cd ..)

compiler:
	ml-build mlpolyr.cm Main.main mlpolyr

ml-lex:
	(cd util/ml-lex; $(MAKE); cd ../..)

ml-yacc:
	(cd util/ml-yacc; $(MAKE); cd ../..)

mlpolyr.grm.sml mlpolyr.grm.sig: ml-yacc mlpolyr.grm
	util/ml-yacc/ml-yacc mlpolyr.grm

mlpolyr.lex.sml: ml-lex mlpolyr.lex
	util/ml-lex/ml-lex mlpolyr.lex

load:
	poly --eval 'PolyML.SaveState.loadState "ML_State";'

check: mlpolyr.lex.sml mlpolyr.grm.sml mlpolyr.grm.sig
	polyc -o check check.sml

ML_State: load.sml
	poly < util/save.sml
