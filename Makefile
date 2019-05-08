all: compiler
	@echo all done

runtime:
	(cd rt; $(MAKE); cd ..)

compiler:
	ml-build mlpolyr.cm Main.main mlpolyr

load:
	poly --eval 'PolyML.SaveState.loadState "ML_State";'

check:
	polyc -o check load.sml	

ML_State: load.sml
	poly < util/save.sml
