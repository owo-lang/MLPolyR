all: compiler
	@echo all done

runtime:
	(cd rt; $(MAKE); cd ..)

compiler:
	ml-build mlpolyr.cm Main.main mlpolyr

load:
	poly < load.sml

check:
	polyc -o check load.sml	
