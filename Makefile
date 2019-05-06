all: compiler
	@echo all done

runtime:
	(cd rt; $(MAKE); cd ..)

compiler:
	ml-build mlpolyr.cm Main.main mlpolyr
