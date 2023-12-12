all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f .CoqMakefile.*
	rm -f CoqMakefile.conf
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f .*.aux
	rm -f *.glob
	rm -f .lia.cache
	rm -f CoqMakefile

Makefile.coq: Make
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

Make: ;

%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean