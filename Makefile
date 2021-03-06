%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o $@

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony
