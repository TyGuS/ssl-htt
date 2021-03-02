
all: default doc

default: Makefile.coq mczify/theories/zify.vo
	make -f Makefile.coq

mczify/theories/zify.vo: mczify/theories/zify.v
	$(MAKE) -C mczify

clean: Makefile.coq
	$(MAKE) -C benchmarks clean
	$(MAKE) -C mczify clean
	make -f Makefile.coq clean
	rm -f Makefile.coq

examples: default
	$(MAKE) -C examples

benchmarks: default
	$(MAKE) -C benchmarks standard

benchmarks-advanced: default
	$(MAKE) -C benchmarks advanced

install: Makefile.coq mczify/Makefile.coq
	make -f Makefile.coq install
	$(MAKE) -C mczify install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq



.PHONY: coq clean install doc examples benchmarks
