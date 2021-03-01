
all: default doc

default: Makefile.coq mczify/theories/zify.vo
	make -f Makefile.coq

mczify/theories/zify.vo: mczify/theories/zify.v
	$(MAKE) -C mczify

clean: Makefile.coq
	$(MAKE) -C mczify clean
	make -f Makefile.coq clean
	rm -f Makefile.coq

examples: default
	$(MAKE) -C examples

install: Makefile.coq mczify/Makefile.coq
	make -f Makefile.coq install
	cd mczify; make -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq



.PHONY: coq clean install doc examples
