common=common.v
proofs=$(wildcard %.v, *)
compiled_files=$(patsubst %.v,%.vo,$(filter-out $(common), $(proofs)))

default: all

common: common.v
	coqc -w none -R ../../../mczify/theories mathcomp.zify -Q ../../../lib SSL $<

%.vo: %.v common
	coqc -w none -R ../../../mczify/theories mathcomp.zify -Q ../../../lib SSL $<

clean:
	rm -f *.vo *.glob *.vo *.vok *.vos

all: $(compiled_files)

.PHONY: all clean
