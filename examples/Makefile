proofs=$(wildcard %.v, *)
compiled_files=$(patsubst %.v,%.vo,$(proofs))

default:
	@echo run "make all" to build all proofs, or make "<proof>.v" to build a specific proof.

%.vo: %.v
	coqc -R ../mczify/theories mathcomp.zify -Q ../lib SSL $<

clean:
	rm -f *.vo *.glob *.vo *.vok *.vos

all: $(compiled_files)

.PHONY: all clean
