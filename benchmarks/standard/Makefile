proofs=$(wildcard %.v, *)
compiled_files=$(patsubst %.v,%.vo,$(proofs))

all: ints sll sll-bounds dll tree

%.vo: %.v
	coqc -R ../../mczify/theories mathcomp.zify -Q ../lib SSL $<

clean:
	$(MAKE) -C ints clean
	$(MAKE) -C sll clean
	$(MAKE) -C sll-bounds clean
	$(MAKE) -C dll clean
	$(MAKE) -C tree clean

ints:
	$(MAKE) -C ints

sll:
	$(MAKE) -C sll

sll-bounds:
	$(MAKE) -C sll

dll:
	$(MAKE) -C dll

tree:
	$(MAKE) -C tree

.PHONY: clean ints sll sll-bounds dll tree
