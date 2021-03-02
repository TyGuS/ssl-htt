all: bst dll srtl

%.vo: %.v
	coqc -R ../../mczify/theories mathcomp.zify -Q ../lib SSL $<

clean:
	$(MAKE) -C bst clean
	$(MAKE) -C dll clean
	$(MAKE) -C srtl clean

bst:
	$(MAKE) -C bst

dll:
	$(MAKE) -C dll

srtl:
	$(MAKE) -C srtl

.PHONY: clean bst dll srtl
