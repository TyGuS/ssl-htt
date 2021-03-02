all: standard advanced
%.vo: %.v
	coqc -R ../../mczify/theories mathcomp.zify -Q ../lib SSL $<

clean:
	$(MAKE) -C standard clean
	$(MAKE) -C advanced clean

standard:
	$(MAKE) -C standard

advanced:
	$(MAKE) -C advanced

.PHONY: clean standard advanced
