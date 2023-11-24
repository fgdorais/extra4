LEANS = $(shell find Extra -name '*.lean')
TESTS = $(wildcard test/*.lean)
LEAN_TAG = $(shell sed 's/^.*://' lean-toolchain)

.PHONY: build clean

build: Extra.lean
	lake build

clean:
	-rm -fr .lake/build

Extra.lean: $(LEANS)
	find Extra -name \*.lean | env LC_ALL=C sort | sed 's/.lean//;s/\//./g;s/^/import /' > $@

lakefile.lean: lakefile.template lean-toolchain
	sed 's/LEAN_TAG/$(LEAN_TAG)/g' $< > $@
