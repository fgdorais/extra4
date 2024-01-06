LEANS = $(shell find Extra -name '*.lean')
TESTS = $(wildcard test/*.lean)
ROOTS = $(shell ls -1F Extra | grep '/' | sed 's/^/Extra\//;s/\/$$/.lean/')

.PHONY: build clean

build: Extra.lean
	lake build

clean:
	-rm -fr .lake/build

Extra.lean: $(ROOTS)
	ls -1F Extra | grep '/' | env LC_ALL=C sort | sed 's/\/$$//;s/^/import Extra./' > $@

Extra/%.lean: Extra/%
	find $< -name \*.lean | env LC_ALL=C sort | sed 's/.lean//;s/\//./g;s/^/import /' > $@
