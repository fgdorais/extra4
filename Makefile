LEANS = $(shell find Extra -name '*.lean')
TESTS = $(wildcard test/*.lean)

.PHONY: build clean

build: Extra.lean
	lake build

clean:
	-rm -fr .lake/build

Extra.lean: $(LEANS)
	find Extra -name \*.lean | env LC_ALL=C sort | sed 's/.lean//;s/\//./g;s/^/import /' > $@
