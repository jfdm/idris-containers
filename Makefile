##  Makefile

IDRIS := idris
LIB   := containers
OPTS  :=

# N.B. The ordering in DEPS is significant.
DEPS     := ziman/lightyear jfdm/idris-testing
DEPS_DIR ?= deps

.PHONY: doc test clobber check clean lib install install-deps

install: lib
	${IDRIS} ${OPTS} --install ${LIB}.ipkg

install-deps: $(DEPS_DIR)

$(DEPS_DIR):
	mkdir -p $@
	./install-deps.sh $@ $(DEPS)

lib: install-deps
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

clean:
	${IDRIS} --clean ${LIB}.ipkg
	find . -name "*~" -delete

check: clobber
	${IDRIS} --checkpkg ${LIB}.ipkg

clobber: clean
	find . -name "*.ibc" -delete

test: clean
	${IDRIS} --testpkg ${LIB}.ipkg

doc:
	${IDRIS} --mkdoc ${LIB}.ipkg
