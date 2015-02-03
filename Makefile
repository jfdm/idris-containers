##  Makefile

IDRIS := idris
LIB   := containers
OPTS  :=

.PHONY: doc test clobber check clean lib install

install: lib
	${IDRIS} ${OPTS} --install ${LIB}.ipkg

lib:
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

clean:
	${IDRIS} --clean ${LIB}.ipkg
	${IDRIS} --clean ${BIN}.ipkg
	find . -name "*~" -delete

check: clobber
	${IDRIS} --checkpkg ${LIB}.ipkg

clobber : clean
	rm eddabin
	find . -name "*.ibc" -delete

test: install
	$(MAKE) -C test build
	(cd test; ./a.out)
	$(MAKE) -C test clean

doc:
	${IDRIS} --mkdoc ${LIB}.ipkg
