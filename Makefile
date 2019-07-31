##  Makefile

IDRIS := idris
LIB   := containers
TEST  := ${LIB}-test
OPTS  :=

.PHONY: doc test clobber check clean lib install

install: lib
	${IDRIS} ${OPTS} --install ${LIB}.ipkg

lib:
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

clean:
	${IDRIS} --clean ${LIB}.ipkg
	find . -name "*~" -delete

check: clobber
	${IDRIS} --checkpkg ${LIB}.ipkg
	${IDRIS} --checkpkg ${TEST}.ipkg

clobber : clean
	find . -name "*.ibc" -delete

test: clean
	${IDRIS} --testpkg ${TEST}.ipkg

doc:
	${IDRIS} --mkdoc ${LIB}.ipkg
