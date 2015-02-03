##  Makefile

IDRIS := idris
BIN   := test
EXE   := a.out
OPTS  :=

.PHONY: clean build

build:
	${IDRIS} ${OPTS} --build ${BIN}.ipkg

clean:
	${IDRIS} --clean ${BIN}.ipkg
	find . -name "*~" -delete
	rm -rf a.out
