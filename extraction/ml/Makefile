OCAMLMAKEFILE = OCamlMakefile
SOURCEMODULES = Datatypes Decimal Logic Bool Nat Specif Sumbool \
 Equalities Orders OrdersTac \
 NZAxioms NAxioms NBase NDefOps \
 Modules DigitModule DependentFingerTreeModule \
 FingerTreeModule StringInterface RopeModule

SOURCES = ${SOURCEMODULES:=.mli} ${SOURCEMODULES:=.ml}

LIB_PACK_NAME = Fingertrees
OCAMLFLAGS= -for-pack ${LIB_PACK_NAME} #-unsafe

OCAMLNCFLAGS= -inline 1000
RESULT = fingertrees
LIBINSTALL_FILES := $(RESULT).cmi $(RESULT).cma \
		    $(RESULT).cmxa $(RESULT).a \
	$(SOURCEMODULES:=.mli)

all: ncl

realclean:
	rm -f ${SOURCES} Extract.vo Extract.glob

install: libinstall

uninstall: libuninstall

-include ${OCAMLMAKEFILE}

