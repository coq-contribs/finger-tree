OCAMLMAKEFILE = OCamlMakefile
SOURCEMODULES = Datatypes Logic Peano Specif Sumbool \
 Equalities Orders OrdersTac \
 NZAxioms NAxioms NBase NDefOps NMaxMin NProperties \
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

all: depend bcl ncl

depend: ${SOURCES}
	$(CAMLBIN)ocamldep ${SOURCES} > .depend

realclean:
	rm -f ${SOURCES} Extract.vo

install: libinstall

uninstall: libuninstall

-include .depend

-include ${OCAMLMAKEFILE}

