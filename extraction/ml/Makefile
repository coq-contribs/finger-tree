OCAMLMAKEFILE = OCamlMakefile
SOURCEMODULES = datatypes logic   peano specif sumbool \
	modules  \
	digitModule dependentFingerTreeModule fingerTreeModule \
	nZAxioms nZBase nZAdd nZMul nZOrder nZAddOrder nZMulOrder \
	nAxioms nBase nAdd nMul nOrder nAddOrder nMulOrder nSub \
	stringInterface ropeModule

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
	ocamldep ${SOURCES} > .depend

realclean:
	rm -f ${SOURCES} Extract.vo

install: libinstall

uninstall: libuninstall

-include .depend

-include ${OCAMLMAKEFILE}

