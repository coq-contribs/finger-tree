OCAMLMAKEFILE = ../OCamlMakefile
SOURCES = strings.ml strings.mli

INCDIRS=.. /sw/lib/ocaml
LIBDIRS=.. /sw/lib/ocaml

LIBS= ../fingertrees
RESULT = icfp
# OCAMLFLAGS= -unsafe
OCAMLNCFLAGS= -inline 1000

all: depend pbc pnc

depend: ${SOURCES}
	ocamldep ${SOURCES} > .depend

-include .depend

-include ${OCAMLMAKEFILE}

