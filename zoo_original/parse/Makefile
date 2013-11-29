#
# Makefile generated
# by nmakegen -f -lex nlex rabbit
#

NMLC=nmlc
NMLO=nmlo
NLEX=nlex
NYACC=nyacc
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
COMPFLAGS=$(INCLUDES)
DEPFLAGS=$(INCLUDES)
LINKFLAGS=
LEXFLAGS=
YACCFLAGS=
NMAKEGEN=nmakegen
INCLUDES=

OBJ=./ast.cmo ./rabbit.cmo ./error.cmo ./fileinfo.cmo ./pattern.cmo \
    ./print.cmo ./parser.cmo ./lexer.cmo ./main.cmo 

all: $(OBJ)
	$(NMLC) $(LINKFLAGS) $(INCLUDES) -o rabbit $(OBJ)

opt: $(OBJ:.cmo=.cmx)
	$(NMLO) $(LINKFLAGS) $(INCLUDES) -o rabbit.opt $(OBJ:.cmo=.cmx)

.SUFFIXES:
.SUFFIXES: .ml .mli .n .cmo .cmi .cmx .ny .nl .mly .mll
.n.cmo:
	$(NMLC) $(COMPFLAGS) -c $<
.n.cmx:
	$(NMLO) $(COMPFLAGS) -c $<
.nl.n:
	$(NLEX) $(LEXFLAGS) $<
.ny.n:
	$(NYACC) $(YACCFLAGS) $<
.ml.cmo:
	$(NMLC) $(COMPFLAGS) -c $<
.mli.cmi:
	$(NMLC) $(COMPFLAGS) -c $<
.ml.cmx:
	$(NMLO) $(COMPFLAGS) -c $<
.mll.ml:
	$(OCAMLLEX) $(LEXFLAGS) $<
.mly.ml:
	$(OCAMLYACC) $(YACCFLAGS) $<
.mly.mli:
	$(OCAMLYACC) $(YACCFLAGS) $<

depend:
	$(NMAKEGEN) -d -f $(DEPFLAGS) 

clean::
	rm -f *.cm[iox] *.[so] *.obj *.nty rabbit rabbit.opt
	rm -f ./lexer.n ./parser.n ./parser.output

include .depend

