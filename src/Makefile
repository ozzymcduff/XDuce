DEBUG = false

ifeq ($(OSTYPE),cygwin)
  SUFFIX = .exe
else
  SUFFIX =
endif

TARGET = xduce$(SUFFIX)
OPTTARGET = xduce.opt$(SUFFIX)

ADDONOBJS = $(shell ls addon/*.ml) 
BIBTEXOBJS = bibtex/bibtex.cmo bibtex/bibtex_lexer.cmo \
bibtex/bibtex_parser.cmo bibtex/latex_accents.cmo
UTILOBJS = util/printing.cmo util/filing.cmo \
util/counter.cmo util/timer.cmo \
util/listutil.cmo \
util/sortedlist.cmo util/nonduplist.cmo \
util/setutil.cmo
COREOBJS = \
pref.cmo finfo.cmo \
base.cmo sym.cmo ns.cmo label.cmo \
syn.cmo  ctx.cmo synutil.cmo typath.cmo \
bltin.cmo $(ADDONOBJS:.ml=.cmo) \
htype.cmo \
typeop.cmo \
desugtype.cmo \
patmatch.cmo \
wf.cmo check.cmo eval.cmo \
lexer.cmo top.cmo parsedtd.cmo parser.cmo main.cmo
OBJS = $(BIBTEXOBJS) $(UTILOBJS) $(COREOBJS) 


INCLUDES = -I util -I bibtex -I addon
PACKAGES = -package str -package unix -package netstring   -package pxp
OCAMLFLAGS = $(INCLUDES) -g 
#OCAMLOPTFLAGS = $(INCLUDES) -p
OCAMLOPTFLAGS = $(INCLUDES) 
RUNFLAGS = 
#RUNFLAGS = -show -echo
STDLIBDIR = $(shell pwd)/../lib

ifeq ($(DEBUG),true)
 EXECUTABLE = $(TARGET)
 LINKFLAGS = -g 
else
 EXECUTABLE = $(OPTTARGET)
# OPTLINKFLAGS = -p
 OPTLINKFLAGS = 
endif

OCAMLC = ocamlfind ocamlc $(PACKAGES) -linkpkg
OCAMLCI = ocamlfind ocamlc $(PACKAGES) -linkpkg
OCAMLOPT = ocamlfind ocamlopt $(PACKAGES) -linkpkg
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLDEP = ocamldep

.SUFFIXES: .ml .mli .cmo .cmi .cmx .q .qout

all: $(EXECUTABLE)

$(TARGET): $(OBJS)
	$(OCAMLC) -custom -o $@ $(LINKFLAGS) $(WITH_UNIX) $(OBJS) $(INCLUDES)

$(OPTTARGET): $(OBJS:.cmo=.cmx)
	$(OCAMLOPT) -o $@ $(OPTLINKFLAGS) $(WITH_UNIX:.cma=.cmxa) $(OBJS:.cmo=.cmx) $(INCLUDES) 

debug:
	make DEBUG=true

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLCI) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

lexer.ml lexer.mli: lexer.mll parser.cmi
	$(OCAMLLEX) $<

parser.ml parser.mli: parser.mly
	$(OCAMLYACC) -v $<

bibtex/bibtex_lexer.ml: bibtex/bibtex_lexer.mll bibtex/bibtex_parser.cmi
	$(OCAMLLEX) $<

bibtex/latex_accents.ml: bibtex/latex_accents.mll
	$(OCAMLLEX) $<

bibtex/bibtex_parser.ml bibtex/bibtex_parser.mli: bibtex/bibtex_parser.mly
	$(OCAMLYACC) -v $<

pref.ml: pref.mlp
	sed -e 's|%%LIBDIR%%|$(STDLIBDIR)|' \
	    -e 's|%%VERSION%%|$(RELEASE)|' \
	    pref.mlp > pref.ml

addon/loadsmlng.ml: addon/loadsmlng.mll 
	$(OCAMLLEX) $<

dep:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml util/*.ml util/*.mli bibtex/*.ml bibtex/*.mli addon/*.ml addon/*.mli >.depend

clean:
	-rm *.cmx *.cmo *.cmi *.o lexer.ml parser.ml parser.mli
	-rm core *~ TAGS *.output gmon.out
	-rm pref.ml $(TARGET) $(OPTTARGET) 
	-$(MAKE) -C bibtex clean
	-$(MAKE) -C util clean
	-$(MAKE) -C addon clean

tags:
	find . -name "*.ml" -print | xargs etags -a
	find . -name "*.mli" -print | xargs etags -a
	find . -name "*.mly" -print | xargs etags -a
	find . -name "*.mll" -print | xargs etags -a

dispdep:
	ocamldep *.ml | ocamldot | dot -Tps | gv -

include .depend

test:
	$(MAKE) -C .. test
