# Makefile for the quantitative logic project
# This will compile all relevant Coq files and
# extract a stack aware compiler with automatic
# bound analysis.
#
# This work is currently only available for the
# ia32 backend of the CompCert compiler.
#
# An appropriate path to a stack aware copy of
# CompCert must have been specified prior to
# running this Makefile.


# Settings provided by the configure script
include Makefile.config

# Compute Coq/Ocamlbuild include list
INCLUDES = $(patsubst %, -I %, $(DIRS) examples compiler .)

# Local programs and options
LNS = ln -s

COQC    = coqc -q $(INCLUDES)
COQDEP  = coqdep $(INCLUDES)
COQDOC  = coqdoc
COQEXEC = coqtop $(INCLUDES) -batch -load-vernac-source
COQCHK  = coqchk.opt $(INCLUDES)

OCAMLBUILD = ocamlbuild
OCB_OPTIONS =                     \
	-j 2                      \
	-no-hygiene               \
	-no-links                 \
	-I extraction $(INCLUDES) -I compcert/cparser -I compcert

all:
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) qccomp


proof: $(VFILES:.v=.vo) $(patsubst %.v, examples/%.vo, $(EXAMPLES))

extraction: extraction/STAMP

extraction/STAMP: $(VFILES:.v=.vo) extraction/extract.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extract.v
	touch extraction/STAMP

qccomp: extraction/STAMP
	$(OCAMLBUILD) $(OCB_OPTIONS) QDriver.native \
	&& rm -f qccomp \
	&& $(LNS) _build/compiler/QDriver.native qccomp


.PHONY: all proof extraction qccomp clean


%.vo: %.v
	@echo "COQC $*.v"
	@$(COQC) -dump-glob glob/$(*F).glob $*.v


clean:
	find -P . -path ./compcert -prune -o -name \*.vo -print | xargs rm -f
	rm -f qccomp
	rm -rf _build
	rm -rf glob/*
	# rm -f compiler/Configuration.ml
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli

distclean:
	$(MAKE) clean
	rm -f Makefile.config


.depend: $(VFILES) $(patsubst %, examples/%, $(EXAMPLES)) Makefile.config
	$(COQDEP) $^ > .depend

-include .depend
