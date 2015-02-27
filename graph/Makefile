# $Id: Makefile,v 1.2 2008/07/18 11:36:28 michiel Exp $
include ../Makefile.head

SOURCES = tod.ml   resumeforgraph.ml

OCAMLC_CFLAGS += -g
OCAMLC_LDFLAGS += -g
OCAML_INC += /usr/local/lib/ocaml/site-lib/frontc ../O_Range ../inst/lib/
OCAML_LIB += unix /usr/local/lib/ocaml/site-lib/frontc/frontc ../O_Range/orange 

$(eval $(call ocaml_prog,resumeforgraph, $(SOURCES), no_install $(PROG_FLAGS)))
$(eval $(call ocaml_lib,resumeforgraph,$(SOURCES),no_install))

OCAMLYACC_FLAGS = -v




include ../Makefile.tail



