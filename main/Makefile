# $Id: Makefile,v 1.3 2008/07/18 11:36:31 michiel Exp $
 

include ../Makefile.head

SOURCES = \
	main.ml
OCAMLC_FLAGS += -g
OCAMLC_LDFLAGS += -g

OCAML_INC += ../../frontc/frontc ../O_Range ../inst/lib/
OCAML_LIB += unix ../../frontc/frontc/frontc ../O_Range/orange 

$(eval $(call ocaml_prog,main,$(SOURCES)))

include ../Makefile.tail
