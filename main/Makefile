# $Id: Makefile,v 1.3 2008/07/18 11:36:31 michiel Exp $
include ../Makefile.head

SOURCES = \
	main.ml

OCAML_INC += ../../Frontc-3.2-3/frontc/frontc ../O_Range
OCAML_LIB += unix ../../Frontc-3.2-3/frontc/frontc/frontc ../O_Range/orange

$(eval $(call ocaml_prog,main,$(SOURCES)))

include ../Makefile.tail
