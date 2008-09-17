# $Id: Makefile,v 1.3 2008/07/18 11:36:31 michiel Exp $
#Rajoute truc pour yacas.
include ../Makefile.head

SOURCES = \
	main.ml

OCAML_INC += ../../Frontc-3.2-3/frontc/frontc ../O_Range ../inst/lib/
OCAML_LIB += unix ../../Frontc-3.2-3/frontc/frontc/frontc ../O_Range/orange ../inst/lib/cyacas

$(eval $(call ocaml_prog,main,$(SOURCES)))

include ../Makefile.tail
