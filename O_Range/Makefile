# $Id: Makefile,v 1.2 2008/07/18 11:36:28 michiel Exp $
include ../Makefile.head

SOURCES = \
	cexptostr.ml \
	cvariables.ml \
	constante.ml\
	coutput.ml \
	rename.ml\
	util.ml\
	extractinfoPtr.ml\
	cvarabs.ml \
	interval.ml \
	increment.ml\
    covariance.ml \
	cextraireboucle.ml\
	orange.ml 

# absClassProperty.ml\
	
OCAMLC_CFLAGS += -g
OCAMLC_LDFLAGS += -g
OCAML_INC += ../../frontc/frontc
OCAML_LIB += unix ../../frontc/frontc/frontc


$(eval $(call ocaml_prog,orange, $(SOURCES), no_install))
$(eval $(call ocaml_lib,orange,$(SOURCES), no_install))



OCAMLYACC_FLAGS = -v




include ../Makefile.tail




