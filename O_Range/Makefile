# $Id: Makefile,v 1.2 2008/07/18 11:36:28 michiel Exp $
include ../Makefile.head

# 	conditionAnalysis_test.ml \

SOURCES = \
	conditionAnalysis.ml \
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
	cextraireboucle.ml \
	tMap.ml \
	maxima.ml \
	balance.ml \
	wcee.ml \
	orange.ml 

# absClassProperty.ml\

OCAMLC_CFLAGS += -g #-p f  #profiler (fcts)
OCAMLC_LDFLAGS += -g
OCAML_INC += ../../annot-inline/frontc-evolution/frontc ../xml-light
OCAML_LIB += unix ../../annot-inline/frontc-evolution/frontc/frontc ../xml-light/xml-light


$(eval $(call ocaml_prog,orange, $(SOURCES), no_install))
$(eval $(call ocaml_lib,orange,$(SOURCES), no_install))



OCAMLYACC_FLAGS = -v




include ../Makefile.tail




