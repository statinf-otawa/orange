# $Id: Makefile,v 1.2 2008/07/18 11:36:28 michiel Exp $
include Makefile.head

# $Id: Makefile,v 1.2 2008/07/18 11:36:28 michiel Exp $


SOURCES = \
	cexptostr.ml \
	cvariables.ml \
	constante.ml\
	cvarabs.ml \
	coutput.ml \
	increment.ml\
	cextraireboucle.ml\
	rename.ml\
	orange.ml 
	


OCAML_INC += ../../frontc/frontc
OCAML_LIB += unix ../../frontc/frontc/frontc


$(eval $(call ocaml_prog,orange,$(SOURCES)))
$(eval $(call ocaml_lib,orange,$(SOURCES)))



OCAMLYACC_FLAGS = -v




include Makefile.tail




