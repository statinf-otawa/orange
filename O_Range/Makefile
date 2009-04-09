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
    renamestatic.ml\
	orange.ml 
	
OCAMLC_CFLAGS += -g
OCAMLC_LDFLAGS += -g
OCAML_INC += ../../Frontc-3.2-3/frontc/frontc
OCAML_LIB += unix ../../Frontc-3.2-3/frontc/frontc/frontc


$(eval $(call ocaml_prog,orange, $(SOURCES), no_install))
$(eval $(call ocaml_lib,orange,$(SOURCES)))



OCAMLYACC_FLAGS = -v




include Makefile.tail




