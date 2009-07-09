# $Id: Makefile,v 1.2 2008/07/18 11:36:28 michiel Exp $
include Makefile.head

# $Id: Makefile,v 1.2 2008/07/18 11:36:28 michiel Exp $


SOURCES = resumeforgraph.ml 
	
OCAMLC_CFLAGS += -g
OCAMLC_LDFLAGS += -g
OCAML_INC += ../../frontc/frontc ../O_Range ../inst/lib/
OCAML_LIB += unix ../../frontc/frontc/frontc ../O_Range/orange 

$(eval $(call ocaml_prog,resumeforgraph, $(SOURCES), no_install))
$(eval $(call ocaml_lib,resumeforgraph,$(SOURCES)))



OCAMLYACC_FLAGS = -v




include Makefile.tail


 
