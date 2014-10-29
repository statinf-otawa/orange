# $Id: Makefile,v 1.3 2008/07/18 11:36:31 michiel Exp $


include ../Makefile.head

SOURCES = \
	main.ml \
	version.ml
OCAMLC_FLAGS += -g
OCAMLC_LDFLAGS += -g

ifdef NATIVE
OPTIONS += native
endif
ifdef CUSTOM
OPTIONS += custom
endif

OCAML_INC += ../../frontc/frontc ../O_Range ../inst/lib/ ../graph /home/jak/src/WCET-tools/PD/xml-light
OCAML_LIB += unix str ../../frontc/frontc/frontc ../O_Range/orange ../graph/resumeforgraph /home/jak/src/WCET-tools/PD/xml-light/xml-light

$(eval $(call ocaml_prog,orange,$(SOURCES),$(OPTIONS)))

VERSION=$(shell hg log -l 1 | head -1 | cut -c 14-30)
DATE=$(shell date +%Y%m%d)
version.ml:
	echo "let version=\"\\n!!VERSION=$(VERSION) ($(DATE))!!\\n\"" > version.ml

include ../Makefile.tail
