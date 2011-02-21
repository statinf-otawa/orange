include ./Makefile.head

ifdef NATIVE
export NATIVE=1
endif

SUBDIRS = O_Range graph main

include  ./Makefile.tail
