include ./Makefile.head

ifdef NATIVE
export PROG_FLAGS=native
endif

SUBDIRS = O_Range graph main

include  ./Makefile.tail
