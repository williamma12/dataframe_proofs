#!/bin/bash

# Produce files Make and Makefile

cp -f Make.in Make

COQ_VERSION_LINE=$(coqc --version | head -1)
COQ_VERSION=`echo $COQ_VERSION_LINE | sed 's/The Coq Proof Assistant, version 8\.\([^ +]*\).*/\1/'`
DIRECTORIES="theories"

${COQBIN}coq_makefile -f Make -o Makefile
