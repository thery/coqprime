#!/bin/sh

rm -f Makefile Makefile.conf
coq_makefile -f _CoqProject -o Makefile

