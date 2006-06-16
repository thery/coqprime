OCAMLC=ocamlc 
OCAMLOPT=ocamlopt 
OCAMLDEP=ocamldep 
OCAMLLIB=eval ocamlc -where

GENML = datatypes.ml logic.ml peano.ml \
        binPos.ml binNat.ml binInt.ml \
        zmisc.ml zpower.ml basic_type.ml \
        genBase.ml genDivn1.ml genSqrt.ml genLift.ml \
        znZ.ml zn2Z.ml genWord.ml mod_op.ml 

GENMLI=$(GENML:.ml=.mli)

MLSOURCES=$(GENML) w31C.ml w64C.ml testlucas.ml

CMX=$(MLSOURCES:.ml=.cmx)
CM0=$(MLSOURCES:.ml=.cmo)


testlucas: $(CMX) uint31C.o uint64C.o
	$(OCAMLOPT) -o testlucas nums.cmxa uint31C.o uint64C.o $(CMX) 

testlucas.byte: $(CM0) uint31C.o uint64C.o
	$(OCAMLC) -o testlucas.byte nums.cma -custom uint31C.o uint64C.o $(CM0) 

uint31C.o: uint31C.c
	$(OCAMLOPT) -c uint31C.c

uint64C.o: uint64C.c
	$(OCAMLOPT) -c uint64C.c

clean_gen:
	rm -f $(GENML) $(GENMLI)  *~ 

clean_comp:
	rm -f test31C test64 *.cmi *.cmx *.o *~ *~

clean: clean_gen clean_comp

.SUFFIXES:  .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) -c  $<

.mli.cmi:
	$(OCAMLC)  -c $<

.ml.cmx:
	$(OCAMLOPT) -c $<


depend:
	$(OCAMLDEP) *.ml *.mli > .depend

include .depend
