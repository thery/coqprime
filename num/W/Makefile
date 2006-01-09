all: genW 
#	cd W2 ; $(MAKE) all
#	cd W8 ; $(MAKE) all


genW: genW.ml
	ocamlopt -cclib -lunix -o genW  unix.cmxa genW.ml

genfile: genW
	cd W2; ../genW 2
#	cd W8; ../genW 8

clean:
	rm -f *~ genW *.cmi *.cmo *.cmx *.o 
#	(cd W2; $(MAKE) clean)
#	(cd W8; $(MAKE) clean)

depend: 
#	(cd W2; $(MAKE) depend)
#	(cd W8; $(MAKE) depend)

