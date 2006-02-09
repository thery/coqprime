all: genfile
#	cd W2 ; $(MAKE) all
#	cd W8 ; $(MAKE) all


genW: genW.ml
	ocamlopt -cclib -lunix -o genW  unix.cmxa genW.ml

genfile: genW
	cd W2; ../genW 2 -noproof
	cd W8; ../genW 8 -noproof
	echo ok >> genfile

clean:
	rm -f *~ genW *.cmi *.cmo *.cmx *.o 
#	(cd W2; $(MAKE) clean)
#	(cd W8; $(MAKE) clean)

depend: 
#	(cd W2; $(MAKE) depend)
#	(cd W8; $(MAKE) depend)

