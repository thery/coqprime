ECMDIR=/usr/lib/

OPT=
CC=gcc

CFIRSTPRIMES=certif.c factorize.c firstprimes.c
OFIRSTPRIMES=$(CFIRSTPRIMES:.c=.o)

CPOCK=certif.c factorize.c pocklington.c

OPOCK=$(CPOCK:.c=.o)

all:   
	make pock
	make first
	make o2v

pock: $(OPOCK)
	$(CC) -g -O2  -o pocklington $(OPOCK) -lecm -lgmp -lm 

first: $(OFIRSTPRIMES)
	$(CC) -g -O2 -o firstprimes $(OFIRSTPRIMES) -lecm -lgmp -lm


clean:
	rm -f *~ *.o *.cmo *.cmi pocklington firstprimes o2v 


.SUFFIXES: .v .vo .c .o

.c.o:
	$(CC) -I$(GMPDIR) -I$(ECMDIR) -Wall -pedantic -c $<

o2v: parser.ml
	ocamlc -o o2v nums.cma str.cma parser.ml


