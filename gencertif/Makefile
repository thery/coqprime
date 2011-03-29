ECMDIR=/usr/lib/

OPT=
CC=gcc

CFIRSTPRIMES=certif.c factorize.c firstprimes.c
OFIRSTPRIMES=$(CFIRSTPRIMES:.c=.o)

CPOCK=certif.c factorize.c pocklington.c

OPOCK=$(CPOCK:.c=.o)

pock: $(OPOCK)
	$(CC) -g -O2  -o pocklington $(OPOCK) -lecm -lgmp -lm 

first: $(OFIRSTPRIMES)
	$(CC) -g -O2 -o firstprimes $(OFIRSTPRIMES) -lecm -lgmp -lm

nextprime: nextprime.c nextprime.o
	$(CC) -g -O2  -o nextprime nextprime.o  -lecm -lgmp -lm 

all:   
	make pock
	make first
	make nextprime
	make o2v
	make o2ml

clean:
	rm -f *~ *.o pocklington firstprimes nextprime o2v


.SUFFIXES: .v .vo .c .o

.c.o:
	$(CC) -I$(GMPDIR) -I$(ECMDIR) -Wall -pedantic -c $<

o2v: parser.ml
	ocamlc -o o2v nums.cma str.cma parser.ml

o2ml: mparser.ml
	ocamlc -o o2ml nums.cma str.cma mparser.ml


