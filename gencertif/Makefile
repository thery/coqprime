ECMDIR=/usr/local/lib/

OPT=
CC=gcc

CFIRSTPRIMES=certif.c factorize.c firstprimes.c
OFIRSTPRIMES=$(CFIRSTPRIMES:.c=.o)

CPOCK=certif.c factorize.c pocklington.c

OPOCK=$(CPOCK:.c=.o)

pock: $(OPOCK)
	$(CC) -g -O2  -o pocklington $(OPOCK) $(ECMDIR)libecm.a -lgmp -lm 

first: $(OFIRSTPRIMES)
	$(CC) -g -O2 -o firstprimes $(OFIRSTPRIMES) $(ECMDIR)libecm.a -lgmp -lm

nextprime: nextprime.c nextprime.o
	$(CC) -g -O2  -o nextprime nextprime.o  $(ECMDIR)libecm.a -lgmp -lm 

all: 
	make pock
	make first

clean:
	rm -f *~ *.o pocklington firstprimes


.SUFFIXES: .v .vo .c .o

.c.o:
	$(CC) -I$(GMPDIR) -I$(ECMDIR) -Wall -pedantic -c $<


