
# pocklington command 

`pocklington [-v] [-o file] numspec`

options are:
- `-v` 			: verbose mode
- `-o file` 	: set the output in file "file"
- `numspec`:

	* directly a prime number.

	* `-next num`: generate certificate for the next prime number following
             `num`.
    
	* `-size s` : generate certificate for a prime number with a least `s`
	     digits (in base 10).
    
	* `-proth k n` : generate certificate for the Proth number : k*2^n + 1.
    
	* `-lucas n` : generate certificate for the Mersenne number 2^n - 1
	    using Lucas test (more efficient).
    
	* `-mersenne n` : generate certificate for the Mersenne number 2^n - 1
	   using Pocklington,
    
	* `-dec file` : generate certificate for the number given in file,
	    the file should also contain a partial factorization of the
	    predecessor. An example of such file for the prime 
		7237005577332262213973186563042994240857116359379907606001950938285454250989
		is the following.
		Its factors are 
		 2 × 2 × 3 × 11 × 198211423230930754013084525763697 × 
		 276602624281642239937218680557139826668747.
		In the `dec` file you need to give a big enough partial decomposition containing 
		 all the 2. For example the following one line is enough
```
7237005577332262213973186563042994240857116359379907606001950938285454250989276602624281642239937218680557139826668747 2 2
```
	     

# o2v command 

`o2v [-split] [-n name] [-o file] file.out`

options are:

- `-split`  : generate one file per certificate
- `-o file` : set the output in file "file"
- `-o name` : set the name of the final theorem "name"

# BUILD / INSTALL :

The certificate generator is included in Coq Platform, which also contains
opam files for the certificate generator and its dependencies. So installing
Coq Platform might be the easiest way to install this.

Otherwise please install dependencies:

```
	gmp     (version 6.2.1 or later)
	gmp-ecm (version 7.0 or later)
```

Please note that the gmp-ecm package provided by MacPorts is too old.

After installing the dependencies, these commands should work:

```
	cd gencertif
	autoreconf -i -s
	./configure --prefix <install-prefix> CPPFLAGS=-I%<include path> LDFLAGS=-L<library path>
	make -j 4
	make install
```

The `CPPFLAGS` and `LDFLAGS` options to configure are only required if the headers/library
for gmp and gmp-ecm are not in the default system include / library path.
This is e.g. the case for macOS MacPorts.
