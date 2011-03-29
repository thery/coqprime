all: 
	cd Tactic; $(MAKE) all
	cd N; $(MAKE) all
	cd List; $(MAKE) all
	cd Z; $(MAKE) all
	cd PrimalityTest; $(MAKE) all
	cd elliptic; $(MAKE) all
	cd num; $(MAKE) all

clean: 
	cd Tactic; $(MAKE) clean
	cd N; $(MAKE) clean
	cd List; $(MAKE) clean
	cd Z; $(MAKE) clean
	cd PrimalityTest; $(MAKE) clean
	cd elliptic; $(MAKE) clean
	cd num; $(MAKE) clean



