all: 
	cd Tactic; $(MAKE) all
	cd N; $(MAKE) all
	cd List; $(MAKE) all
	cd Z; $(MAKE) all
	cd PrimalityTest; $(MAKE) all
	cd num; $(MAKE) GenBase.vo
	cd num/W; $(MAKE) all
	cd num/W/W2; $(MAKE) all
	cd num/W/W8; $(MAKE) all
	cd num; $(MAKE) all

clean: 
	cd Tactic; $(MAKE) clean
	cd N; $(MAKE) clean
	cd List; $(MAKE) clean
	cd Z; $(MAKE) clean
	cd PrimalityTest; $(MAKE) clean
	cd num; $(MAKE) clean
	cd num/W; $(MAKE) clean
	cd num/W/W2; $(MAKE) clean
	cd num/W/W8; $(MAKE) clean
