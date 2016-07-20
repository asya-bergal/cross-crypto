MOD_NAME := CrossCrypto
SRC_DIR  := src

.PHONY: coq clean install fcf clean-fcf clean-all

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	$(Q)$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

clean-fcf:
	$(MAKE) -C fcf/src/FCF clean

clean-all: clean clean-fcf

install: coq Makefile.coq
	$(MAKE) -f Makefile.coq install

fcf:
	$(MAKE) -C fcf/src/FCF
