MOD_NAME := CrossCrypto
SRC_DIR  := .

.PHONY: coq clean install

.DEFAULT_GOAL := coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	$(Q)$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

install: coq Makefile.coq
	$(MAKE) -f Makefile.coq install
