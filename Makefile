MOD_NAME := CrossCrypto
SRC_DIR  := src
SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

.PHONY: coq clean install fcf clean-fcf clean-all update-_CoqProject

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

update-_CoqProject::
	(echo '-R $(SRC_DIR) $(MOD_NAME)'; (git ls-files 'src/*.v' | $(SORT_COQPROJECT))) > _CoqProject

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
