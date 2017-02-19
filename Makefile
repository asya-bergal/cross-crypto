MOD_NAME := CrossCrypto
SRC_DIR  := src

.PHONY: coq
coq: Makefile.coq
	./coqpath $(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	$(Q)$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
.PHONY: update-_CoqProject

update-_CoqProject::
	(echo '-R $(SRC_DIR) $(MOD_NAME)'; (git ls-files 'src/*.v' | $(SORT_COQPROJECT))) > _CoqProject

.PHONY: fcf
fcf:
	$(MAKE) -C fcf

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

.PHONY: clean-fcf
clean-fcf:
	$(MAKE) -C fcf clean

.PHONY: cleanall
cleanall: clean clean-fcf
