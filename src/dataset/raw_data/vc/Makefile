COQMFFLAGS := -Q . VC  

ALLVFILES := sumarray.v reverse.v append.v stack.v strlib.v hash.v hints.v stdlib.v stdlib2.v stack2.v triang2.v main2.v Preface.v Verif_sumarray.v Verif_reverse.v Verif_stack.v Verif_triang.v Verif_append1.v Verif_append2.v Verif_strlib.v Hashfun.v Verif_hash.v VSU_intro.v Spec_stack.v Spec_triang.v Spec_stdlib.v VSU_stack.v VSU_triang.v VSU_stdlib.v VSU_main.v VSU_stdlib2.v VSU_main2.v Postscript.v Bib.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
