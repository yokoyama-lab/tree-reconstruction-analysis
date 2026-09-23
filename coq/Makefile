# Reproducible build for the formal-verification development (Rocq Prover 9.1,
# standard library only).
#
#   make               compile every module (39 .v files)
#   make check-axioms  verify the headline theorems are axiom-free
#   make clean         remove build artifacts
#
# COQBIN is auto-pointed at the Rocq 9.1 opam switch (`opam var bin`); override
# on the command line if your `rocq` lives elsewhere:
#   make COQBIN=/path/to/rocq/bin
COQBIN ?= $(shell opam var --switch=default bin 2>/dev/null)
export COQBIN
ROCQ := $(if $(strip $(COQBIN)),$(COQBIN)/rocq,rocq)

COQ_MAKEFILE := Makefile.coq

.PHONY: all clean check-axioms

all: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE)

$(COQ_MAKEFILE): _CoqProject
	"$(ROCQ)" makefile -f _CoqProject -o $(COQ_MAKEFILE)

check-axioms: all
	./check-axioms.sh

clean:
	-$(MAKE) -f $(COQ_MAKEFILE) clean
	rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf
