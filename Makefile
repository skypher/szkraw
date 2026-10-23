LAKE ?= lake
PDFLATEX ?= pdflatex
PYTHON ?= python3

.PHONY: help paper papers lean axioms lean-kink500 axioms-kink500 diagnostics check
.DEFAULT_GOAL := help

help:
	@echo 'make paper        Build paper.pdf (two LaTeX passes)'
	@echo 'make lean         Build all Lean declarations'
	@echo 'make axioms       Check principal statements and enforce the axiom allowlist'
	@echo 'make lean-kink500 Build the optional N=500 one-kink certificate (P3; about 6 min, up to about 20 GB)'
	@echo 'make axioms-kink500  Axiom audit of that certificate'
	@echo 'make diagnostics  Replay exact rational diagnostics through N=7'
	@echo 'make check        Run all of the above'
	@echo 'Override LAKE, PDFLATEX or PYTHON when needed.'

paper:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex > paper-build.log 2>&1
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex >> paper-build.log 2>&1

# The three papers papers/p1.tex, p2.tex, p3.tex are edited directly (they were generated once from paper.tex;
# the generators papers/build_p*.py are frozen). p2 and p3 read p1.aux for cross-references, so p1 is built first.
papers:
	cd papers && for p in p1 p2 p3; do $(PDFLATEX) -interaction=nonstopmode -halt-on-error $$p.tex > $$p-build.log 2>&1 && $(PDFLATEX) -interaction=nonstopmode -halt-on-error $$p.tex >> $$p-build.log 2>&1 || exit 1; done
	cd papers && for p in p1 p2 p3; do $(PDFLATEX) -interaction=nonstopmode -halt-on-error $$p.tex >> $$p-build.log 2>&1 || exit 1; ! grep -a -q 'LaTeX Warning: \(Reference\|Citation\)' $$p.log || { echo "undefined references in $$p"; exit 1; }; done

lean:
	$(LAKE) -d lean build Szkraw > lean/lake-build.log 2>&1

axioms: lean
	$(LAKE) -d lean env lean lean/CheckAxioms.lean > lean/axioms.log 2>&1

# Optional: the N = 500 one-kink certificate of P3, checked in the kernel in four chunks (built in parallel; about
# 6 minutes and up to about 20 GB of memory). Not part of `lean`, `axioms` or `check`.
lean-kink500: lean
	$(LAKE) -d lean build Szkraw.Kink500 > lean/lake-build-kink500.log 2>&1

axioms-kink500: lean-kink500
	$(LAKE) -d lean env lean lean/CheckAxiomsKink500.lean > lean/axioms-kink500.log 2>&1

diagnostics:
	$(PYTHON) -u verify.py --max-n 7 > verification.log 2>&1

check: paper axioms diagnostics
