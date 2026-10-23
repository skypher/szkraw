LAKE ?= lake
PDFLATEX ?= pdflatex
PYTHON ?= python3

.PHONY: help paper papers lean axioms diagnostics check
.DEFAULT_GOAL := help

help:
	@echo 'make paper        Build paper.pdf (two LaTeX passes)'
	@echo 'make lean         Build all Lean declarations'
	@echo 'make axioms       Check principal statements and enforce the axiom allowlist'
	@echo 'make diagnostics  Replay exact rational diagnostics through N=7'
	@echo 'make check        Run all of the above'
	@echo 'Override LAKE, PDFLATEX or PYTHON when needed.'

paper:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex > paper-build.log 2>&1
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex >> paper-build.log 2>&1

# The three papers (papers/p1.tex, p2.tex, p3.tex) are generated from paper.tex by papers/build_p*.py;
# p2 and p3 read p1.aux for cross-references, so p1 is built first.
papers:
	cd papers && $(PYTHON) build_p1.py && $(PYTHON) build_p2.py && $(PYTHON) build_p3.py
	cd papers && for p in p1 p2 p3; do $(PDFLATEX) -interaction=nonstopmode -halt-on-error $$p.tex > $$p-build.log 2>&1 && $(PDFLATEX) -interaction=nonstopmode -halt-on-error $$p.tex >> $$p-build.log 2>&1 || exit 1; done
	cd papers && for p in p1 p2 p3; do $(PDFLATEX) -interaction=nonstopmode -halt-on-error $$p.tex >> $$p-build.log 2>&1 || exit 1; ! grep -a -q 'LaTeX Warning: \(Reference\|Citation\)' $$p.log || { echo "undefined references in $$p"; exit 1; }; done

lean:
	$(LAKE) -d lean build Szkraw > lean/lake-build.log 2>&1

axioms: lean
	$(LAKE) -d lean env lean lean/CheckAxioms.lean > lean/axioms.log 2>&1

diagnostics:
	$(PYTHON) -u verify.py --max-n 7 > verification.log 2>&1

check: paper axioms diagnostics
