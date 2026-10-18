LAKE ?= lake
PDFLATEX ?= pdflatex
PYTHON ?= python3

.PHONY: help paper lean axioms diagnostics check
.DEFAULT_GOAL := help

help:
	@echo 'make paper        Build paper.pdf (two LaTeX passes)'
	@echo 'make lean         Build all Lean declarations'
	@echo 'make axioms       Check principal statements and print their axioms'
	@echo 'make diagnostics  Replay exact rational diagnostics through N=7'
	@echo 'make check        Run all of the above'
	@echo 'Override LAKE, PDFLATEX or PYTHON when needed.'

paper:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex > paper-build.log 2>&1
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex >> paper-build.log 2>&1

lean:
	$(LAKE) -d lean build Szkraw > lean/lake-build.log 2>&1

axioms: lean
	$(LAKE) -d lean env lean lean/CheckAxioms.lean > lean/axioms.log 2>&1

diagnostics:
	$(PYTHON) -u verify.py --max-n 7 > verification.log 2>&1

check: paper axioms diagnostics
