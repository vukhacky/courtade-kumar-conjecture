PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all paper check verify update-results bundle

all: verify

paper:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error CK-paper.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error CK-paper.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error CK-paper.tex

check:
	$(PYTHON) verify.py --check-only

verify:
	$(PYTHON) verify.py --compare-summary

update-results:
	$(PYTHON) verify.py --refresh-manifest
	$(PYTHON) verify.py --update-results

bundle: verify
	$(PYTHON) verify.py --bundle CK-exact.zip
