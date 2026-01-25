# Makefile for de Finetti formalization paper

MAIN = main
LATEX = pdflatex
BIBTEX = bibtex

.PHONY: all clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex refs.bib sections/*.tex appendices/*.tex
	$(LATEX) $(MAIN)
	$(BIBTEX) $(MAIN)
	$(LATEX) $(MAIN)
	$(LATEX) $(MAIN)

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc *.fls *.fdb_latexmk *.synctex.gz
	rm -f sections/*.aux appendices/*.aux

distclean: clean
	rm -f $(MAIN).pdf
