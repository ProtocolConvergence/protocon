
all: tosat.pdf

%.pdf: %.tex preamble.tex
	pdflatex $<

.PHONY: clean
clean:
	rm -f *.aux *.log

.PHONY: distclean
distclean: clean
	rm -f *.pdf

