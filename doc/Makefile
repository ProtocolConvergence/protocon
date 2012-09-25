
CxPfx = ../../cx

all: tosat.pdf algo.pdf

%.pdf: %.tex $(CxPfx)/doc/preamble.tex
	env TEXINPUTS=$(CxPfx)/doc:.: pdflatex $<

.PHONY: clean
clean:
	rm -f *.aux *.log

.PHONY: distclean
distclean: clean
	rm -f *.pdf

