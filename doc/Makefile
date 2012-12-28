
default: $(patsubst %.tex,%.pdf,$(shell ls */main.tex)) \
	tosat.pdf algo.pdf behavior.pdf

CxPfx = ../../cx

%/main.pdf: %/main.tex preamble.tex predef.tex bibliography.bib
	pdflatex -output-directory $(dir $@) $<
	bibtex $(patsubst %.pdf,%,$@)
	pdflatex -output-directory $(dir $@) $<
	pdflatex -output-directory $(dir $@) $<

%/quick.pdf: %/main.tex preamble.tex predef.tex bibliography.bib
	pdflatex -output-directory $(dir $@) $<
	cp -f $(patsubst %.tex,%.pdf,$<) $@

%/full.pdf: %/main.pdf
	cp -f $< $@

%.pdf: %.tex $(addprefix $(CxPfx)/doc/,preamble.tex predef.tex)
	env TEXINPUTS=$(CxPfx)/doc:.: pdflatex $<

.PHONY: clean
clean:
	rm -f */*.aux */*.log */*.bbl */*.blg
	rm -f *.aux *.log

.PHONY: distclean
distclean: clean
	rm -f *.pdf
	rm -f */*.pdf

