
default: $(patsubst %.tex,%.pdf,$(shell ls */main.tex))

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

.PHONY: clean
clean:
	rm -f */*.aux */*.log */*.bbl */*.blg

.PHONY: distclean
distclean: clean
	rm -f */*.pdf

