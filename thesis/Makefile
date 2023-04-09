.PHONY: all latexmk pdflatex arxiv quick clean

# .tex files generated from .lagda files
generated = \
  agda/latex/LindenbaumTarski.tex \
  agda/latex/examples.tex \


all: thesis.tex $(generated) refs.bib
	rubber -d thesis.tex

latexmk: thesis.tex $(generated) refs.bib
	latexmk -pdfxe thesis.tex

pdflatex: thesis.tex $(generated) refs.bib
	latexmk -pdf thesis.tex

quick: thesis.tex $(generated)
	xelatex $<

$(generated) : agda/latex/%.tex : agda/%.lagda
	cd agda; agda --latex $(notdir $<)

clean:
	rubber --clean thesis.tex
	rm thesis.pdf thesis.ptb thesis.vtc 2> /dev/null || true
	find . -type f -name '*.agdai' -delete
	rm -rf agda/latex/
