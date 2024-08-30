
.PHONY: all
all: freja.pdf freja-sign.pdf verificatum.pdf

# keep intermediate *.latex files
.PRECIOUS: %.latex

%.latex: %.txt
	plantuml -tlatex $<

%.pdf: %.latex
	pdflatex $<

