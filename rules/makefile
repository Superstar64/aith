
all: rules.pdf hierarchy.svg pure.svg

rules.pdf: rules.tex
	latexmk -pdf $<

hierarchy.svg: hierarchy.dot
	dot -Tsvg -o $@ $<

pure.pdf : pure.tex
	latexmk -pdf $<

pure.svg : pure.pdf
	pdf2svg pure.pdf pure.svg
	python opaque.py pure.svg