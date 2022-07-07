
all: rules.pdf hierarchy.svg pure.pdf

rules.pdf: rules.tex
	latexmk -pdf $<

hierarchy.svg: hierarchy.dot
	dot -Tsvg -o $@ $<

pure.pdf : pure.tex
	latexmk -pdf $<
