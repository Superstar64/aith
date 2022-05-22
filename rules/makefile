
all: aith.pdf aith.svg

aith.pdf: aith.tex
	latexmk -pdf $<

aith.svg: aith.dot
	dot -Tpng -o $@ $<
