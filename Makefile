out/paper.pdf: paper.tex
	latexmk -pdf -bibtex -output-directory=out -aux-directory=out
