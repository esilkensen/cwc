all: memo.pdf

memo.pdf: memo.tex refs.bib
	pdflatex memo
	bibtex memo
	pdflatex memo
	pdflatex memo

clean:
	rm -rf *.tar.gz *.pdf *~ *.aux *.log *.bbl *.blg appendix
