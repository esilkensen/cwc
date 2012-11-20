all: mates-silkensen.pdf

memo.pdf: mates-silkensen.tex refs.bib
	pdflatex mates-silkensen
	bibtex mates-silkensen
	pdflatex mates-silkensen
	pdflatex mates-silkensen

clean:
	rm -rf *~ *.pdf *.aux *.log *.bbl *.blg
