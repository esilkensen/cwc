all: proposal.pdf

proposal.pdf: proposal.tex refs.bib
	racket make-appendix.rkt ../*.rkt
	pdflatex proposal
	bibtex proposal
	pdflatex proposal
	pdflatex proposal

clean:
	rm -rf *.tar.gz *.pdf *~ *.aux *.log *.bbl *.blg appendix
