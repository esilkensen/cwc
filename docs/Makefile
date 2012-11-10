all: proposal.pdf

proposal.pdf: proposal.tex refs.bib
	racket make-latex.rkt ../*.rkt
	pdflatex proposal
	bibtex proposal
	pdflatex proposal
	pdflatex proposal

clean:
	rm -rf proposal.pdf *~ *.aux *.log appendix
