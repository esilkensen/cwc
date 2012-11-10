all: proposal.pdf
	cp proposal.pdf mates-silkensen-memo.pdf
	mkdir redex-model
	cp ../*.rkt redex-model
	tar -czf mates-silkensen.tar.gz mates-silkensen-memo.pdf redex-model
	rm -rf mates-silkensen-memo.pdf redex-model

proposal.pdf: proposal.tex refs.bib
	racket make-appendix.rkt ../*.rkt
	pdflatex proposal
	bibtex proposal
	pdflatex proposal
	pdflatex proposal

clean:
	rm -rf *.tar.gz *.pdf *~ *.aux *.log *.bbl *.blg appendix
