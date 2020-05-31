default: pdf

pdf: 
	lhs2TeX --agda paper.lhs > paper.tex
	pdflatex paper
	pdflatex paper
	bibtex paper
	sleep 1
	pdflatex paper
	sleep 1
	pdflatex paper

clean:
	rm -rf paper.aux paper.bbl paper.blg paper.log paper.out paper.pbt paper.spl paper.tex
