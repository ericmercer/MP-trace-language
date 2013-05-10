PAPER=paper
TEXS=paper.tex example-defs.tex introduction.tex example.tex smt-model.tex mp-generation.tex result.tex related-work.tex conclusion.tex complexity.tex
all: remake ${TEXS} ${PAPER}.tex ${PAPER}.pdf proof

proof: ${TEXS}
	#checkwriting $^

%.dvi: %.tex
	latex $^
	bibtex ${PAPER}

%.ps: %.dvi
	dvips -P cmz -t letter -o $@ $^

%.pdf: %.ps
	ps2pdf $^ $@

remake:
	rm -f ${PAPER}.pdf
	rm -f ${PAPER}.html

