PAPER=paper
all: remake ${PAPER}.tex ${PAPER}.pdf proof

proof: *.tex
	checkwriting $^

%.dvi: %.tex
	slatex $^
	bibtex ${PAPER}

%.ps: %.dvi
	dvips -P cmz -t letter -o $@ $^

%.pdf: %.ps
	ps2pdf $^ $@

%.tex: %.scrbl
	raco make $^
	scribble --latex $^

%.html: %.scrbl
	raco make $^
	scribble --html $^

remake:
	rm -f ${PAPER}.pdf
	rm -f ${PAPER}.html

