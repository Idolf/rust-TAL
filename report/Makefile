GRAPHS=
TARGET=report.pdf
TEXFILES=*.tex */*.tex
HELPFILES=

all: $(TARGET)

$(TARGET): $(GRAPHS) $(TEXFILES) $(HELPFILES) Makefile

clean:
	rm -rf *.blg *.mapleout *.bbl *.aux *.log *.out *.toc *.eps *.data *.o *.hi *.dvi *.fdb_latexmk *.fls *.tdo *.ptb *.agdai *~ $(GRAPHS) $(TARGET)

%.svg: %.dot
	dot $*.dot -Tsvg -o $*.svg

%.png: %.dot
	dot $*.dot -Tpng -o $*.png

%.ps: %.dot
	dot $*.dot -Tps -o $*.ps

%_dot.pdf: %.dot
	dot $*.dot -Tpdf -o $*_dot.pdf

%_neato.pdf: %.dot
	neato $*.dot -Tpdf -o $*_neato.pdf

%_circo.pdf: %.dot
	circo $*.dot -Tpdf -o $*_circo.pdf

%.mapleout: %.maple
	$(HOME)/bin/maple $*.maple > $*.mapleout

%_guimaple.ps: %.maple
	mwrapper $*.maple

%_maple.ps: %.maple
	$(HOME)/bin/maple $*.maple


%_dia.eps: %.dia
	dia $*.dia -e $*_dia.eps

%_eps.pdf: %.eps
	epstopdf $*.eps -o $*_eps.pdf

%.pdf: %.tex
	pdflatex $*.tex
	bibtex $* || true
	pdflatex $*.tex
	pdflatex $*.tex

print: $(TARGET)
	cat $(TARGET) | ssh ask lp -d s2a
