GRAPHS=
TARGET=slides.pdf
TEXFILES=*.tex
DOTFILES:=$(shell find -name '*.dot')
HELPFILES := $(DOTFILES:.dot=_dot.pdf)

all: $(TARGET)

$(TARGET): $(GRAPHS) $(TEXFILES) $(HELPFILES) Makefile

clean:
	rm -rf *.vrb *.snm *.nav *.blg *.mapleout *.bbl *.aux *.log *.out *.toc *.eps *.data *.o *.hi *.dvi *.fdb_latexmk *.fls *.tdo *.ptb *.agdai *~ $(GRAPHS) $(TARGET) $(HELPFILES)

%_dot.pdf: %.dot
	dot $< -Tpdf -o $@

%.pdf: %.tex
	pdflatex $*.tex
	pdflatex $*.tex
	pdflatex $*.tex
