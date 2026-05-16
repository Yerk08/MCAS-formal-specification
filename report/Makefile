LATEX     := pdflatex

MAIN      := main
TARGET    := report.pdf

SRC_TEX   := introduction.tex advanced_tsay_li_framework.tex \
             adaptation_to_transactional_memory.tex evaluation.tex \
             strategy_for_reading_model.tex formal_methodology.tex \
             evaluation.tex conclusion.tex tsay_li_tree_animation.tex

all: $(TARGET)

$(TARGET): $(MAIN).tex $(SRC_TEX)
	$(LATEX) $(MAIN).tex
	$(LATEX) $(MAIN).tex
	mv $(MAIN).pdf $(TARGET)

clean:
	rm -f *.aux *.dvi *.log *.out *.toc *.old *.new *.snm *.nav *.vrb $(MAIN).pdf tlatex.tex

.PHONY: all clean FORCE
