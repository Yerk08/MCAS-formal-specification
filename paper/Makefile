LATEX     := pdflatex
TLA2TEX   := java -cp ../tla2tools.jar tla2tex.TeX

MAIN      := main
TARGET    := paper.pdf

SRC_TEX   := abstract.tex introduction.tex related_works.tex \
             advanced_tsay_lee_framework.tex adaptation_to_transactional_memory.tex \
             strategy_for_reading_model.tex formal_methodology.tex \
             evaluation.tex conclusion.tex bibliography.tex appendix.tex

all: $(TARGET)

$(TARGET): $(MAIN).tex $(SRC_TEX)
	$(LATEX) $(MAIN).tex
	$(LATEX) $(MAIN).tex
	mv $(MAIN).pdf $(TARGET)

$(SRC_TEX): %.tex: FORCE
	@echo "Processing TLA+ blocks in $@..."
	@sed -i '1s/^/\\begin{document}\n/' $@
	@echo "\\end{document}" >> $@
	-@$(TLA2TEX) $@ || echo "WARNING: tla2tex failed for $@, continuing with original file."
	@sed -i '1d' $@
	@sed -i '$$d' $@

# Techical target for forcibly set the TLA2TEX modification
FORCE:

clean:
	rm -f *.aux *.log *.out *.toc *.old *.new $(MAIN).pdf tlatex.tex

.PHONY: all clean FORCE
