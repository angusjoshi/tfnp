# Build the balanced-point note. Requires latexmk + a TeX distribution.
# All build artefacts go under $(OUTDIR), which is gitignored.

MAIN   := balanced
OUTDIR := build
LATEXMK := latexmk
LATEXMK_FLAGS := -pdf -interaction=nonstopmode -halt-on-error -outdir=$(OUTDIR)

.PHONY: all watch clean

all: $(OUTDIR)/$(MAIN).pdf

$(OUTDIR)/$(MAIN).pdf: $(MAIN).tex
	$(LATEXMK) $(LATEXMK_FLAGS) $(MAIN).tex

# Continuous rebuild on save.
watch:
	$(LATEXMK) $(LATEXMK_FLAGS) -pvc $(MAIN).tex

# Remove the entire output directory.
clean:
	$(LATEXMK) -C -outdir=$(OUTDIR) $(MAIN).tex 2>/dev/null || true
	rm -rf $(OUTDIR)
