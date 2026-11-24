# TPP-2026 presentation: build commands.
#
#   make            build slides.pdf
#   make watch      rebuild slides.pdf whenever slides.tex changes
#   make check      compile the live-demo files demo/*.v with Rocq
#   make setup      create .venv/ and install Alectryon (once)
#   make clean      remove generated files
#
# How it works: write Rocq code directly in slides.tex inside
#   \begin{alectryon}{coq}{}
#   ...
#   \end{alectryon}
# blocks. Alectryon runs all blocks in ONE Rocq session (later slides see
# earlier definitions) and writes slides.annotated.tex with the proof states
# filled in; latexmk then turns that into slides.pdf.

VENV      := .venv
ALECTRYON := $(VENV)/bin/alectryon
DEMO_V    := $(wildcard demo/*.v)

.PHONY: all slides watch check setup clean

all: slides

slides: slides.pdf

slides.pdf: slides.annotated.tex nagoyatheme.sty
	latexmk -pdf -interaction=nonstopmode -halt-on-error slides.annotated.tex
	cp slides.annotated.pdf slides.pdf

slides.annotated.tex: slides.tex | $(ALECTRYON)
	$(ALECTRYON) --coq-driver=vsrocq --frontend latex --backend latex \
	  --latex-dialect pdflatex slides.tex

watch:
	@echo "Watching slides.tex (Ctrl-C to stop)"
	@while true; do $(MAKE) --no-print-directory slides; \
	  while [ slides.tex -ot slides.pdf ]; do sleep 1; done; done

check:
	@for f in $(DEMO_V); do echo "rocq compile $$f"; rocq compile -Q demo Demo $$f || exit 1; done

setup: $(ALECTRYON)

$(ALECTRYON):
	python3 -m venv $(VENV)
	$(VENV)/bin/pip install --upgrade pip
	$(VENV)/bin/pip install alectryon

clean:
	-latexmk -C slides.annotated.tex
	rm -f slides.annotated.* slides.pdf alectryon.sty pygments.sty
	rm -f demo/*.vo demo/*.vok demo/*.vos demo/*.glob demo/.*.aux
