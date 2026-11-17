main.pdf: main.tex $(wildcard figs/*)
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

clean:
	latexmk -C

.PHONY: clean
