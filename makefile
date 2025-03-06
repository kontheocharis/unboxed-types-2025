runlatex: *
	latexmk
	rm missfont.log || true
	cp .out/main.pdf $$(basename $$(pwd)).pdf
