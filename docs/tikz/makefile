all: fuzzer.tex murxla.tex makefile
	latexmk -pdf fuzzer.tex
	pdftoppm -png -r 600 fuzzer.pdf > fuzzer.png
	latexmk -pdf murxla.tex
	pdftoppm -png -r 600 murxla.pdf > murxla.png

clean:
	latexmk -C
	rm fuzzer.png
	rm murxla.png
