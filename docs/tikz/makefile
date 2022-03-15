all: fuzzer.tex makefile
	latexmk -pdf fuzzer.tex
	pdftoppm -png -r 600 fuzzer.pdf > fuzzer.png

clean:
	latexmk -C
	rm fuzzer.png
