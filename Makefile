SHELL = /bin/sh

interpreter: $(wildcard Arabica/*.hs)
	ghc --make Arabica/Test -package mtl-2.2.2 -o interpreter
