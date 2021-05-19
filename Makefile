SHELL = /bin/sh

interpreter: FORCE
	ghc --make Arabica/Test -package mtl-2.2.2 -o interpreter

# Korzystam z opcji make ghc zamiast tradycyjnego makefile ze względu na zalety wymienione tutaj:
# https://downloads.haskell.org/~ghc/5.02.3/docs/set/make-mode.html
FORCE: ;
