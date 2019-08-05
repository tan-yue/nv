.PHONY: test clean

default:
	dune build src/exe/main.exe

install: default
	cp _build/default/src/exe/main.exe nv

test:
	dune runtest -f --no-buffer

clean:
	dune clean
