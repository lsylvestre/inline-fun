CC=ocamlc

all:
	$(CC) -c inliner.ml;
	menhir parser.mly;
	$(CC) -c parser.mli;
	ocamllex lexer.mll;
	$(CC) -c lexer.ml;
	$(CC) -c parser.ml;
	$(CC) -c main.ml;
	$(CC) -o inliner inliner.cmo lexer.cmo parser.cmo main.cmo

clean:
	rm *.cmo *.cmi