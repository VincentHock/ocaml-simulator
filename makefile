all: clean evaluation miniml expr tests 

evaluation: evaluation.ml
	ocamlbuild -use-ocamlfind evaluation.byte

miniml: miniml.ml
	ocamlbuild -use-ocamlfind miniml.byte

expr: expr.ml
	ocamlbuild -use-ocamlfind expr.byte

tests: tests.ml
	ocamlbuild -use-ocamlfind tests.byte

clean:
	rm -rf _build *.byte *.cmo *.cmi