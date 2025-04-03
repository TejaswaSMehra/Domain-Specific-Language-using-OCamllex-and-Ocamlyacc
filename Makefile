all:
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlc -I +str -o dsl.exe ast.ml parser.mli parser.ml lexer.ml type_checker.ml eval.ml main.ml

pchk:
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlc -I +str -o pcheck.exe ast.ml parser.mli parser.ml lexer.ml type_checker.ml eval.ml parser_checker.ml

clean:
	rm -f *.cmo *.cmi lexer.ml parser.ml parser.mli dsl.exe

zip: main.ml ast.ml lexer.mll parser.mly type_checker.ml eval.ml testcases
	zip project.zip main.ml ast.ml lexer.mll parser.mly type_checker.ml eval.ml parser_checker.ml -r testcases
