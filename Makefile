all:
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlc -I +str -o dsl.exe ast.ml type_checker.ml parser.mli parser.ml lexer.ml main.ml

clean:
	rm -f *.cmo *.cmi lexer.ml parser.ml parser.mli dsl.exe

zip: main.ml ast.ml lexer.mll parser.mly type_checker.ml testcases
	zip project.zip main.ml ast.ml lexer.mll parser.mly type_checker.ml -r testcases
