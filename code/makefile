%.cmi: %.mli
	ocamlc -c $^ -o $@

%.cmo: %.ml
	ocamlc -c $^ -o $@

test: prop.cmo
	ocamlc $< -o $@
