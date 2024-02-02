VerifiedParser.ml: ExportOCaml.v
	coqc -R ../VPGParser VPGParser ExportOCaml.v
	printf "▷ Library Successfully Exported."
	printf "▷ VerifiedParser.ml and VerifiedParser.mli are ready.\n"

test: VerifiedParser.ml
	ocamlc VerifiedParser.mli

clean:
	rm -f *.ml *.mli *.vo *.vos *.vok *.glob .*.aux *.cmi