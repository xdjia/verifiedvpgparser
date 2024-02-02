./_opam:
	opam switch create ./ --deps-only

./Data:
	rm -rf ./Data/ && mkdir Data
	cd eval_antlr/json && make token
	cd eval_antlr/xml  && make token
	cd eval_antlr/html && make token
	python token/process_json_tokens.py
	python token/process_xml_tokens.py
	python token/process_html_tokens.py

run_bench:
	cd eval_antlr/json && make eval
	cd eval_bison/json && make eval
	cd eval_antlr/xml  && make eval
	cd eval_bison/xml  && make eval
	cd eval_antlr/html && make eval
	cd eval_bison/html && make eval

run_vpg_bench:
	rm -rf results && mkdir results
	zsh eval/eval_json.sh
	zsh eval/eval_xml.sh
	zsh eval/eval_html.sh

build_pda_json:
	rm -rf dict_json/ && mkdir dict_json; dune exec ./parse/build_pda.exe json

build_pda_xml:
	rm -rf dict_xml/ && mkdir dict_xml; dune exec ./parse/build_pda.exe xml

build_pda_html:
	rm -rf dict_html/ && mkdir dict_html; dune exec ./parse/build_pda.exe html

tree_action_xml.ml : generate_semantic_actions_xml.py
	cd parse/ && rm -rf tree_action_xml.ml && python generate_semantic_actions_xml.py > tree_action_xml.ml

tree_action_json.ml : generate_semantic_actions_json.py
	cd parse/ && rm -rf tree_action_json.ml && python generate_semantic_actions_json.py > tree_action_json.ml
