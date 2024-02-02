all:
	cd VPGParser/ && coq_makefile -f _CoqProject -o Makefile && make && cd -
	cd Export/ && make && cd -

doc: ./VPGParser
	coqdoc --utf8 --toc VPGParser/*.v -d ./Doc

clean:
	cd VPGParser/ && coq_makefile -f _CoqProject -o Makefile && make clean && cd -
	cd Export/ && make clean && cd -