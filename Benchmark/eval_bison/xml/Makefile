default:
	clear
	rm -rf ./build
	mkdir build
	cp ParseTree.java ./build
	cp Node.java ./build
	jflex XML.l -d build
	bison XML.y -L java -o build/XML.java 
	javac ./build/*.java

test_lexer:
	java -cp build Yylex test.xml

test_parser:
	java -cp ./build XML main test.xml
	java -cp ./build XML main ~/Sync/xml_files/xmls/po.xml

eval: default
	zsh evaluate_bison.sh

clean:
	rm -r ./build
