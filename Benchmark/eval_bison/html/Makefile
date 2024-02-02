default:
	clear
	rm -rf ./build
	jflex HTML.l -d build
	bison HTML.y -L java -o build/HTML.java -v
	cp Node.java ./build
	javac ./build/*.java

test_lexer:
	java -cp build Yylex test.html

test_parser:
	java -cp ./build HTML main test.html

eval: default
	zsh evaluate_bison.sh

clean:
	rm -r ./build
