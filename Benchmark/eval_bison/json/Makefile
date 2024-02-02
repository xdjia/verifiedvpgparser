default:
	clear
	rm -rf ./build
	mkdir build
	cp Node.java ./build
	jflex JSON.l -d build
	bison JSON.y -L java -o build/JSON.java 
	javac ./build/*.java

test_lexer:
	java -cp build Yylex test.json

test_parser:
	java -cp ./build JSON main test.json
	
eval: default
	zsh evaluate_bison.sh

clean:
	rm -r ./build
