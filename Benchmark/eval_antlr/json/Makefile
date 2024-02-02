ANTLR="../antlr-4.11.1-complete.jar"

default:
	clear
	rm -rf antlr_build
	java -cp $(ANTLR) org.antlr.v4.Tool -o antlr_build/ *.g4
	cp TestJSON.java ./antlr_build/
	javac -cp $(ANTLR) antlr_build/*.java

test:
	zsh test.sh

token:
	zsh generate_tokens.sh

eval: default
	zsh evaluate_antlr.sh

clean:
	rm -r ./build
