import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import java.util.List;

public class TestXML {

    public static void main(String[] args) throws Exception {

        CharStream input = CharStreams.fromFileName(args[0]);

        XMLLexer lexer = new XMLLexer(input);

        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // NOTE - Lexing time
        long startTime = System.nanoTime();
        tokens.fill();
        long endTime = System.nanoTime();

        long duration = (endTime - startTime);
        System.out.println(duration);

        // NOTE - Parsing time
        startTime = System.nanoTime();
        XMLParser parser = new XMLParser(tokens);
        ParseTree tree = parser.document(); 
        endTime = System.nanoTime();

        duration = (endTime - startTime);
        System.out.println(duration);
    }
}
