import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import java.util.List;

public class TestHTML {

    public static void main(String[] args) throws Exception {

        CharStream input = CharStreams.fromFileName(args[0]);

        HTMLLexer lexer = new HTMLLexer(input);

        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // NOTE - Lexing time
        long startTime = System.nanoTime();
        tokens.fill();
        long endTime = System.nanoTime();

        long duration = (endTime - startTime);
        System.out.println(duration);

        // NOTE - Parsing time
        startTime = System.nanoTime();
        HTMLParser parser = new HTMLParser(tokens);
        ParseTree tree = parser.htmlDocument();
        endTime = System.nanoTime();

        duration = (endTime - startTime);
        System.out.println(duration);
    }
}
