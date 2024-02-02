import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import java.util.List;

public class TestJSON {

    public static void main(String[] args) throws Exception {

        CharStream input = CharStreams.fromFileName(args[0]);

        JSONLexer lexer = new JSONLexer(input);

        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // NOTE - Lexing time
        long startTime = System.nanoTime();
        tokens.fill();
        long endTime = System.nanoTime();

        long duration = (endTime - startTime);
        System.out.println(duration);

        // NOTE - Parsing time
        startTime = System.nanoTime();
        JSONParser parser = new JSONParser(tokens);
        ParseTree tree = parser.json(); 
        endTime = System.nanoTime();

        duration = (endTime - startTime);
        System.out.println(duration);
    }
}
