import java.util.List;

public class Node {
    // NOTE - The kind of a nonterminal
    public JSON.SymbolKind kind;
    // NOTE - The kind of a terminal
    public int id;
    // NOTE - The name of the terminal/nonterminal
    public String name = "";
    // NOTE - If this is a terminal, the lexeme
    public String lexeme = "";
    // NOTE - The children nodes
    List<Node> children;

    // NOTE - create a node
    public Node(JSON.SymbolKind kind, List<Node> children) {
        this.kind= kind;
        this.children = children;
    }

    // NOTE - create a leaf
    public Node(int id, String lexeme) {
        this.id = id;
        this.lexeme = lexeme;
    }
}