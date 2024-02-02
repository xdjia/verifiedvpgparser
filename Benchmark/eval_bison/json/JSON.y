%define api.prefix {JSON}
%define api.parser.class {JSON}
%define api.parser.public
%define parse.error verbose

/* NOTE - Set the semantic value to be Integer */
%define api.value.type {Node}

%code imports{
  import java.io.InputStream;
  import java.io.InputStreamReader;
  import java.io.File;
  import java.io.FileInputStream;
  import java.io.Reader;
  import java.io.IOException;
  import java.util.ArrayList;
  import java.util.List;
}

%code {
  public static void main(String args[]) throws IOException {
    int num_round = 10;
    File file = new File (args[1]);

    long lexing_time = 0;

    long startTime = System.nanoTime();

    for (int i = 0; i < num_round; i++) {
      JSONLexer lexer = new JSONLexer(new FileInputStream(file));
      JSON parser = new JSON(lexer);
      if(! parser.parse())
      {
        System.out.println("Parsing Failed.");
      }
      lexing_time += lexer.lexing_time;
    }
    
    long endTime = System.nanoTime();
    long parsing_time = (endTime - startTime) / num_round;

    lexing_time /= num_round;

    System.out.println(lexing_time);
    System.out.println((parsing_time - lexing_time));
    return;
  }
}

%token LCURLY
        RCURLY
        LBRAC
        RBRAC
        COMMA
        COLON
        STRING
        NUMBER
        TRUE
        FALSE
        NULL

%%

json :
    
    { List<Node> children = new ArrayList<>();
      
      $$ = new Node(SymbolKind.S_json, children); }
  | value
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_json, children); }
obj :
    LCURLY pairs RCURLY
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_obj, children); }
  | LCURLY RCURLY
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_obj, children); }
pairs :
    pair
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_pairs, children); }
  | pair COMMA pairs
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_pairs, children); }
pair :
    STRING COLON value
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_pair, children); }
arr :
    LBRAC values RBRAC
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_arr, children); }
  | LBRAC RBRAC
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_arr, children); }
values :
    value
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_values, children); }
  | value COMMA values
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_values, children); }
value :
    STRING
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_value, children); }
  | NUMBER
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_value, children); }
  | obj
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_value, children); }
  | arr
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_value, children); }
  | TRUE
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_value, children); }
  | FALSE
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_value, children); }
  | NULL
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_value, children); }


%%

class JSONLexer implements JSON.Lexer {
  public long lexing_time = 0;
  InputStreamReader it;
  Yylex yylex;

  public JSONLexer(InputStream is){
    it = new InputStreamReader(is);
    yylex = new Yylex(it);
  }

  @Override
  public void yyerror (String s){
    System.err.println(s);
  }

  @Override
  public Node getLVal() {
    return yylex.getLVal();
  }

  @Override
  public int yylex () throws IOException{
    long startTime = System.nanoTime();
    int yychar = yylex.yylex();
    long endTime = System.nanoTime();
    lexing_time += (endTime - startTime); 
    return yychar;
  }
}
