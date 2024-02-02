%define api.prefix {XML}
%define api.parser.class {XML}
%define api.parser.public
%define parse.error verbose

/* NOTE - Set the semantic value to be Node */
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
    int yydebug = 0;
    int num_round = 10;
    File file = new File (args[1]);

    long lexing_time = 0;

    long startTime = System.nanoTime();

    for (int i = 0; i < num_round; i++) {
      XMLLexer lexer = new XMLLexer(new FileInputStream(file));
      XML parser = new XML(lexer);
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

%token XMLDeclOpen
        SPECIAL_CLOSE
        CDATA
        PI
        COMMENT
        Name
        EntityRef
        CharRef
        STRING
        TEXT
        SEA_WS
        EQUALS
        TAG_OPEN
        TAG_CLOSE
        TAG_SCLOSE

%%

/* NOTE - ANTLR's XML grammar with regular expressions desugared */

document :
    element
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_document, children); }
  | element vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_document, children); }
  | vv3 element
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_document, children); }
  | vv3 element vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_document, children); }
  | prolog element
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_document, children); }
  | prolog element vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_document, children); }
  | prolog vv3 element
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_document, children); }
  | prolog vv3 element vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_document, children); }
prolog :
    XMLDeclOpen SPECIAL_CLOSE
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_prolog, children); }
  | XMLDeclOpen vv2 SPECIAL_CLOSE
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_prolog, children); }
content :
    
    { List<Node> children = new ArrayList<>();
      
      $$ = new Node(SymbolKind.S_content, children); }
  | content vv1
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_content, children); }
  | chardata
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_content, children); }
element :
    TAG_OPEN content TAG_CLOSE
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_element, children); }
  | TAG_SCLOSE
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_element, children); }
reference :
    EntityRef
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_reference, children); }
  | CharRef
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_reference, children); }
attribute :
    Name EQUALS STRING
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_attribute, children); }
chardata :
    TEXT
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_chardata, children); }
  | SEA_WS
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_chardata, children); }
misc :
    COMMENT
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_misc, children); }
  | PI
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_misc, children); }
  | SEA_WS
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_misc, children); }
vv1 :
    element
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | element chardata
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | reference
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | reference chardata
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | CDATA
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | CDATA chardata
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | PI
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | PI chardata
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | COMMENT
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv1, children); }
  | COMMENT chardata
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv1, children); }
vv2 :
    attribute
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv2, children); }
  | vv2 attribute
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv2, children); }
vv3 :
    misc
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv3, children); }
  | vv3 misc
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv3, children); }


%%

class XMLLexer implements XML.Lexer {
  public long lexing_time = 0;
  InputStreamReader it;
  Yylex yylex;

  public XMLLexer(InputStream is){
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
    int id = yylex.yylex();
    long endTime = System.nanoTime();
    lexing_time += (endTime - startTime); 
    return id;
  }
}
