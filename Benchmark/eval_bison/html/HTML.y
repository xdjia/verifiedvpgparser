%define api.prefix {HTML}
%define api.parser.class {HTML}
%define api.parser.public
%define parse.error verbose
%define parse.trace

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
      HTMLLexer lexer = new HTMLLexer(new FileInputStream(file));
      HTML parser = new HTML(lexer);
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

%token CDATA
        DTD
        HTML_COMMENT
        HTML_CONDITIONAL_COMMENT
        HTML
        SCRIPTLET
        SCRIPT_OPEN
        SCRIPT_BODY
        SCRIPT_SHORT_BODY
        STYLE_OPEN
        STYLE_BODY
        STYLE_SHORT_BODY
        TAG_OPEN_h1
        TAG_OPEN_b
        TAG_OPEN_i
        TAG_OPEN_ul
        TAG_OPEN_ol
        TAG_OPEN_table
        TAG_CLOSE_h1
        TAG_CLOSE_b
        TAG_CLOSE_i
        TAG_CLOSE_ul
        TAG_CLOSE_ol
        TAG_CLOSE_table
        TAG_SCLOSE
        TAG_NAME
        HTML_TEXT
        SEA_WS
        TAG_EQUALS
        TAG_OPEN
        TAG_CLOSE
        TAG_SLASH
        TAG_SLASH_CLOSE
        ATTVALUE_VALUE

%%

/* NOTE - ANTLR's HTML grammar with regular expressions desugared */


htmlDocument :
    
    { List<Node> children = new ArrayList<>();
      
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | DTD
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | DTD vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | DTD vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | DTD vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 DTD
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 DTD vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 DTD vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 DTD vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML DTD
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML DTD vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML DTD vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML DTD vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv4 vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv4 vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv4 DTD
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv4 DTD vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv4 DTD vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | HTML vv4 DTD vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      children.add($5);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv4 vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv4 vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv4 DTD
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv4 DTD vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv4 DTD vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 vv4 DTD vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      children.add($5);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML DTD
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML DTD vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML DTD vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML DTD vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      children.add($5);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv4 vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv4 vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      children.add($5);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv4 DTD
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv4 DTD vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      children.add($5);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv4 DTD vv4
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      children.add($5);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
  | vv4 HTML vv4 DTD vv4 vv3
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      children.add($4);
      children.add($5);
      children.add($6);
      $$ = new Node(SymbolKind.S_htmlDocument, children); }
vv4 :
    vv4 scriptletOrSeaWs
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv4, children); }
  | scriptletOrSeaWs
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv4, children); }
vv3 :
    vv3 htmlElements
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv3, children); }
  | htmlElements
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv3, children); }
scriptletOrSeaWs :
    SCRIPTLET
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_scriptletOrSeaWs, children); }
  | SEA_WS
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_scriptletOrSeaWs, children); }
htmlElements :
    htmlElement
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElements, children); }
  | htmlElement vv2
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlElements, children); }
  | vv2 htmlElement
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlElements, children); }
  | vv2 htmlElement vv2
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlElements, children); }
vv2 :
    vv2 htmlMisc
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_vv2, children); }
  | htmlMisc
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_vv2, children); }
htmlElement :
    TAG_OPEN_h1 htmlElement_ TAG_CLOSE_h1
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | TAG_OPEN_b htmlElement_ TAG_CLOSE_b
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | TAG_OPEN_i htmlElement_ TAG_CLOSE_i
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | TAG_OPEN_ul htmlElement_ TAG_CLOSE_ul
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | TAG_OPEN_ol htmlElement_ TAG_CLOSE_ol
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | TAG_OPEN_table htmlElement_ TAG_CLOSE_table
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      children.add($3);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | TAG_OPEN
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | TAG_CLOSE
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | TAG_SCLOSE
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | CDATA
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | SCRIPTLET
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | htmlChardata
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | htmlComment
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | script
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
  | style
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement, children); }
htmlElement_ :
    
    { List<Node> children = new ArrayList<>();
      
      $$ = new Node(SymbolKind.S_htmlElement_, children); }
  | htmlElement
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlElement_, children); }
  | htmlElement_ htmlElement
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_htmlElement_, children); }
htmlChardata :
    HTML_TEXT
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlChardata, children); }
  | SEA_WS
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlChardata, children); }
htmlMisc :
    htmlComment
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlMisc, children); }
  | SEA_WS
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlMisc, children); }
htmlComment :
    HTML_COMMENT
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlComment, children); }
  | HTML_CONDITIONAL_COMMENT
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_htmlComment, children); }
script :
    SCRIPT_OPEN
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_script, children); }
  | SCRIPT_OPEN SCRIPT_BODY
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_script, children); }
  | SCRIPT_OPEN SCRIPT_SHORT_BODY
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_script, children); }
style :
    STYLE_OPEN
    { List<Node> children = new ArrayList<>();
      children.add($1);
      $$ = new Node(SymbolKind.S_style, children); }
  | STYLE_OPEN STYLE_BODY
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_style, children); }
  | STYLE_OPEN STYLE_SHORT_BODY
    { List<Node> children = new ArrayList<>();
      children.add($1);
      children.add($2);
      $$ = new Node(SymbolKind.S_style, children); }

  
%%

class HTMLLexer implements HTML.Lexer {
  public long lexing_time = 0;
  InputStreamReader it;
  Yylex yylex;

  public HTMLLexer(InputStream is){
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
