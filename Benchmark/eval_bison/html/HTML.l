%%

%unicode

%public
%standalone

%line
%column

%{
   Node yylval;

   public Node getLVal() {
     return yylval;
   }
%}

/* %debug */

%xstate HTML_COMMENT, CDATA, TAG, DTD, HTML_CONDITIONAL_COMMENT, HTML, SCRIPTLET, SCRIPT,SCRIPT_OPEN,STYLE, STYLE_OPEN, ATTVALUE

TAG_WHITESPACE = [ \t\r\n]

CommentStart = "<!--"
CommentEnd = "-->"

TAG_NameStartChar =
        ":" | [a-z] | [A-Z]
      | [\u2070-\u218F]
      | [\u2C00-\u2FEF]
      | [\u3001-\uD7FF]
      | [\uF900-\uFDCF]
      | [\uFDF0-\uFFFD]

DIGIT = [0-9]

TAG_NameChar = {TAG_NameStartChar} | "-" | "_" | "." | {DIGIT} 
  | \u00B7
  | [\u0300-\u036F]
  | [\u203F-\u2040]

TAG_NAME = {TAG_NameStartChar} {TAG_NameChar}*

CDataStart = "<![CDATA["
CDataEnd   = "]]>"

ATTVALUE_VALUE = " "* {ATTRIBUTE}

ATTRIBUTE 
  = {DOUBLE_QUOTE_STRING}
  | {SINGLE_QUOTE_STRING}
  | {ATTCHARS}
  | {HEXCHARS}
  | {DECCHARS}

ATTCHARS = {ATTCHAR}+ " "?

ATTCHAR
    = "-"
    | "_"
    | "."
    | "/"
    | "+"
    | ","
    | "?"
    | "="
    | ":"
    | ";"
    | "#"
    | [0-9] | [a-z] | [A-Z]

HEXCHARS = "#" [0-9a-fA-F]+

DECCHARS = [0-9]+ "%"?

DOUBLE_QUOTE_STRING = \"[^<\"]*\"

SINGLE_QUOTE_STRING = "'" [^<']* "'"

/* NOTE - TAG Names */

/* NOTE - tags that much be closed */
TAG_NAME_h1 = "h1"
TAG_NAME_b = "b"
TAG_NAME_i = "i"
TAG_NAME_ul = "ul"
TAG_NAME_ol = "ol"
TAG_NAME_table = "table"

ATTRS = {TAG_WHITESPACE}+ ({TAG_NAME} {TAG_WHITESPACE}* ("=" {TAG_WHITESPACE}* {ATTVALUE_VALUE})? {TAG_WHITESPACE}*)*

TAG_OPEN_h1 = {TAG_WHITESPACE}* {TAG_NAME_h1} {ATTRS}? {TAG_WHITESPACE}* ">"
TAG_OPEN_b = {TAG_WHITESPACE}* {TAG_NAME_b} {ATTRS}? {TAG_WHITESPACE}* ">"
TAG_OPEN_i = {TAG_WHITESPACE}* {TAG_NAME_i} {ATTRS}? {TAG_WHITESPACE}* ">"
TAG_OPEN_ul = {TAG_WHITESPACE}* {TAG_NAME_ul} {ATTRS}? {TAG_WHITESPACE}* ">"
TAG_OPEN_ol = {TAG_WHITESPACE}* {TAG_NAME_ol} {ATTRS}? {TAG_WHITESPACE}* ">"
TAG_OPEN_table = {TAG_WHITESPACE}* {TAG_NAME_table} {ATTRS}? {TAG_WHITESPACE}* ">"

TAG_CLOSE_h1 = {TAG_WHITESPACE}* "/" {TAG_WHITESPACE}* {TAG_NAME_h1} {TAG_WHITESPACE}* ">"
TAG_CLOSE_b = {TAG_WHITESPACE}* "/" {TAG_WHITESPACE}* {TAG_NAME_b} {TAG_WHITESPACE}* ">"
TAG_CLOSE_i = {TAG_WHITESPACE}* "/" {TAG_WHITESPACE}* {TAG_NAME_i} {TAG_WHITESPACE}* ">"
TAG_CLOSE_ul = {TAG_WHITESPACE}* "/" {TAG_WHITESPACE}* {TAG_NAME_ul} {TAG_WHITESPACE}* ">"
TAG_CLOSE_ol = {TAG_WHITESPACE}* "/" {TAG_WHITESPACE}* {TAG_NAME_ol} {TAG_WHITESPACE}* ">"
TAG_CLOSE_table = {TAG_WHITESPACE}* "/" {TAG_WHITESPACE}* {TAG_NAME_table} {TAG_WHITESPACE}* ">"

TAG_OPEN = {TAG_WHITESPACE}* {TAG_NAME} {ATTRS}? {TAG_WHITESPACE}* ">"

TAG_CLOSE = {TAG_WHITESPACE}* "/" {TAG_WHITESPACE}* {TAG_NAME} {TAG_WHITESPACE}* ">"

TAG_SCLOSE = {TAG_WHITESPACE}* {TAG_NAME} {ATTRS}? {TAG_WHITESPACE}* "/" ">"


%%

<YYINITIAL> {

  /* NOTE - HTML_COMMENT */
  {CommentStart} {
      yybegin(HTML_COMMENT);
  }

  /* NOTE - CDATA */
  {CDataStart} {
      yybegin(CDATA);
  }

  /* NOTE - DTD (-> skip)*/
  "<!" { 
      /* System.out.println("DTD"); */
      yybegin(DTD);
   }

  "<?" | "<%" {
      yybegin(SCRIPTLET);
  }

   "<![" {
      yybegin(HTML_CONDITIONAL_COMMENT);
   }

  "<?xml" {
      yybegin(HTML);
  }

  "<script" {
      yybegin(SCRIPT_OPEN);
  }

  "<style" {
      yybegin(STYLE_OPEN);
  }
  
  (" "|"\t"|"\r"? "\n")+  { 
    yylval = new Node(HTMLLexer.SEA_WS, yytext());
    return HTMLLexer.SEA_WS; }

  "<" {
    yybegin(TAG);
  }

  /* NOTE - TEXT */
  [^<]+ {
    yylval = new Node(HTMLLexer.HTML_TEXT, yytext());
    return HTMLLexer.HTML_TEXT;
  }

}

<TAG> {
  /* NOTE - Collect an open, close or self-closed tag */

    {TAG_OPEN_h1} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_OPEN_h1, yytext()); return HTMLLexer.TAG_OPEN_h1; }
    {TAG_OPEN_b} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_OPEN_b, yytext()); return HTMLLexer.TAG_OPEN_b; }
    {TAG_OPEN_i} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_OPEN_i, yytext()); return HTMLLexer.TAG_OPEN_i; }
    {TAG_OPEN_ul} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_OPEN_ul, yytext()); return HTMLLexer.TAG_OPEN_ul; }
    {TAG_OPEN_ol} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_OPEN_ol, yytext()); return HTMLLexer.TAG_OPEN_ol; }
    {TAG_OPEN_table} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_OPEN_table, yytext()); return HTMLLexer.TAG_OPEN_table; }

    {TAG_CLOSE_h1} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_CLOSE_h1, yytext()); return HTMLLexer.TAG_CLOSE_h1; }
    {TAG_CLOSE_b} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_CLOSE_b, yytext()); return HTMLLexer.TAG_CLOSE_b; }
    {TAG_CLOSE_i} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_CLOSE_i, yytext()); return HTMLLexer.TAG_CLOSE_i; }
    {TAG_CLOSE_ul} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_CLOSE_ul, yytext()); return HTMLLexer.TAG_CLOSE_ul; }
    {TAG_CLOSE_ol} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_CLOSE_ol, yytext()); return HTMLLexer.TAG_CLOSE_ol; }
    {TAG_CLOSE_table} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_CLOSE_table, yytext()); return HTMLLexer.TAG_CLOSE_table; }

    {TAG_OPEN} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_OPEN, yytext()); return HTMLLexer.TAG_OPEN; }
    {TAG_CLOSE} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_CLOSE, yytext()); return HTMLLexer.TAG_CLOSE; }
    {TAG_SCLOSE} { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.TAG_SCLOSE, yytext()); return HTMLLexer.TAG_SCLOSE; }
}

/* <TAG_NAME> {

  {TAG_NameChar}+ {
      tag_name.append(yytext());
  }

  [^] {
    yypushback(1);
    yybegin(TAG);
    System.out.println("TAGN:" + tag_name);

    return (HTMLLexer.TAG_NAME); 
  }
} */

<HTML> {
  ">" { yybegin(YYINITIAL); yylval = new Node(HTMLLexer.HTML, yytext()); return (HTMLLexer.HTML); }

  ~(">")
  {
    yypushback(1);
  }
}

<HTML_CONDITIONAL_COMMENT> {
  "]>" {
    yybegin(YYINITIAL); yylval = new Node(HTMLLexer.HTML_CONDITIONAL_COMMENT, yytext());
    return (HTMLLexer.HTML_CONDITIONAL_COMMENT);

  }

  ~("]>") 
  {
    yypushback(2);
  }
}


<DTD> {
  ">"
  {
      /* System.out.println("DTD Ends"); */
      yybegin(YYINITIAL);
  }

  ~">"
  { 
    yypushback(1);
  }
}

<HTML_COMMENT> {
  {CommentEnd}  {
      yybegin(YYINITIAL); 
      yylval = new Node(HTMLLexer.HTML_COMMENT, yytext());
      return (HTMLLexer.HTML_COMMENT);
  }
  
   ~{CommentEnd}  {
      /* System.out.println(yytext()); */

      yypushback(3);
      /* return (TokenType.HTML_COMMENT); */
  }
}

<SCRIPTLET> {
("?>"|"%>")                         {
                                     yybegin(YYINITIAL);
                                     yylval = new Node(HTMLLexer.SCRIPTLET, yytext());

                                     return (HTMLLexer.SCRIPTLET);
                                 }
  ~("?>"|"%>")                    {
                                     yypushback(2);
                                 }
}

<CDATA> {
  {CDataEnd}                     {
                                     yybegin(YYINITIAL);
                                     yylval = new Node(HTMLLexer.CDATA, yytext());

                                     return (HTMLLexer.CDATA);
                                 }
  ~{CDataEnd}                    {
                                     yypushback(3);
                                 }
}

<SCRIPT_OPEN> {
  ">"  {
      yybegin(SCRIPT);
                                     yylval = new Node(HTMLLexer.SCRIPT_OPEN, yytext());

      return (HTMLLexer.SCRIPT_OPEN);
  }
  ~">"  {
      yypushback(1);
  }
}

<STYLE_OPEN> {
  ">"  {
      yybegin(STYLE);
                                     yylval = new Node(HTMLLexer.STYLE_OPEN, yytext());

      return (HTMLLexer.STYLE_OPEN);
  }
  ~">"  {
      yypushback(1);
  }
}

<SCRIPT> {
  "</script>" {
    yybegin(YYINITIAL);
    
                                         yylval = new Node(HTMLLexer.SCRIPT_BODY, yytext());

    return (HTMLLexer.SCRIPT_BODY);
  }

  "</>" {
    yybegin(YYINITIAL);
                                         yylval = new Node(HTMLLexer.SCRIPT_SHORT_BODY, yytext());

    return (HTMLLexer.SCRIPT_SHORT_BODY);
  }

  ~"</script>"  {
      yypushback(9);
  }

  ~"</>"  {
      yypushback(3);
  }
}

<STYLE> {
  "</style>" {
    yybegin(YYINITIAL);
                                         yylval = new Node(HTMLLexer.STYLE_BODY, yytext());

    return (HTMLLexer.STYLE_BODY);
  }

  "</>" {
    yybegin(YYINITIAL);
                                         yylval = new Node(HTMLLexer.STYLE_SHORT_BODY, yytext());

    return (HTMLLexer.STYLE_SHORT_BODY);
  }

  ~"</style>"  {
      yypushback(8);
  }

  ~"</>"  {
      yypushback(3);
  }
}



/* <ATTVALUE> {
  {ATTVALUE_VALUE} {
    yybegin(TAG);
    return (HTMLLexer.ATTVALUE_VALUE);
  }

  {ATTRIBUTE} {

  }

} */

<YYINITIAL,HTML_COMMENT, CDATA, TAG, DTD, HTML_CONDITIONAL_COMMENT, HTML, SCRIPTLET, SCRIPT,SCRIPT_OPEN,STYLE, STYLE_OPEN, ATTVALUE> {
   [^]                          
   { 
      System.out.println("Lexing Error: "+yytext()+" line:"+yyline+" col:"+yycolumn); 
      System.exit(1);
    }

   <<EOF>>
   { 
      /* System.out.println("Lexing Finished"); */
      return 0; 
    }
}