%%

%unicode

%public
/* NOTE - comment %standalone if not using "int" as the token type  */
%standalone

%line
%column
%int

/* %debug */

%xstate COMMENT, CDATA, PROC_INSTR, INSIDE, DTD, TAG


%{
   Node yylval;

   public Node getLVal() {
     return yylval;
   }
%}

S = [ \t\r\n]

CommentStart = "<!--"
CommentEnd = "-->"

NameStartChar =
        ":" | [a-z] | [A-Z]
      | [\u2070-\u218F]
      | [\u2C00-\u2FEF]
      | [\u3001-\uD7FF]
      | [\uF900-\uFDCF]
      | [\uFDF0-\uFFFD]

DIGIT = [0-9]
HEXDIGIT = [a-fA-F0-9]

NameChar = {NameStartChar} | "-" | "_" | "." | {DIGIT} 
  | \u00B7
  | [\u0300-\u036F]
  | [\u203F-\u2040]

Name = {NameStartChar} {NameChar}*

CDataStart = "<![CDATA["
CDataEnd   = "]]>"

STRING = (\"[^<\"]*\" | \'[^<']*\') 

ATTRS = {S}+ (({Name}) {S}* ("=" {S}* {STRING})? {S}*)*

TAG_OPEN = {S}* {Name} {ATTRS}? {S}* ">"

TAG_CLOSE = {S}* "/" {S}* {Name} {S}* ">"

TAG_SCLOSE = {S}* {Name} {ATTRS}? {S}* "/" ">"

/* CloseTag = "</" {Name} {S}* ">" */

/* Attribute = {Name} "=" */

%%

<YYINITIAL> {

  /* NOTE - COMMENT */
  {CommentStart} {
      yybegin(COMMENT);
  }

  /* NOTE - CDATA */
  {CDataStart} {
      yybegin(CDATA);
  }

  /* NOTE - DTD (-> skip)*/
  "<!" { 
      System.out.println("DTD");
      yybegin(DTD);
   }

  "&" {Name} ";"  { 
    yylval = new Node(XMLLexer.EntityRef, yytext());
    return XMLLexer.EntityRef; }
  
  "&#"  {DIGIT}+ ";"  |
  "&#x" {HEXDIGIT}+ ";"  { 
    yylval = new Node(XMLLexer.CharRef, yytext());
    return XMLLexer.CharRef; }

  (" "|"\t"|"\r"? "\n")+  { 
    yylval = new Node(XMLLexer.SEA_WS, yytext());
    return XMLLexer.SEA_WS; }

  "<"  {
    /* System.out.println("| < |"); */
      yybegin(TAG);
  }

  "<?xml" {S} {
      yybegin(INSIDE);
      
      yylval = new Node(XMLLexer.XMLDeclOpen, yytext());
      return XMLLexer.XMLDeclOpen;
  }

  "<?" {
      yybegin(PROC_INSTR);
  }

  /* NOTE - TEXT */
  [^<&]+ { 
    yylval = new Node(XMLLexer.TEXT, yytext()) ;
    return XMLLexer.TEXT ; }

}

<TAG> {

    {TAG_OPEN} {
      yybegin(YYINITIAL);
      yylval = new Node(XMLLexer.TAG_OPEN, yytext());
      return XMLLexer.TAG_OPEN;
    }

    {TAG_CLOSE} {
      yybegin(YYINITIAL);
      yylval = new Node(XMLLexer.TAG_CLOSE, yytext());
      return XMLLexer.TAG_CLOSE;
    }

    {TAG_SCLOSE} {
      yybegin(YYINITIAL);
      yylval = new Node(XMLLexer.TAG_SCLOSE, yytext());
      return XMLLexer.TAG_SCLOSE;
    }

}

<INSIDE> {
  /* NOTE - Collect an open, close or single tag */

  "?>"                   
    {
      yybegin(YYINITIAL);
      /* System.out.println("| ?> |"); */
      yylval = new Node (XMLLexer.SPECIAL_CLOSE, yytext());
      return XMLLexer.SPECIAL_CLOSE;
    }

  "="
    {
      yylval = new Node (XMLLexer.EQUALS, yytext());
      return XMLLexer.EQUALS;
    }

  {STRING}
      { 
        yylval = new Node (XMLLexer.STRING, yytext());
        return XMLLexer.STRING;}

  {Name} 
    {
      /* System.out.println("Name:" + yytext()); */
      yylval = new Node (XMLLexer.Name, yytext());
      return XMLLexer.Name;
    }

  {S} {}
}

<PROC_INSTR> {
  "?>"  {
    /* System.out.println("PI:"+yytext()); */
    yybegin(YYINITIAL);
    yylval = new Node (XMLLexer.PI, yytext());
    return XMLLexer.PI;
  }

  ~"?>"
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

<COMMENT> {
  {CommentEnd}                   {
                                     yybegin(YYINITIAL);
                                     yylval = new Node (XMLLexer.COMMENT, yytext());
                                     return XMLLexer.COMMENT;
                                 }
   ~{CommentEnd}                 {
                                     /* System.out.println(yytext()); */

                                     yypushback(3);
                                     /* return new Node (TokenType.COMMENT, yytext()); */
                                 }
}

<CDATA> {
  {CDataEnd}                     {
                                     yybegin(YYINITIAL);
                                     yylval = new Node (XMLLexer.CDATA, yytext());
                                     return XMLLexer.CDATA;
                                 }
  ~{CDataEnd}                    {
                                     yypushback(3);
                                 }
}

<YYINITIAL,INSIDE,PROC_INSTR,CDATA,COMMENT,DTD,TAG> {
   [^]                          
   { 
      System.out.println("Lexing Error: "+yytext()+" line:"+yyline+" col:"+yycolumn); 
      System.exit(1);

    }

   <<EOF>>
   { 
      /* System.out.println("Lexing Finished"); */
      /* List<Node> children = new ArrayList<>();
      return new Node(XMLLexer.YYEOF, children); */
      return XMLLexer.YYEOF;
    }
}