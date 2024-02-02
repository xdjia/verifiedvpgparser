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

/* NOTE The grammar below is translated from ANTLR's JSON grammar */

HEX = [0-9a-fA-F]

SAFECODEPOINT = [^\u0000-\u001F\"\\]

UNICODE = \\([\"\\/bfnrt]|(u({HEX}{4})))

STRING = \" ({SAFECODEPOINT} | {UNICODE})* \"

INT = "0" | [1-9] [0-9]*
EXP = [Ee] ["+"-]? INT
NUMBER = "-"? {INT} ("." [0-9]+)? {EXP}?

%state STRING

%%

// Scan for the allowable JSON "punctuation" tokens and return the relevant
// symbols to the CUP parser

<YYINITIAL> {

  "{" { 
    yylval = new Node(JSONLexer.LCURLY, yytext());
    return JSONLexer.LCURLY ; }
  "}" { 
    yylval = new Node(JSONLexer.RCURLY, yytext());
    return JSONLexer.RCURLY ; }

  "[" { 
    yylval = new Node(JSONLexer.LBRAC, yytext());
    return JSONLexer.LBRAC ; }
  "]" { 
    yylval = new Node(JSONLexer.RBRAC, yytext());
    return JSONLexer.RBRAC ; }

  "," { 
    yylval = new Node(JSONLexer.COMMA, yytext());
    return JSONLexer.COMMA ; }
  ":" { 
    yylval = new Node(JSONLexer.COLON, yytext());
    return JSONLexer.COLON ; }

  "true"  { 
    yylval = new Node(JSONLexer.TRUE, yytext());
    return JSONLexer.TRUE; }
  "false"  { 
    yylval = new Node(JSONLexer.FALSE, yytext());
    return JSONLexer.FALSE; }
  "null"	   { 
    yylval = new Node(JSONLexer.NULL, yytext());
    return JSONLexer.NULL; }

  {STRING} { 
    yylval = new Node(JSONLexer.STRING, yytext());
    return JSONLexer.STRING; }

  {NUMBER}  { 
    yylval = new Node(JSONLexer.NUMBER, yytext());
    return JSONLexer.NUMBER; }

}


[ \t\n\r] { /* ignore white spaces */ }

. { 
  System.err.println("\nError (Lexing): "+yytext() + "\n");  
	System.exit(1);
}