/*
 [The "BSD licence"] Copyright (c) 2013 Tom Everett All rights reserved.
 
 Redistribution and use in source and binary forms, with or without modification, are permitted
 provided that the following conditions are met: 1. Redistributions of source code must retain the
 above copyright notice, this list of conditions and the following disclaimer. 2. Redistributions in
 binary form must reproduce the above copyright notice, this list of conditions and the following
 disclaimer in the documentation and/or other materials provided with the distribution. 3. The name
 of the author may not be used to endorse or promote products derived from this software without
 specific prior written permission.
 
 THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING,
 BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 POSSIBILITY OF SUCH DAMAGE.
 */

lexer grammar HTMLLexer;

HTML_COMMENT: '<!--' .*? '-->';

HTML_CONDITIONAL_COMMENT: '<![' .*? ']>';

HTML: '<?xml' .*? '>';

CDATA: '<![CDATA[' .*? ']]>';

DTD: '<!' .*? '>';

SCRIPTLET: '<?' .*? '?>' | '<%' .*? '%>';

SEA_WS: (' ' | '\t' | '\r'? '\n')+;

SCRIPT_OPEN: '<script' .*? '>' -> pushMode(SCRIPT);

STYLE_OPEN: '<style' .*? '>' -> pushMode(STYLE);

fragment ATTRS: TAG_WHITESPACE+ ((TAG_NAME) TAG_WHITESPACE* ('=' TAG_WHITESPACE* ATTVALUE_VALUE)? TAG_WHITESPACE*)*;

// NOTE - Tags that must be matched
TAG_NAME_h1 : 'h1';
TAG_NAME_b : 'b';
TAG_NAME_i : 'i';
TAG_NAME_ul : 'ul';
TAG_NAME_ol : 'ol';
TAG_NAME_table : 'table';

TAG_OPEN_h1: '<' TAG_WHITESPACE* TAG_NAME_h1 ATTRS? TAG_WHITESPACE* '>';
TAG_OPEN_b: '<' TAG_WHITESPACE* TAG_NAME_b ATTRS? TAG_WHITESPACE* '>';
TAG_OPEN_i: '<' TAG_WHITESPACE* TAG_NAME_i ATTRS? TAG_WHITESPACE* '>';
TAG_OPEN_ul: '<' TAG_WHITESPACE* TAG_NAME_ul ATTRS? TAG_WHITESPACE* '>';
TAG_OPEN_ol: '<' TAG_WHITESPACE* TAG_NAME_ol ATTRS? TAG_WHITESPACE* '>';
TAG_OPEN_table: '<' TAG_WHITESPACE* TAG_NAME_table ATTRS? TAG_WHITESPACE* '>';

TAG_CLOSE_h1: '<' TAG_WHITESPACE* '/' TAG_WHITESPACE* TAG_NAME_h1 TAG_WHITESPACE* '>';
TAG_CLOSE_b: '<' TAG_WHITESPACE* '/' TAG_WHITESPACE* TAG_NAME_b TAG_WHITESPACE* '>';
TAG_CLOSE_i: '<' TAG_WHITESPACE* '/' TAG_WHITESPACE* TAG_NAME_i TAG_WHITESPACE* '>';
TAG_CLOSE_ul: '<' TAG_WHITESPACE* '/' TAG_WHITESPACE* TAG_NAME_ul TAG_WHITESPACE* '>';
TAG_CLOSE_ol: '<' TAG_WHITESPACE* '/' TAG_WHITESPACE* TAG_NAME_ol TAG_WHITESPACE* '>';
TAG_CLOSE_table: '<' TAG_WHITESPACE* '/' TAG_WHITESPACE* TAG_NAME_table TAG_WHITESPACE* '>';

// NOTE - Tags that can be indepdent
TAG_OPEN: '<' TAG_WHITESPACE* TAG_NAME ATTRS? TAG_WHITESPACE* '>';

TAG_CLOSE: '<' TAG_WHITESPACE* '/' TAG_WHITESPACE* TAG_NAME TAG_WHITESPACE* '>';

TAG_SCLOSE: '<' TAG_WHITESPACE* TAG_NAME ATTRS? TAG_WHITESPACE* '/' '>';

HTML_TEXT: ~'<'+;

// tag declarations

TAG_NAME: TAG_NameStartChar TAG_NameChar*;

TAG_WHITESPACE: [ \t\r\n] -> channel(HIDDEN);

fragment HEXDIGIT: [a-fA-F0-9];

fragment DIGIT: [0-9];

fragment TAG_NameChar:
	TAG_NameStartChar
	| '-'
	| '_'
	| '.'
	| DIGIT
	| '\u00B7'
	| '\u0300' ..'\u036F'
	| '\u203F' ..'\u2040';

fragment TAG_NameStartChar:
	[:a-zA-Z]
	| '\u2070' ..'\u218F'
	| '\u2C00' ..'\u2FEF'
	| '\u3001' ..'\uD7FF'
	| '\uF900' ..'\uFDCF'
	| '\uFDF0' ..'\uFFFD';

// <scripts>

mode SCRIPT;

SCRIPT_BODY: .*? '</script>' -> popMode;

SCRIPT_SHORT_BODY: .*? '</>' -> popMode;

// <styles>

mode STYLE;

STYLE_BODY: .*? '</style>' -> popMode;

STYLE_SHORT_BODY: .*? '</>' -> popMode;

// attribute values

ATTVALUE_VALUE: ' '* ATTRIBUTE ;

ATTRIBUTE:
	DOUBLE_QUOTE_STRING
	| SINGLE_QUOTE_STRING
	| ATTCHARS
	| HEXCHARS
	| DECCHARS;

fragment ATTCHARS: ATTCHAR+ ' '?;

fragment ATTCHAR:
	'-'
	| '_'
	| '.'
	| '/'
	| '+'
	| ','
	| '?'
	| '='
	| ':'
	| ';'
	| '#'
	| [0-9a-zA-Z];

fragment HEXCHARS: '#' [0-9a-fA-F]+;

fragment DECCHARS: [0-9]+ '%'?;

fragment DOUBLE_QUOTE_STRING: '"' ~[<"]* '"';

fragment SINGLE_QUOTE_STRING: '\'' ~[<']* '\'';

