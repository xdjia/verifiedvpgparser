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

parser grammar HTMLParser;

options {
	tokenVocab = HTMLLexer;
}

htmlDocument:
	scriptletOrSeaWs* HTML? scriptletOrSeaWs* DTD? scriptletOrSeaWs* htmlElements* EOF;

scriptletOrSeaWs: SCRIPTLET | SEA_WS;

htmlElements: htmlMisc* htmlElement htmlMisc*;

htmlElement:
	  TAG_OPEN_h1 htmlElement* TAG_CLOSE_h1
	| TAG_OPEN_b htmlElement* TAG_CLOSE_b
	| TAG_OPEN_i htmlElement* TAG_CLOSE_i
	| TAG_OPEN_ul htmlElement* TAG_CLOSE_ul
	| TAG_OPEN_ol htmlElement* TAG_CLOSE_ol
	| TAG_OPEN_table htmlElement* TAG_CLOSE_table
	| TAG_OPEN
	| TAG_CLOSE
	| TAG_SCLOSE
	| CDATA
	| SCRIPTLET
	| htmlChardata
	| htmlComment
	| script
	| style;

htmlChardata: HTML_TEXT | SEA_WS;

htmlMisc: htmlComment | SEA_WS;

htmlComment: HTML_COMMENT | HTML_CONDITIONAL_COMMENT;

script: SCRIPT_OPEN (SCRIPT_BODY | SCRIPT_SHORT_BODY);

style: STYLE_OPEN (STYLE_BODY | STYLE_SHORT_BODY);
