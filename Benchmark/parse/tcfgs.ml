(* NOTE - Find a set of sentences that trigger all transitions of a VPG PDA.
   Usage:
   ```
   python gen_vpg_lexer_compare_online.py && dune exec ./parse_tcfg.exe vpgs/vpg.vpg
   ``` *)

open TCFGParser

let g_html : TCFG.grammar =
  [
    ( "htmlDocument",
      [
        [
          Ast [ Var "scriptletOrSeaWs" ];
          Qst [ Trm "HTML" ];
          Ast [ Var "scriptletOrSeaWs" ];
          Qst [ Trm "DTD" ];
          Ast [ Var "scriptletOrSeaWs" ];
          Ast [ Var "htmlElements" ];
        ];
      ] );
    ("scriptletOrSeaWs", [ [ Trm "SCRIPTLET" ]; [ Trm "SEA_WS" ] ]);
    ( "htmlElements",
      [ [ Ast [ Var "htmlMisc" ]; Var "htmlElement"; Ast [ Var "htmlMisc" ] ] ]
    );
    ( "htmlElement",
      [
        [ Mat ("TAG_OPEN_h1", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_h1") ];
        [ Mat ("TAG_OPEN_h2", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_h2") ];
        [ Mat ("TAG_OPEN_h3", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_h3") ];
        [ Mat ("TAG_OPEN_h4", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_h4") ];
        [ Mat ("TAG_OPEN_div", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_div") ];
        [ Mat ("TAG_OPEN_b", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_b") ];
        [ Mat ("TAG_OPEN_i", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_i") ];
        [ Mat ("TAG_OPEN_ul", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_ul") ];
        [ Mat ("TAG_OPEN_ol", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_ol") ];
        [ Mat ("TAG_OPEN_table", [ Ast [ Var "htmlElement" ] ], "TAG_CLOSE_table"); ];
        [ Trm "TAG_OPEN" ];
        [ Trm "TAG_CLOSE" ];
        [ Trm "TAG_SCLOSE" ];
        [ Trm "CDATA" ];
        [ Trm "SCRIPTLET" ];
        [ Var "htmlChardata" ];
        [ Var "htmlComment" ];
        [ Var "script" ];
        [ Var "style" ];
      ] );
    ("htmlChardata", [ [ Trm "HTML_TEXT" ]; [ Trm "SEA_WS" ] ]);
    ("htmlMisc", [ [ Var "htmlComment" ]; [ Trm "SEA_WS" ] ]);
    ( "htmlComment",
      [ [ Trm "HTML_COMMENT" ]; [ Trm "HTML_CONDITIONAL_COMMENT" ] ] );
    ( "script",
      [
        [
          Trm "SCRIPT_OPEN"; Chc [ Trm "SCRIPT_BODY"; Trm "SCRIPT_SHORT_BODY" ];
        ];
      ] );
    ( "style",
      [ [ Trm "STYLE_OPEN"; Chc [ Trm "STYLE_BODY"; Trm "STYLE_SHORT_BODY" ] ] ]
    );
  ]

let g_json : TCFG.grammar =
  [
    ("json", [ [ Var "value" ] ]);
    ( "obj",
      [
        [ Mat ("'{'", [ Var "pair"; Ast [ Trm "','"; Var "pair" ] ], "'}'") ];
        [ Mat ("'{'", [], "'}'") ];
      ] );
    ("pair", [ [ Trm "STRING"; Trm "':'"; Var "value" ] ]);
    ( "arr",
      [
        [ Mat ("'['", [ Var "value"; Ast [ Trm "','"; Var "value" ] ], "']'") ];
        [ Mat ("'['", [], "']'") ];
      ] );
    ( "value",
      [
        [ Trm "STRING" ];
        [ Trm "NUMBER" ];
        [ Var "obj" ];
        [ Var "arr" ];
        [ Trm "'true'" ];
        [ Trm "'false'" ];
        [ Trm "'null'" ];
      ] );
  ]

let g_xml : TCFG.grammar =
  [
    ( "document",
      [
        [
          Qst [ Var "prolog" ];
          Ast [ Var "misc" ];
          Var "element";
          Ast [ Var "misc" ];
        ];
      ] );
    ( "prolog",
      [ [ Trm "XMLDeclOpen"; Ast [ Var "attribute" ]; Trm "SPECIAL_CLOSE" ] ] );
    ( "content",
      [
        [
          Qst [ Var "chardata" ];
          Ast
            [
              Chc
                [
                  Var "element";
                  Var "reference";
                  Trm "CDATA";
                  Trm "PI";
                  Trm "COMMENT";
                ];
              Qst [ Var "chardata" ];
            ];
        ];
      ] );
    ( "element",
      [
        [ Mat ("TAG_OPEN", [ Var "content" ], "TAG_CLOSE") ];
        [ Trm "TAG_SCLOSE" ];
      ] );
    ("reference", [ [ Trm "EntityRef" ]; [ Trm "CharRef" ] ]);
    ("attribute", [ [ Trm "Name"; Trm "'='"; Trm "STRING" ] ]);
    ("chardata", [ [ Trm "TEXT" ]; [ Trm "SEA_WS" ] ]);
    ("misc", [ [ Trm "COMMENT" ]; [ Trm "PI" ]; [ Trm "SEA_WS" ] ]);
  ]

let tcfg : TCFG.grammar =
  [
    ("grammar", [ [ Qst [ Trm "Action" ]; Pls [ Chc [ Var "rule" ] ] ] ]);
    ( "rule",
      [
        [
          Trm "Nonterminal";
          Trm "':'";
          Var "ruleBody";
          Ast [ Trm "'|'"; Var "ruleBody" ];
          Trm "';'";
        ];
      ] );
    ("ruleBody", [ [ Pls [ Var "term" ]; Qst [ Trm "Action" ] ] ]);
    ( "term",
      [
        [
          Chc [ Trm "Terminal"; Trm "Nonterminal"; Var "call"; Var "return" ];
          Qst [ Trm "Reg_op" ];
        ];
        [
          Mat
            ( "'('",
              [ Pls [ Var "term" ]; Ast [ Trm "'|'"; Pls [ Var "term" ] ] ],
              "')'" );
          Qst [ Trm "Reg_op" ];
        ];
      ] );
    ("call", [ [ Trm "'<'"; Trm "Terminal" ] ]);
    ("return", [ [ Trm "Terminal"; Trm "'>'" ] ]);
  ]

(** Some VPG examples for testing *)
let vpg0 : TCFG.grammar =
  [
    ("ruleBody", [ [ Pls [ Var "term" ] ] ]);
    ("term", [ [ Trm "Terminal" ]; [ Mat ("(", [ Var "term" ], ")") ] ]);
  ]

let vpg1 : TCFG.grammar =
  (* NOTE - H -> c | aHbH | ε *)
  [
    (* ("H", [ [ Var "A" ]; [ Var "A"; Var "H" ] ]); *)
    ("H", [ []; [ Trm "c"; Var "H" ]; [ Mat ("a", [ Var "H" ], "b"); Var "H" ] ]);
    (* ("A", [ []; [ Trm "c" ]; [ Mat ("a", [ Var "A" ], "b") ] ]); *)
  ]

let vpg2 : TCFG.grammar =
  [
    (* ("H", [ [ Var "A" ]; [ Var "A"; Var "H" ] ]); *)
    ("L", [ [ Pls [ Trm "c" ]; Trm "c" ] ]);
  ]

let vpg3 : TCFG.grammar =
  [
    ("H", [ [ Var "A"; Trm "a"; Var "B" ] ]);
    ("A", [ [ Pls [ Trm "c" ] ] ]);
    ("B", [ [ Pls [ Trm "d" ] ] ]);
  ]

let vpg4 : TCFG.grammar =
  [ ("H", [ [ Mat ("a", [], "b") ]; [ Mat ("a", [ Var "H" ], "b") ] ]) ]

let vpg5 : TCFG.grammar =
  [
    ("H", [ [ Mat ("{", [ Var "P" ], "}") ] ]);
    ("P", [ [ Trm "c"; Var "V" ] ]);
    ("V", [ [ Var "H" ]; [ Mat ("[", [], "]") ] ]);
  ]

let vpg6 : TCFG.grammar =
  [
    ( "H",
      [
        [ Mat ("[", [ Var "H" ], "]"); Var "H" ];
        [ Mat ("{", [ Var "H" ], "}"); Var "H" ];
        [ Chc [ Trm "a"; Trm "b"; Trm "c"; Trm "d" ]; Var "H" ];
        [];
      ] );
  ]

let vpg7 : TCFG.grammar =
  [
    ( "H",
      [
        [ Mat ("[", [ Var "H" ], "]"); Var "H" ];
        [ Mat ("{", [ Var "H" ], "}"); Var "H" ];
        [ Ast [ Chc [ Trm "a"; Trm "b"; Trm "c"; Trm "d" ] ] ];
        [];
      ] );
  ]
