open Core
open TCFGParser.Utils
open TCFGParser.TCFGParseTree

type nt =
 | S_htmlDocument
 | S_vv4
 | S_vv3
 | S_scriptletOrSeaWs
 | S_htmlElements
 | S_vv2
 | S_htmlElement
 | S_vv1
 | S_htmlChardata
 | S_htmlMisc
 | S_htmlComment
 | S_script
 | S_style
[@@deriving show]

type tn =
 | S_0 (* DTD *)
 | S_1 (* HTML *)
 | S_2 (* SCRIPTLET *)
 | S_3 (* SEA_WS *)
 | S_4 (* TAG_OPEN *)
 | S_5 (* TAG_CLOSE *)
 | S_6 (* TAG_SCLOSE *)
 | S_7 (* CDATA *)
 | S_8 (* HTML_TEXT *)
 | S_9 (* HTML_COMMENT *)
 | S_10 (* HTML_CONDITIONAL_COMMENT *)
 | S_11 (* SCRIPT_OPEN *)
 | S_12 (* SCRIPT_BODY *)
 | S_13 (* SCRIPT_SHORT_BODY *)
 | S_14 (* STYLE_OPEN *)
 | S_15 (* STYLE_BODY *)
 | S_16 (* STYLE_SHORT_BODY *)
 | S_17 (* TAG_OPEN_h1 *)
 | S_18 (* TAG_OPEN_h2 *)
 | S_19 (* TAG_OPEN_h3 *)
 | S_20 (* TAG_OPEN_h4 *)
 | S_21 (* TAG_OPEN_div *)
 | S_22 (* TAG_OPEN_b *)
 | S_23 (* TAG_OPEN_i *)
 | S_24 (* TAG_OPEN_ul *)
 | S_25 (* TAG_OPEN_ol *)
 | S_26 (* TAG_OPEN_table *)
 | S_27 (* TAG_CLOSE_h1 *)
 | S_28 (* TAG_CLOSE_h2 *)
 | S_29 (* TAG_CLOSE_h3 *)
 | S_30 (* TAG_CLOSE_h4 *)
 | S_31 (* TAG_CLOSE_div *)
 | S_32 (* TAG_CLOSE_b *)
 | S_33 (* TAG_CLOSE_i *)
 | S_34 (* TAG_CLOSE_ul *)
 | S_35 (* TAG_CLOSE_ol *)
 | S_36 (* TAG_CLOSE_table *)
[@@deriving show]

type parse_tree =
 | Node of (nt * parse_tree array)
 | Leaf of (tn * string)
 | PTNull
[@@deriving show]

let restore_leaves w tokens =
  List.zip_exn w tokens
  |> List.map ~f:(fun (lexeme, name) ->
  match name with
  | "DTD" -> Leaf (S_0, lexeme)
  | "HTML" -> Leaf (S_1, lexeme)
  | "SCRIPTLET" -> Leaf (S_2, lexeme)
  | "SEA_WS" -> Leaf (S_3, lexeme)
  | "TAG_OPEN" -> Leaf (S_4, lexeme)
  | "TAG_CLOSE" -> Leaf (S_5, lexeme)
  | "TAG_SCLOSE" -> Leaf (S_6, lexeme)
  | "CDATA" -> Leaf (S_7, lexeme)
  | "HTML_TEXT" -> Leaf (S_8, lexeme)
  | "HTML_COMMENT" -> Leaf (S_9, lexeme)
  | "HTML_CONDITIONAL_COMMENT" -> Leaf (S_10, lexeme)
  | "SCRIPT_OPEN" -> Leaf (S_11, lexeme)
  | "SCRIPT_BODY" -> Leaf (S_12, lexeme)
  | "SCRIPT_SHORT_BODY" -> Leaf (S_13, lexeme)
  | "STYLE_OPEN" -> Leaf (S_14, lexeme)
  | "STYLE_BODY" -> Leaf (S_15, lexeme)
  | "STYLE_SHORT_BODY" -> Leaf (S_16, lexeme)
  | "TAG_OPEN_h1" -> Leaf (S_17, lexeme)
  | "TAG_OPEN_h2" -> Leaf (S_18, lexeme)
  | "TAG_OPEN_h3" -> Leaf (S_19, lexeme)
  | "TAG_OPEN_h4" -> Leaf (S_20, lexeme)
  | "TAG_OPEN_div" -> Leaf (S_21, lexeme)
  | "TAG_OPEN_b" -> Leaf (S_22, lexeme)
  | "TAG_OPEN_i" -> Leaf (S_23, lexeme)
  | "TAG_OPEN_ul" -> Leaf (S_24, lexeme)
  | "TAG_OPEN_ol" -> Leaf (S_25, lexeme)
  | "TAG_OPEN_table" -> Leaf (S_26, lexeme)
  | "TAG_CLOSE_h1" -> Leaf (S_27, lexeme)
  | "TAG_CLOSE_h2" -> Leaf (S_28, lexeme)
  | "TAG_CLOSE_h3" -> Leaf (S_29, lexeme)
  | "TAG_CLOSE_h4" -> Leaf (S_30, lexeme)
  | "TAG_CLOSE_div" -> Leaf (S_31, lexeme)
  | "TAG_CLOSE_b" -> Leaf (S_32, lexeme)
  | "TAG_CLOSE_i" -> Leaf (S_33, lexeme)
  | "TAG_CLOSE_ul" -> Leaf (S_34, lexeme)
  | "TAG_CLOSE_ol" -> Leaf (S_35, lexeme)
  | "TAG_CLOSE_table" -> Leaf (S_36, lexeme)
  | s -> err (sprintf "invalid token name %s" s))

let act get_stack_value pop_stack_value i_rule =
  match i_rule with
  | 0 ->
    ( let children = Array.init 0 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 0;
      let node = Node(S_htmlDocument, children) in
      node )
  | 1 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlDocument, children) in
      node )
  | 2 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlDocument, children) in
      node )
  | 3 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 4 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlDocument, children) in
      node )
  | 5 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 6 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 7 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 8 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 9 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 10 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 11 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 12 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 13 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 14 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlDocument, children) in
      node )
  | 15 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 16 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 17 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 18 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 19 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 20 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 21 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 22 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 23 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 24 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 25 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 26 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 27 ->
    ( let children = Array.init 5 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 5;
      let node = Node(S_htmlDocument, children) in
      node )
  | 28 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 29 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 30 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 31 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 32 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 33 ->
    ( let children = Array.init 5 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 5;
      let node = Node(S_htmlDocument, children) in
      node )
  | 34 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlDocument, children) in
      node )
  | 35 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 36 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 37 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 38 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlDocument, children) in
      node )
  | 39 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 40 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 41 ->
    ( let children = Array.init 5 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 5;
      let node = Node(S_htmlDocument, children) in
      node )
  | 42 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 43 ->
    ( let children = Array.init 5 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 5;
      let node = Node(S_htmlDocument, children) in
      node )
  | 44 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_htmlDocument, children) in
      node )
  | 45 ->
    ( let children = Array.init 5 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 5;
      let node = Node(S_htmlDocument, children) in
      node )
  | 46 ->
    ( let children = Array.init 5 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 5;
      let node = Node(S_htmlDocument, children) in
      node )
  | 47 ->
    ( let children = Array.init 6 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 6;
      let node = Node(S_htmlDocument, children) in
      node )
  | 48 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv4, children) in
      node )
  | 49 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv4, children) in
      node )
  | 50 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv3, children) in
      node )
  | 51 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv3, children) in
      node )
  | 52 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_scriptletOrSeaWs, children) in
      node )
  | 53 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_scriptletOrSeaWs, children) in
      node )
  | 54 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElements, children) in
      node )
  | 55 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElements, children) in
      node )
  | 56 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElements, children) in
      node )
  | 57 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElements, children) in
      node )
  | 58 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv2, children) in
      node )
  | 59 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv2, children) in
      node )
  | 60 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 61 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 62 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 63 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 64 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 65 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 66 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 67 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 68 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 69 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 70 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 71 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 72 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 73 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 74 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 75 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 76 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 77 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 78 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_htmlElement, children) in
      node )
  | 79 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_htmlElement, children) in
      node )
  | 80 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 81 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 82 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 83 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 84 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 85 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 86 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 87 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 88 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlElement, children) in
      node )
  | 89 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 90 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv1, children) in
      node )
  | 91 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlChardata, children) in
      node )
  | 92 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlChardata, children) in
      node )
  | 93 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlMisc, children) in
      node )
  | 94 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlMisc, children) in
      node )
  | 95 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlComment, children) in
      node )
  | 96 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_htmlComment, children) in
      node )
  | 97 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_script, children) in
      node )
  | 98 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_script, children) in
      node )
  | 99 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_style, children) in
      node )
  | 100 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_style, children) in
      node )
  | _ -> err " action not found "
let run_ppda lookup_pda2 lookup_pda3 hint forest : unit =
  let me = ref 1 in
  let st = ref [] in
  for l = 0 to Array.length hint - 1 do
    match hint.(l) with
         | 17 -> (* TAG_OPEN_h1 *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 17);
                    forest.(l) <- !me
         | 18 -> (* TAG_OPEN_h2 *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 18);
                    forest.(l) <- !me
         | 19 -> (* TAG_OPEN_h3 *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 19);
                    forest.(l) <- !me
         | 20 -> (* TAG_OPEN_h4 *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 20);
                    forest.(l) <- !me
         | 21 -> (* TAG_OPEN_div *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 21);
                    forest.(l) <- !me
         | 22 -> (* TAG_OPEN_b *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 22);
                    forest.(l) <- !me
         | 23 -> (* TAG_OPEN_i *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 23);
                    forest.(l) <- !me
         | 24 -> (* TAG_OPEN_ul *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 24);
                    forest.(l) <- !me
         | 25 -> (* TAG_OPEN_ol *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 25);
                    forest.(l) <- !me
         | 26 -> (* TAG_OPEN_table *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 26);
                    forest.(l) <- !me
         | 27 -> (* TAG_CLOSE_h1 *)
                    me := lookup_pda3 (!me, hdi !st, 27);
                    forest.(l) <- !me;
                    st := tl !st
         | 28 -> (* TAG_CLOSE_h2 *)
                    me := lookup_pda3 (!me, hdi !st, 28);
                    forest.(l) <- !me;
                    st := tl !st
         | 29 -> (* TAG_CLOSE_h3 *)
                    me := lookup_pda3 (!me, hdi !st, 29);
                    forest.(l) <- !me;
                    st := tl !st
         | 30 -> (* TAG_CLOSE_h4 *)
                    me := lookup_pda3 (!me, hdi !st, 30);
                    forest.(l) <- !me;
                    st := tl !st
         | 31 -> (* TAG_CLOSE_div *)
                    me := lookup_pda3 (!me, hdi !st, 31);
                    forest.(l) <- !me;
                    st := tl !st
         | 32 -> (* TAG_CLOSE_b *)
                    me := lookup_pda3 (!me, hdi !st, 32);
                    forest.(l) <- !me;
                    st := tl !st
         | 33 -> (* TAG_CLOSE_i *)
                    me := lookup_pda3 (!me, hdi !st, 33);
                    forest.(l) <- !me;
                    st := tl !st
         | 34 -> (* TAG_CLOSE_ul *)
                    me := lookup_pda3 (!me, hdi !st, 34);
                    forest.(l) <- !me;
                    st := tl !st
         | 35 -> (* TAG_CLOSE_ol *)
                    me := lookup_pda3 (!me, hdi !st, 35);
                    forest.(l) <- !me;
                    st := tl !st
         | 36 -> (* TAG_CLOSE_table *)
                    me := lookup_pda3 (!me, hdi !st, 36);
                    forest.(l) <- !me;
                    st := tl !st
         | i ->
            me := lookup_pda2 (!me, i);
            forest.(l) <- !me
       done
let run_epda_no_act lookup_eTrans lookup_epda (m : int array) (hint : int array) =
        let re, irules = lookup_eTrans m.(Array.length hint - 1) in
        if re = 0 then err "Extraction Error: Cannot terminate.";
        let stack =
            ref
            (match hint.(Array.length hint - 1) with
                    | 27 -> [ re ]
        | 28 -> [ re ]
        | 29 -> [ re ]
        | 30 -> [ re ]
        | 31 -> [ re ]
        | 32 -> [ re ]
        | 33 -> [ re ]
        | 34 -> [ re ]
        | 35 -> [ re ]
        | 36 -> [ re ]
        | _ ->  [])
        in
        if Int.equal (Array.length hint - 1) 0 then ()
        else
            let r = ref re in
            for i = Array.length hint - 2 downto 0 do
            let r', irules = lookup_epda (!r, hdi !stack, m.(i)) in
            r := r';
            stack :=
                match hint.(i) with
                        | 17 -> tl !stack
        | 18 -> tl !stack
        | 19 -> tl !stack
        | 20 -> tl !stack
        | 21 -> tl !stack
        | 22 -> tl !stack
        | 23 -> tl !stack
        | 24 -> tl !stack
        | 25 -> tl !stack
        | 26 -> tl !stack
        | 27 -> !r :: !stack
        | 28 -> !r :: !stack
        | 29 -> !r :: !stack
        | 30 -> !r :: !stack
        | 31 -> !r :: !stack
        | 32 -> !r :: !stack
        | 33 -> !r :: !stack
        | 34 -> !r :: !stack
        | 35 -> !r :: !stack
        | 36 -> !r :: !stack
        | _ -> !stack
            done

        
let run_action w (actions : int list array) =
let stack_height = ref 16 in
let value_stack = ref (Array.create ~len:!stack_height PTNull) in
let stack_top = ref (-1) in
let push_stack v =
stack_top := !stack_top + 1;
if !stack_top >= !stack_height then (
    let new_height = !stack_height * 2 in
    let new_value_stack = Array.create ~len:new_height PTNull in
    Array.blit ~src:!value_stack ~src_pos:0 ~dst:new_value_stack ~dst_pos:0
    ~len:!stack_height;
    stack_height := new_height;
    value_stack := new_value_stack);
!value_stack.(!stack_top) <- v
in
let get_stack_value i = !value_stack.(!stack_top - i) in
let pop_stack_value k = stack_top := !stack_top - k in
let run_act acts =
List.iter acts ~f:(fun a ->
    let node = act get_stack_value pop_stack_value a in
    push_stack node)
in
for l = 0 to Array.length w - 1 do
push_stack w.(l);
let acts = actions.(l) in
run_act acts
done;
assert (Int.equal !stack_top 0);
!value_stack.(0)

let stack_height = ref 16
let value_stack : (parse_tree array) ref = ref (Array.create ~len:!stack_height PTNull) 
let stack_top = ref (-1) 
let push_stack v =
stack_top := !stack_top + 1;
if !stack_top >= !stack_height then (
    (* NOTE - enlarge the stack *)
    let new_height = !stack_height * 2 in
    let new_value_stack = Array.create ~len:new_height PTNull in
    Array.blit ~src:!value_stack ~src_pos:0 ~dst:new_value_stack
    ~dst_pos:0 ~len:!stack_height;
    stack_height := new_height;
    value_stack := new_value_stack);
!value_stack.(!stack_top) <- v

let get_stack_value i = !value_stack.(!stack_top - i)
let pop_stack_value k = stack_top := !stack_top - k 

let run_action (acts : t_action) =
    Array.iter acts ~f:(fun a ->
        let node = act get_stack_value pop_stack_value a in
        push_stack node)
    
    let run_epda_act lookup_eTrans lookup_epda (forest : int array) (hint : int array) leaves : parse_tree
        =
      stack_top := -1;
      let i = Array.length hint - 1 in
      let re, irules = lookup_eTrans forest.(i) in
      push_stack leaves.(i);
      run_action irules;
      if re = 0 then err "Extraction Error: Cannot terminate.";
      let stack =
        ref
          (match hint.(i) with
                  | 27 -> [ re ]
        | 28 -> [ re ]
        | 29 -> [ re ]
        | 30 -> [ re ]
        | 31 -> [ re ]
        | 32 -> [ re ]
        | 33 -> [ re ]
        | 34 -> [ re ]
        | 35 -> [ re ]
        | 36 -> [ re ]
        | _ ->  [])
      in
      (if Int.equal i 0 then ()
      else
        let r = ref re in
        for i = Array.length hint - 2 downto 0 do
          let r', irules = lookup_epda (!r, hdi !stack, forest.(i)) in
          push_stack leaves.(i);
          run_action irules;
          r := r';
          stack :=
            match hint.(i) with
                    | 17 -> tl !stack
        | 18 -> tl !stack
        | 19 -> tl !stack
        | 20 -> tl !stack
        | 21 -> tl !stack
        | 22 -> tl !stack
        | 23 -> tl !stack
        | 24 -> tl !stack
        | 25 -> tl !stack
        | 26 -> tl !stack
        | 27 -> !r :: !stack
        | 28 -> !r :: !stack
        | 29 -> !r :: !stack
        | 30 -> !r :: !stack
        | 31 -> !r :: !stack
        | 32 -> !r :: !stack
        | 33 -> !r :: !stack
        | 34 -> !r :: !stack
        | 35 -> !r :: !stack
        | 36 -> !r :: !stack
        | _ -> !stack
        done);
      assert (Int.equal !stack_top 0);
      !value_stack.(0)
      
      