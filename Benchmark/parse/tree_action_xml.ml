open Core
open TCFGParser.Utils
open TCFGParser.TCFGParseTree

type nt =
 | S_document
 | S_vv3
 | S_prolog
 | S_vv2
 | S_content
 | S_vv1
 | S_element
 | S_reference
 | S_attribute
 | S_chardata
 | S_misc
[@@deriving show]

type tn =
 | S_0 (* XMLDeclOpen *)
 | S_1 (* SPECIAL_CLOSE *)
 | S_2 (* COMMENT *)
 | S_3 (* PI *)
 | S_4 (* CDATA *)
 | S_5 (* TAG_SCLOSE *)
 | S_6 (* EntityRef *)
 | S_7 (* CharRef *)
 | S_8 (* Name *)
 | S_9 (* '=' *)
 | S_10 (* STRING *)
 | S_11 (* TEXT *)
 | S_12 (* SEA_WS *)
 | S_13 (* TAG_OPEN *)
 | S_14 (* TAG_CLOSE *)
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
  | "XMLDeclOpen" -> Leaf (S_0, lexeme)
  | "SPECIAL_CLOSE" -> Leaf (S_1, lexeme)
  | "COMMENT" -> Leaf (S_2, lexeme)
  | "PI" -> Leaf (S_3, lexeme)
  | "CDATA" -> Leaf (S_4, lexeme)
  | "TAG_SCLOSE" -> Leaf (S_5, lexeme)
  | "EntityRef" -> Leaf (S_6, lexeme)
  | "CharRef" -> Leaf (S_7, lexeme)
  | "Name" -> Leaf (S_8, lexeme)
  | "'='" -> Leaf (S_9, lexeme)
  | "STRING" -> Leaf (S_10, lexeme)
  | "TEXT" -> Leaf (S_11, lexeme)
  | "SEA_WS" -> Leaf (S_12, lexeme)
  | "TAG_OPEN" -> Leaf (S_13, lexeme)
  | "TAG_CLOSE" -> Leaf (S_14, lexeme)
  | s -> err (sprintf "invalid token name %s" s))

let act get_stack_value pop_stack_value i_rule =
  match i_rule with
  | 0 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_document, children) in
      node )
  | 1 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_document, children) in
      node )
  | 2 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_document, children) in
      node )
  | 3 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_document, children) in
      node )
  | 4 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_document, children) in
      node )
  | 5 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_document, children) in
      node )
  | 6 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_document, children) in
      node )
  | 7 ->
    ( let children = Array.init 4 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 4;
      let node = Node(S_document, children) in
      node )
  | 8 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv3, children) in
      node )
  | 9 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv3, children) in
      node )
  | 10 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_prolog, children) in
      node )
  | 11 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_prolog, children) in
      node )
  | 12 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv2, children) in
      node )
  | 13 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv2, children) in
      node )
  | 14 ->
    ( let children = Array.init 0 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 0;
      let node = Node(S_content, children) in
      node )
  | 15 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_content, children) in
      node )
  | 16 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_content, children) in
      node )
  | 17 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_content, children) in
      node )
  | 18 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_vv1, children) in
      node )
  | 19 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 20 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_vv1, children) in
      node )
  | 21 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 22 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_vv1, children) in
      node )
  | 23 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 24 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_vv1, children) in
      node )
  | 25 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 26 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_vv1, children) in
      node )
  | 27 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 28 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 29 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv1, children) in
      node )
  | 30 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 31 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv1, children) in
      node )
  | 32 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 33 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv1, children) in
      node )
  | 34 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 35 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv1, children) in
      node )
  | 36 ->
    ( let children = Array.init 2 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 2;
      let node = Node(S_vv1, children) in
      node )
  | 37 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_vv1, children) in
      node )
  | 38 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_element, children) in
      node )
  | 39 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_element, children) in
      node )
  | 40 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_reference, children) in
      node )
  | 41 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_reference, children) in
      node )
  | 42 ->
    ( let children = Array.init 3 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 3;
      let node = Node(S_attribute, children) in
      node )
  | 43 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_chardata, children) in
      node )
  | 44 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_chardata, children) in
      node )
  | 45 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_misc, children) in
      node )
  | 46 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_misc, children) in
      node )
  | 47 ->
    ( let children = Array.init 1 ~f:(fun i -> get_stack_value i) in
      pop_stack_value 1;
      let node = Node(S_misc, children) in
      node )
  | _ -> err " action not found "
let run_ppda lookup_pda2 lookup_pda3 hint forest : unit =
  let me = ref 1 in
  let st = ref [] in
  for l = 0 to Array.length hint - 1 do
    match hint.(l) with
         | 13 -> (* TAG_OPEN *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, 13);
                    forest.(l) <- !me
         | 14 -> (* TAG_CLOSE *)
                    me := lookup_pda3 (!me, hdi !st, 14);
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
                    | 14 -> [ re ]
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
                        | 13 -> tl !stack
        | 14 -> !r :: !stack
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
                  | 14 -> [ re ]
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
                    | 13 -> tl !stack
        | 14 -> !r :: !stack
        | _ -> !stack
        done);
      assert (Int.equal !stack_top 0);
      !value_stack.(0)
      
      