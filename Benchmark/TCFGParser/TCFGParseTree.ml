(* NOTE - Apply actions to build TCFG parse trees. *)

open Core
open SimpleForm.SimpleForm


type tcfg_pt =
  | Node of (variable * tcfg_pt list)
  | RNode of (variable * tcfg_pt list)
  (* NOTE Leaf of (terminal, Literal) *)
  | Leaf of terminal
  (* NOTE Leaf of (nonterminal, ε) *)
  | ENode of variable

let rec show_tcfg_pt pt : string =
  match pt with
  | ENode nt -> sprintf "(%s ε)" nt
  | Leaf s1 -> sprintf "%s" s1
  | RNode (nt, pts) | Node (nt, pts) ->
      sprintf "(%s %s)" nt
        (List.map pts ~f:show_tcfg_pt |> String.concat ~sep:" ")

let show_value_stack value_stack =
  value_stack |> List.map ~f:show_tcfg_pt |> String.concat ~sep:";"

type t_action = int array
[@@deriving equal]

(* let show_t_action = show_pre_pt_list *)
(* let show_t_action = show_terms_list *)

(* let restore_m (actions : arr_node array array) num_actions w m =
   let wstack = m in
   let wstack_top = ref 0 in
   let nstack = Array.create ~len:num_actions NE in
   let nstack_top = ref 0 in
   let h (child_actions : child_action array) : child array =
     let len_children = Array.length child_actions in
     let children = Array.create ~len:len_children CE in
     for l = 0 to len_children - 1 do
       match child_actions.(l) with
       | CA_NT _ | CA_RE _ ->
           nstack_top := !nstack_top - 1;
           children.(l) <- RefNode (ref nstack.(!nstack_top))
       | CA_Leaf trm ->
           wstack_top := !wstack_top - 1;
           let i = wstack.(!wstack_top) in
           children.(l) <- MLeaf (ref trm, ref w.(i))
       | CA_EX _ -> err "CA_EX"
     done;
     children
   in
   for l = 0 to Array.length actions - 1 do
     wstack.(!wstack_top) <- Array.length actions - 1 - l;
     wstack_top := !wstack_top + 1;
     let actions' = actions.(l) in
     for j = 0 to Array.length actions' - 1 do
       let node =
         match actions'.(j) with
         | NAct (variable, child_actions) ->
             MNode { nt = variable; children = h child_actions }
         | RAct (variable, child_actions) ->
             MRNode { nt = variable; children = h child_actions }
         | EpsAct variable -> MENode variable
       in
       nstack.(!nstack_top) <- node;
       nstack_top := !nstack_top + 1
     done
   done;
   assert (!nstack_top = 1);
   nstack.(0) *)
