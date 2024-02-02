open Core
open CoqVPG
open CoqParseTree
open IntVPG
open TCFGParseTree

let flag_debug = false

let debug s = if flag_debug then print_endline (Printf.sprintf "▶%s◀" s) else ()

module type Tree = sig
  val path : string

  type parse_tree

  val run_ppda :
    (int * int -> int) ->
    (int * int * int -> int) ->
    int array ->
    int array ->
    unit

  val run_epda_no_act :
    (int -> int * t_action) ->
    (int * int * int -> int * t_action) ->
    int array ->
    int array ->
    unit

  val run_epda_act :
    (int -> int * t_action) ->
    (int * int * int -> int * t_action) ->
    int array ->
    int array ->
    parse_tree array ->
    parse_tree

  val value_stack : parse_tree array ref
  val stack_top : int ref
  val push_stack : parse_tree -> unit
  val get_stack_value : int -> parse_tree
  val pop_stack_value : int -> unit
  val run_action : t_action -> unit
  val act : (int -> parse_tree) -> (int -> unit) -> int -> parse_tree
end

module Unmarshall (Info : Tree) : sig
  (* include IntDict.IntDict *)

  val lookup_pda : Int3.t -> int
  val run_ppda : int array -> int array -> unit
  val lookup_sym : symbol -> int
  val lookup_pda : HashInt3.t -> int
  val lookup_epda : HashInt3.t -> int * t_action
  val lookup_eTrans : int -> int * t_action

  (* val run_EPDA : int list -> int array -> int list array *)
  val run_epda_no_act : int array -> int array -> unit

  val run_epda_act :
    int array -> int array -> Info.parse_tree array -> Info.parse_tree

  (* val restore : t_action -> tcfg_pt list -> tcfg_pt list *)
end = struct
  open Info

  let marshall_from name =
    Marshal.from_channel (In_channel.create ?binary:(Some true) name)

  module Var = struct
    type t = CoqVPG.vpg_var [@@deriving show, compare, sexp_of, equal]
  end

  module HashTagged = struct
    type t = symbol [@@deriving show, compare, sexp_of, equal]
  end

  let int_trans_eps : (int * (int * t_action)) list =
    marshall_from (Filename.concat path "int_trans_eps")

  let int_epda : ((int * int * int) * (int * t_action)) list =
    marshall_from (Filename.concat path "int_epda")

  let int_pda : ((int * int * int) * int) list = marshall_from (Filename.concat path "int_pda")
  let int2estate : (int * ve) list = marshall_from (Filename.concat path "int2estate")
  let int2sym : (int * symbol) list = marshall_from (Filename.concat path "int2sym")
  let int2state : (int * me_list) list = marshall_from (Filename.concat path "int2state")
  let i2rule : (int * TCFG.single_rule) list = marshall_from (Filename.concat path "i2rule")
  let int2state = Map.of_alist_exn (module Int) int2state
  let i2rule = Map.of_alist_exn (module Int) i2rule
  let lookup_rule i = Map.find_exn i2rule i

  let pda =
    Hashtbl.of_alist_exn ~growth_allowed:false ~size:(List.length int_pda)
      (module HashInt3)
      int_pda

  let epda =
    Hashtbl.of_alist_exn ~growth_allowed:false ~size:(List.length int_epda)
      (module HashInt3)
      int_epda

  let trans_eps =
    Hashtbl.of_alist_exn ~growth_allowed:false
      ~size:(List.length int_trans_eps)
      (module Int)
      int_trans_eps

  let sym2int =
    int2sym
    |> List.map ~f:(fun (x, y) ->
      (y, x))
    |> Hashtbl.of_alist_exn ~growth_allowed:false ~size:(List.length int2sym)
         (module HashSymbol)

  let state2int =
    int2state |> Map.to_alist
    |> List.map ~f:(fun (x, y) -> (y, x))
    |> Map.of_alist_exn (module MeList)

  let estate2int =
    int2estate
    |> List.map ~f:(fun (x, y) -> (y, x))
    |> Map.of_alist_exn (module VE)

  let lookup_epda = Hashtbl.find_exn epda

  let lookup_epda' =
    int_epda |> List.map ~f:(fun ((r, top, m), v) -> ((m, top, r), v))
    |> fun x ->
    Hashtbl.of_alist_exn ~growth_allowed:false ~size:(List.length x)
      (module HashInt3)
      x
    |> Hashtbl.find_exn

  let lookup_eTrans = Hashtbl.find_exn trans_eps
  let lookup_sym = Hashtbl.find_exn sym2int
  let lookup_pda = Hashtbl.find_exn pda

  let lookup_pda2 =
    int_pda
    |> List.filter_map ~f:(fun t ->
           let (i1, top, i2), v = t in
           match top with 0 -> Some ((i1, i2), v) | _ -> None)
    |> (fun x ->
         Hashtbl.of_alist_exn ~growth_allowed:false ~size:(List.length x)
           (module HashInt2)
           x)
    |> Hashtbl.find_exn

  let lookup_pda3 =
    int_pda
    |> List.filter_map ~f:(fun t ->
           let (i1, top, i2), v = t in
           match top with 0 -> None | _ -> Some t)
    |> (fun x ->
         Hashtbl.of_alist_exn ~growth_allowed:false ~size:(List.length x)
           (module HashInt3)
           x)
    |> Hashtbl.find_exn

  let lookup_trans_eps = Hashtbl.find_exn trans_eps
  let lookup_state = Map.find_exn state2int
  let lookup_estate = Map.find_exn estate2int
  let int2sym = Map.of_alist_exn (module Core.Int) int2sym
  let int2estate = Map.of_alist_exn (module Core.Int) int2estate
  let run_epda_act = run_epda_act lookup_eTrans lookup_epda
  let run_ppda = run_ppda lookup_pda2 lookup_pda3
  let run_epda_no_act = run_epda_no_act lookup_eTrans lookup_epda
end
