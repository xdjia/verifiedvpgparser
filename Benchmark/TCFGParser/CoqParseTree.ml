open Core
open Utils
open CoqVPG

include CoqParser.VerifiedParser.DEF

module DEF = struct

  type var = vpg_var [@@deriving equal, show, compare, sexp_of, equal]

  type coq_PlnEdge = [%import: CoqParser.VerifiedParser.DEF.coq_PlnEdge]
  [@@deriving equal, show, compare, sexp_of, equal]

  type coq_CalEdge = [%import: CoqParser.VerifiedParser.DEF.coq_CalEdge]
  [@@deriving equal, show, compare, sexp_of, equal]

  type coq_RetEdge = [%import: CoqParser.VerifiedParser.DEF.coq_RetEdge]
  [@@deriving show, compare, sexp_of, equal]

  type ea = coq_CalEdge option * coq_CalEdge
  [@@deriving show, compare, sexp_of, equal]

  type ec = coq_CalEdge option * coq_PlnEdge
  [@@deriving show, compare, sexp_of, equal]

  type eb = coq_CalEdge option * coq_RetEdge
  [@@deriving show, compare, sexp_of, equal]

  let show_retEdge = function
    | PndRetE (l1, b, l2) ->
        sprintf "%s->%s.%s" (display_vpg_var l1) (cl2str b) (display_vpg_var l2)
    | MatRetE (l, a, l1, b, l2) ->
        sprintf "%s->%s %s %s.%s" (display_vpg_var l) (cl2str a)
          (display_vpg_var l1) (cl2str b) (display_vpg_var l2)

  let show_calEdge = function
    | PndCalE (l1, b, l2) ->
        sprintf "%s->%s.%s" (display_vpg_var l1) (cl2str b) (display_vpg_var l2)
    | MatCalE (l, a, l1, b, l2) ->
        sprintf "%s->%s.%s %s %s" (display_vpg_var l) (cl2str a)
          (display_vpg_var l1) (cl2str b) (display_vpg_var l2)

  let show_plnEdge = function
    | PlnE (l1, b, l2) ->
        sprintf "%s->%s.%s" (display_vpg_var l1) (cl2str b) (display_vpg_var l2)

  type ve = [%import: CoqParser.VerifiedParser.DEF.coq_VE]
  [@@deriving equal, show, compare, sexp_of]

  type coq_VE_list = ve list [@@deriving equal, show, compare, sexp_of]
  type coq_ME = [%import: CoqParser.VerifiedParser.DEF.coq_ME]
end

include DEF

module VE = Cmp (struct
  type t = ve [@@deriving equal, show, compare, sexp_of]
end)

(* module Ea = Cmp (struct
     type t = calEdge option * calEdge [@@deriving equal, show, compare, sexp_of]

     let show (r1, r2) =
       sprintf "(%s,%s)"
         (match r1 with None -> "None" | Some r1 -> show_calEdge r1)
         (show_calEdge r2)
   end)

   module Ec = Cmp (struct
     type t = calEdge option * plnEdge [@@deriving equal, show, compare, sexp_of]

     let show (r1, r2) =
       sprintf "(%s,%s)"
         (match r1 with None -> "None" | Some r1 -> show_calEdge r1)
         (show_plnEdge r2)
   end)

   module Eb = Cmp (struct
     type t = calEdge option * retEdge [@@deriving equal, show, compare, sexp_of]

     let show (r1, r2) =
       sprintf "(%s,%s)"
         (match r1 with None -> "None" | Some r1 -> show_calEdge r1)
         (show_retEdge r2)
   end)

   module MA = struct
     type t = (Ea.t, Ea.comparator_witness) Set.t

     let compare = Set.compare_direct
     let sexp_of_t = Set.sexp_of_m__t (module Ea)

     let show s =
       s |> Set.to_list |> List.map ~f:Ea.show |> String.concat ~sep:";"
       |> sprintf "{ %s }"

     let equal = Set.equal
     let pp (f : Format.formatter) (s : t) : unit = Format.fprintf f "%s" (show s)
   end

   module MB = struct
     type t = (Eb.t, Eb.comparator_witness) Set.t

     let compare = Set.compare_direct
     let sexp_of_t = Set.sexp_of_m__t (module Eb)

     let show s =
       s |> Set.to_list |> List.map ~f:Eb.show |> String.concat ~sep:";"
       |> sprintf "{ %s }"

     let equal = Set.equal
     let pp (f : Format.formatter) (s : t) : unit = Format.fprintf f "%s" (show s)
   end

   module MC = Cmp (struct
     type t = (Ec.t, Ec.comparator_witness) Set.t

     let compare = Set.compare_direct
     let sexp_of_t = Set.sexp_of_m__t (module Ec)

     let show s =
       s |> Set.to_list |> List.map ~f:Ec.show |> String.concat ~sep:";"
       |> sprintf "{ %s }"

     let equal = Set.equal
     let pp (f : Format.formatter) (s : t) : unit = Format.fprintf f "%s" (show s)
   end)
*)

type va_set = Coq_va_set.t
type vc_set = Coq_vc_set.t
type vb_set = Coq_vb_set.t

let show_va_set s = List.map s ~f:show_ea |> String.concat ~sep:";"
let show_vc_set s = List.map s ~f:show_ec |> String.concat ~sep:";"
let show_vb_set s = List.map s ~f:show_eb |> String.concat ~sep:";"

let pp_va_set (f : Format.formatter) (s : va_set) : unit =
  Format.fprintf f "%s" (show_va_set s)

let pp_vc_set (f : Format.formatter) (s : vc_set) : unit =
  Format.fprintf f "%s" (show_vc_set s)

let pp_vb_set (f : Format.formatter) (s : vb_set) : unit =
  Format.fprintf f "%s" (show_vb_set s)

let equal_va_set = Coq_va_set.equal
let equal_vc_set = Coq_vc_set.equal
let equal_vb_set = Coq_vb_set.equal

let compare_va_set s1 s2 =
  Coq_va_set.compare s1 s2 |> function Lt -> -1 | Eq -> 0 | Gt -> 1

let compare_vc_set s1 s2 =
  Coq_vc_set.compare s1 s2 |> function Lt -> -1 | Eq -> 0 | Gt -> 1

let compare_vb_set s1 s2 =
  Coq_vb_set.compare s1 s2 |> function Lt -> -1 | Eq -> 0 | Gt -> 1

let sexp_of_va_set s =
  Sexp.List (s |> Coq_va_set.elements |> List.map ~f:sexp_of_ea)

let sexp_of_vc_set s =
  Sexp.List (s |> Coq_vc_set.elements |> List.map ~f:sexp_of_ec)

let sexp_of_vb_set s =
  Sexp.List (s |> Coq_vb_set.elements |> List.map ~f:sexp_of_eb)

let sexp_of_t = function
  | V0 s -> Sexp.List [ Sexp.Atom "V0"; Sexp.Atom (cl2str s) ]
  | V1 s -> Sexp.List [ Sexp.Atom "V1"; Sexp.Atom (cl2str s) ]

type me_list = CalMEl of va_set | PlnMEl of vc_set | RetMEl of vb_set
[@@deriving equal, show, compare, sexp_of]

module MeList = Cmp (struct
  type t = me_list [@@deriving equal, show, compare, sexp_of]
end)

let cme2cmel m =
  match m with
  | CalCME m -> CalMEl (Coq_va_set.elements m)
  | PlnCME m -> PlnMEl (Coq_vc_set.elements m)
  | RetCME m -> RetMEl (Coq_vb_set.elements m)

module ME = Cmp (struct
  type me = CalME of va_set | PlnME of vc_set | RetME of vb_set
  [@@deriving equal, show, compare, sexp_of]

  let coq_me2me = function
    | CalCME s -> CalME s
    | PlnCME s -> PlnME s
    | RetCME s -> RetME s

  let show_coq_ME m = m |> coq_me2me |> show_me
  let equal_coq_ME m1 m2 = equal_me (coq_me2me m1) (coq_me2me m2)
  let compare_coq_ME m1 m2 = compare_me (coq_me2me m1) (coq_me2me m2)
  let sexp_of_coq_ME m = sexp_of_me (coq_me2me m)

  let pp_coq_ME (f : Format.formatter) (s : coq_ME) : unit =
    Format.fprintf f "%s" (show_coq_ME s)

  type t = coq_ME [@@deriving equal, show, compare, sexp_of]
end)

let is_empty_me = 
  function 
  | CalCME m -> (Coq_va_set.is_empty m)
  | PlnCME m -> (Coq_vc_set.is_empty m)
  | RetCME m -> (Coq_vb_set.is_empty m)

type me = ME.t [@@deriving equal, show, compare, sexp_of]

let filter f = List.filter ~f
let map f = List.map ~f
let fold_left = List.fold_left
let app = List.append
let concat = List.concat
let existsb f = List.exists ~f

let filter_map l f g =
  let l' = filter f l in
  map g l'

let beginE = function
  | Calv va -> (
      match va with PndCalE (l, _, _) -> l | MatCalE (l, _, _, _, _) -> l)
  | Plnv vc ->
      let (PlnE (l, _, _)) = vc in
      l
  | Retv vb -> (
      match vb with PndRetE (l, _, _) -> l | MatRetE (l, _, _, _, _) -> l)

let endE = function
  | Calv va -> (
      match va with PndCalE (_, _, l) -> l | MatCalE (_, _, l, _, _) -> l)
  | Plnv vc ->
      let (PlnE (_, _, l)) = vc in
      l
  | Retv vb -> (
      match vb with PndRetE (_, _, l) -> l | MatRetE (_, _, _, _, l) -> l)

let tl = function [] -> [] | _ :: m -> m

module MeSet = Cmp (struct
  type t = (ME.t, ME.comparator_witness) Set.t

  let compare = Set.compare_direct
  let sexp_of_t = Set.sexp_of_m__t (module ME)
  let show s = s |> Set.to_list |> List.map ~f:ME.show |> String.concat
  let pp (f : Format.formatter) (s : t) : unit = Format.fprintf f "%s" (show s)
  let equal s1 s2 = compare s1 s2 = 0
end)

module TransitionKey = Cmp (struct
  type t = me * me option * symbol [@@deriving show, compare, sexp_of]

  let equal s1 s2 = compare s1 s2 = 0
end)

module Transition = Cmp (struct
  type t = TransitionKey.t * me [@@deriving show, compare, sexp_of]

  let equal s1 s2 = compare s1 s2 = 0
end)

module TransitionSet = Cmp (struct
  type t = (Transition.t, Transition.comparator_witness) Set.t

  let compare = Set.compare_direct
  let sexp_of_t = Set.sexp_of_m__t (module Transition)
  let show s = s |> Set.to_list |> List.map ~f:Transition.show |> String.concat
  let pp (f : Format.formatter) (s : t) : unit = Format.fprintf f "%s" (show s)
  let equal s1 s2 = compare s1 s2 = 0
end)

module ETransitionKey = Cmp (struct
  type t = VE.t * coq_RetEdge option * me
  [@@deriving equal, show, compare, sexp_of]
end)

module ETransition = Cmp (struct
  type t = ETransitionKey.t * ve [@@deriving show, compare, sexp_of]

  let equal s1 s2 = compare s1 s2 = 0
end)

module ETransitionSet = Cmp (struct
  type t = (ETransition.t, ETransition.comparator_witness) Set.t

  let compare = Set.compare_direct
  let sexp_of_t = Set.sexp_of_m__t (module ETransition)

  let show s =
    s |> Set.to_list |> List.map ~f:ETransition.show |> String.concat ~sep:";"

  let pp (f : Format.formatter) (s : t) : unit = Format.fprintf f "%s" (show s)
  let equal s1 s2 = compare s1 s2 = 0
end)

module Show = struct
  module ShowCoqVPG = struct
    let show_nt nt : string =
      match nt with
      | V0 nt -> if String.equal (cl2str nt) "_E" then "" else cl2str nt
      | V1 nt -> cl2str nt

    let show_symbol symbol : string =
      match symbol with
      | Call s -> cl2str s
      | Ret s -> cl2str s
      | Plain s -> cl2str s

    let show_alt (alt : alt) : string =
      match alt with
      | Alt_Epsilon -> "ε"
      | Alt_Linear (i, l) -> show_symbol i ^ show_nt l
      | Alt_Match (a, b, l1, l2) ->
          cl2str a ^ show_nt l1 ^ cl2str b ^ show_nt l2

    let show_rule (l, alt) : string =
      sprintf "%s -> %s ;" (show_nt l) (show_alt alt)

    let show_rules rs : string =
      rs |> List.map ~f:show_rule |> String.concat ~sep:"\n"
  end

  module ShowCoqM = struct
    open ShowCoqVPG

    let show_ra ra =
      match ra with
      | PndCalE (l, a, l1) ->
          sprintf "%s->%s.%s" (show_nt l) (cl2str a) (show_nt l1)
      | MatCalE (l, a, l1, b, l2) ->
          sprintf "%s->%s.%s%s%s" (show_nt l) (cl2str a) (show_nt l1) (cl2str b)
            (show_nt l2)

    let show_rb rb =
      match rb with
      | PndRetE (l, a, l1) ->
          sprintf "%s->%s.%s" (show_nt l) (cl2str a) (show_nt l1)
      | MatRetE (l, a, l1, b, l2) ->
          sprintf "%s->%s%s%s.%s" (show_nt l) (cl2str a) (show_nt l1) (cl2str b)
            (show_nt l2)

    let show_rc rc =
      match rc with
      | PlnE (l, a, l1) ->
          sprintf "%s->%s.%s" (show_nt l) (cl2str a) (show_nt l1)

    let show_ra_op ra_op =
      match ra_op with None -> "None" | Some ra -> show_ra ra

    let show_rb_op rb_op =
      match rb_op with None -> "None" | Some rb -> show_rb rb

    let show_rc_op rc_op =
      match rc_op with None -> "None" | Some rc -> show_rc rc

    let show_Ea (ra_op, ra) = sprintf "(%s,%s)" (show_ra_op ra_op) (show_ra ra)
    let show_Eb (ra_op, rb) = sprintf "(%s,%s)" (show_ra_op ra_op) (show_rb rb)
    let show_Ec (ra_op, rc) = sprintf "(%s,%s)" (show_ra_op ra_op) (show_rc rc)

    let show_MA m =
      m |> Coq_va_set.elements |> List.map ~f:show_Ea |> String.concat ~sep:","
      |> sprintf "{%s}"

    let show_MB m =
      m |> Coq_vb_set.elements |> List.map ~f:show_Eb |> String.concat ~sep:","
      |> sprintf "{%s}"

    let show_MC m =
      m |> Coq_vc_set.elements |> List.map ~f:show_Ec |> String.concat ~sep:","
      |> sprintf "{%s}"

    let show_me = function
      | CalCME m -> show_MA m
      | PlnCME m -> show_MC m
      | RetCME m -> show_MB m
  end

  module ShowCoqV = struct
    open ShowCoqM

    let show_VE ve =
      match ve with
      | Calv va -> show_ra va
      | Plnv vc -> show_rc vc
      | Retv vb -> show_rb vb

    let show_VE_op ve_op =
      match ve_op with None -> "None" | Some ve -> show_VE ve
  end

  module Set = Core.Set

  module Option_me_A_Key = Cmp (struct
    open Base

    type t = (ME.t * symbol) option [@@deriving equal, show, compare, sexp_of]
  end)

  module Option_MA_me_A_Key = Cmp (struct
    open Base

    type t = (ME.t option * ME.t * symbol) option
    [@@deriving equal, show, compare, sexp_of]
  end)

  module Key_MR = Cmp (struct
    open Base

    type t = ME.t option * coq_RetEdge option
    [@@deriving equal, show, compare, sexp_of]
  end)

  module MR = Cmp (struct
    open Base

    type t = ME.t * VE.t [@@deriving equal, show, compare, sexp_of]
  end)

  module Key_MR_MR = Cmp (struct
    open Base

    type t = (ME.t option * coq_RetEdge option) * (ME.t * ve)
    [@@deriving equal, show, compare, sexp_of]
  end)

  module Key_MM = Cmp (struct
    open Base

    type t = ME.t option * ME.t [@@deriving equal, show, compare, sexp_of]
  end)

  module Option_A_Key = Cmp (struct
    open Base

    type t = va_set option [@@deriving equal, show, compare, sexp_of]
  end)

  module Option_me_Key = Cmp (struct
    open Base

    type t = ME.t option [@@deriving equal, show, compare, sexp_of]

    let show m = match m with None -> "None" | Some m -> show_me m
  end)

  module MCM = Cmp (struct
    open Base

    type t = ME.t * symbol * ME.t [@@deriving equal, show, compare, sexp_of]
  end)

  module MAM = Cmp (struct
    open Base

    type t = ME.t * symbol * ME.t [@@deriving equal, show, compare, sexp_of]
  end)
end
