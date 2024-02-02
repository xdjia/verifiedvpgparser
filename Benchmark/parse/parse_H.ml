(* H Lexer *)

open TCFGParser.CoqParseTree
open TCFGParser.CoqVPG
open TCFGParser
open Utils
open Core
open BuildPDA
open TCFGParser.TCFGParseTree
open Printf

module G = struct
  let s4 : symbol list =
    "aabb" |> String.to_list
    |> List.map ~f:(fun w ->
           if Char.equal w 'b' then Ret "b"
           else if Char.equal w 'c' then Plain "c"
           else if Char.equal w 'a' then Call "a"
           else err "")

  let s3 : symbol list =
    "aacbbc" |> String.to_list
    |> List.map ~f:(fun w ->
           if Char.equal w 'b' then Ret "b"
           else if Char.equal w 'c' then Plain "c"
           else if Char.equal w 'a' then Call "a"
           else err "")

  let s2 : symbol list =
    "cccaddd" |> String.to_list
    |> List.map ~f:(fun w -> Plain (String.of_char w))

  let s1 : symbol list =
    "aaabccbcccbc" |> String.to_list
    |> List.map ~f:(fun w ->
           if Char.equal w 'b' then Ret "b"
           else if Char.equal w 'c' then Plain "c"
           else if Char.equal w 'a' then Call "a"
           else err "")

  let s5 : symbol list =
    "{c{c[]}}" |> String.to_list
    |> List.map ~f:(fun c ->
           if Char.equal c '}' || Char.equal c ']' then Ret (String.of_char c)
           else if Char.equal c '{' || Char.equal c '[' then
             Call (String.of_char c)
           else Plain (String.of_char c))

  let s6 : symbol list =
  "{abc{abc[abc]abc}abc}" |> String.to_list
  |> List.map ~f:(fun c ->
          if Char.equal c '}' || Char.equal c ']' then Ret (String.of_char c)
          else if Char.equal c '{' || Char.equal c '[' then
            Call (String.of_char c)
          else Plain (String.of_char c))

  let s7 : symbol list =
    "{abcdabcabcd}[]" |> String.to_list
    |> List.map ~f:(fun c ->
            if Char.equal c '}' || Char.equal c ']' then Ret (String.of_char c)
            else if Char.equal c '{' || Char.equal c '[' then
              Call (String.of_char c)
            else Plain (String.of_char c))
end

let name = "vpg7"

let tcfg, s =
  match name with
  | "vpg7" -> (Tcfgs.vpg7, G.s7)
  | "vpg6" -> (Tcfgs.vpg6, G.s6)
  | "vpg5" -> (Tcfgs.vpg5, G.s5)
  | "vpg4" -> (Tcfgs.vpg4, G.s4)
  | "vpg3" -> (Tcfgs.vpg3, G.s3)
  | "vpg2" -> (Tcfgs.vpg2, G.s2)
  | "vpg1" -> (Tcfgs.vpg1, G.s1)
  | _ -> err "Undefined grammar name"

module Info = GInfo (struct
  let tcfg = tcfg
  let grammar_name = "H"
  let c0 = "△"
end)

module Dict = BuildDict (Info)
open Dict

let rec _parse (s : symbol list) w m stack =
  let m1 = List.hd_exn m in
  match s with
  | [] -> (w, m)
  | i :: s -> (
      match i with
      | Call _ ->
          let me =
            match Map.find pda (m1, None, i) with
            | None ->
                let () = debug (show_me m1) in
                err "_parse: call not in pda"
            | Some me -> me
          in
          _parse s (HCall :: w) (me :: m) (m1 :: stack)
      | Plain _ ->
          let me =
            match Map.find pda (List.hd_exn m, None, i) with
            | None ->
                let () = debug (show_me m1) in
                err "_parse: plain not in pda"
            | Some me -> me
          in
          _parse s (HPln :: w) (me :: m) stack
      | Ret _ ->
          let stack_top, stack_tail = split_stack stack in
          let me =
            match Map.find pda (List.hd_exn m, stack_top, i) with
            | None ->
                let () = debug (show_me m1) in
                err "_parse: ret not in pda"
            | Some me -> me
          in
          _parse s (HRet :: w) (me :: m) stack_tail)

(* FIXME - extract has some problem *)
(* let tcfg_pt =
  let h, forest = _parse s [] [ m0 ] [] in
  let v =
    let ss : string list =
      List.map s ~f:(function Ret s | Call s | Plain s -> s) |> List.rev
    in
    extract h ss forest
  in
  v *)

(* let tcfg_pt =
   let t = Unix.gettimeofday () in
   let pt = Info.expand_pt v in
   debug (Printf.sprintf "Conversion time: %f" (Unix.gettimeofday () -. t));
   (* let arr, top = res in *)
   (* let pt = Array.slice arr 0 (top+1) |> Array.to_list in  *)
   (* let t = Unix.gettimeofday () in *)
   (* let pt = show_expanded_pt pt in *)
   (* debug (sprintf "Expand time: %f" (Unix.gettimeofday () -. t)); *)
   (* show_pair_pt pt |> debug; *)
   pt *)

(* let () = debug (Parser.TCFGParseTree.show_tcfg_pt tcfg_pt) *)