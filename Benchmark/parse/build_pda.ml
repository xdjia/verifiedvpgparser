(* NOTE - Build offline parser PDAs and extraction PDAs. *)

open Core
open TCFGParser
open TCFGParser.CoqVPG
open BuildPDA

(* NOTE - cmd arguments *)
let usage_msg = "Build offline parser PDAs and extraction PDAs."
let g = ref ""
let anon_fun grammar = g := grammar
let speclist = []
let () = Arg.parse speclist anon_fun usage_msg

let tcfg, path =
  match !g with
  | "json" -> (Tcfgs.g_json, sprintf "dict_%s/" !g)
  | "xml" -> (Tcfgs.g_xml, sprintf "dict_%s/" !g)
  | "html" -> (Tcfgs.g_html, sprintf "dict_%s/" !g)
  | _ -> Utils.err "invalid grammars"

module Info = Translation.GInfo (struct
  let tcfg = tcfg
  let grammar_name = !g
end)

module Dict = BuildDict (Info)

module Dict2 = struct
  include Info
  include Dict

  let syms = plainSyms @ callSyms @ retSyms
  
  let () = debug (sprintf "|syms|=%d" (List.length syms))

  let sym2int =
    syms |> List.mapi ~f:(fun i x -> (x, i)) |> Map.of_alist_exn (module Symbol)

  let int2sym =
    syms |> List.mapi ~f:(fun i x -> (i, x)) |> Map.of_alist_exn (module Int)
end

module IDict  = TCFGParser.IntDict.IntDict (Dict2)
module ExpPDA = ExportPDA.ExportPDA (IDict)

let () = ExpPDA.export path
