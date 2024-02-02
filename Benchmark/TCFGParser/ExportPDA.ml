module ExportPDA (Dict : IntDict.IntDict) : sig
  val export : string -> unit
  (* val export_csv : string -> unit *)
end = struct
  (* NOTE - PDA in Int *)
  open Core
  open Dict

  let marshall = VMarshall.marshall

  let export path =
    (* NOTE - Store the int PDA etc. as `path/*` *)
    int_trans_eps |> marshall (Filename.concat path "int_trans_eps");
    int_epda |> marshall (Filename.concat path "int_epda");
    (* int2actions |> marshall (Filename.concat path "int2actions"); *)
    int_pda |> marshall (Filename.concat path "int_pda");
    (* leps2funs |> marshall (Filename.concat path "leps2funs"); *)
    int2estate |> Map.to_alist |> marshall (Filename.concat path "int2estate");
    int2sym |> Map.to_alist |> marshall (Filename.concat path "int2sym");
    int2state |> Map.to_alist |> marshall (Filename.concat path "int2state");
    i2rule |> Map.to_alist |> marshall (Filename.concat path "i2rule")

  type ieps = int * (int * int list)
  type ipda = (int * int * int) * int
  type iepda = (int * int * int) * (int * int list)

  let show_int_list (is : int list) : string =
    is |> List.map ~f:Int.to_string |> String.concat ~sep:"," |> sprintf "[%s]"

  let show_ieps (dict : ieps list) : string =
    dict
    |> List.map ~f:(fun (i1, (i2, is)) ->
           sprintf "%d,%d,%s" i1 i2 (show_int_list is))
    |> String.concat ~sep:"\n"

  let show_iepda (dict : iepda list) : string =
    dict
    |> List.map ~f:(fun ((i1, i2, i3), (i4, il)) ->
           sprintf "%d,%d,%d,%d, %s" i1 i2 i3 i4 (show_int_list il))
    |> String.concat ~sep:"\n"

  let show_ipda (dict : ipda list) : string =
    dict
    |> List.map ~f:(fun ((i1, i2, i3), i4) -> sprintf "%d,%d,%d,%d" i1 i2 i3 i4)
    |> String.concat ~sep:"\n"

end
