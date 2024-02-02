open CoqVPG
open CoqParseTree

let edge2rule e : CoqVPG.rule option =
  match e with
  | Calv (PndCalE (l1, a, l2)) -> Some (l1, CoqVPG.Alt_Linear (Call a, l2))
  | Calv (MatCalE (l, a, l1, b, l2)) -> Some (l, CoqVPG.Alt_Match (a, b, l1, l2))
  | Plnv (PlnE (l1, c, l2)) -> Some (l1, CoqVPG.Alt_Linear (Plain c, l2))
  | Retv (PndRetE (l1, b, l2)) -> Some (l1, CoqVPG.Alt_Linear (Ret b, l2))
  | Retv (MatRetE _) -> None
