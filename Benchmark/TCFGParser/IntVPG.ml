open Core
open Utils

type iSym = Ic of int | Ir of int | Ip of int [@@deriving show, equal]

type iAlt = Ae | Al of int * int | Am of int * int * int * int
[@@deriving show]

type iRul = int * iAlt list [@@deriving show]
type iGmr = iRul list [@@deriving show]

module Int2 = Cmp (struct
  type t = Int.t * Int.t [@@deriving equal, show, compare, sexp_of, of_sexp]
end)

module Int3 = Cmp (struct
  type t = Int.t * Int.t * Int.t
  [@@deriving equal, show, compare, sexp_of, of_sexp]
end)

type int3 = Int.t * Int.t * Int.t [@@deriving show, compare, equal]

module Int4 = Cmp (struct
  type t = Int.t * Int.t * Int.t * Int.t
  [@@deriving equal, show, compare, sexp_of, of_sexp]
end)

type iTMSet = int list [@@deriving show]

module HashInt2 = struct
  type t = int * int [@@deriving show, compare, sexp_of]

  let equal = phys_equal
  let hash = Hashtbl.hash
end

(* module HashInt3 = struct
     type t = Int.t * Int.t * Int.t
     [@@deriving show, compare, sexp_of, equal]
   end *)

module HashInt3 = struct
  type t = int * int * int [@@deriving show, compare, sexp_of]

  let equal = phys_equal
  let hash = Hashtbl.hash
end
