
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val add : nat -> nat -> nat **)

let rec add n0 m =
  match n0 with
  | O -> m
  | S p0 -> S (add p0 m)

(** val mul : nat -> nat -> nat **)

let rec mul n0 m =
  match n0 with
  | O -> O
  | S p0 -> add m (mul p0 m)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f0 x y =
  f0 y x

module type DecStrOrder' =
 sig
  type t

  val compare : t -> t -> comparison
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module Compare2EqBool =
 functor (O:DecStrOrder') ->
 struct
  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match O.compare x y with
    | Eq -> true
    | _ -> false
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    let c0 = compSpec2Type x y (O.compare x y) in
    (match c0 with
     | CompLtT -> true
     | _ -> false)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module Nat =
 struct
  (** val eq_dec : nat -> nat -> bool **)

  let rec eq_dec n0 m =
    match n0 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n1 -> (match m with
               | O -> false
               | S n2 -> eq_dec n1 n2)
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p0 -> XO (succ p0)
  | XO p0 -> XI p0
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> XO (add_carry p0 q)
       | XO q -> XI (add p0 q)
       | XH -> XO (succ p0))
    | XO p0 ->
      (match y with
       | XI q -> XI (add p0 q)
       | XO q -> XO (add p0 q)
       | XH -> XI p0)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> XI (add_carry p0 q)
       | XO q -> XO (add_carry p0 q)
       | XH -> XI (succ p0))
    | XO p0 ->
      (match y with
       | XI q -> XO (add_carry p0 q)
       | XO q -> XI (add p0 q)
       | XH -> XO (succ p0))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p0 -> add y (XO (mul p0 y))
    | XO p0 -> XO (mul p0 y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q -> compare_cont r p0 q
       | XO q -> compare_cont Gt p0 q
       | XH -> Gt)
    | XO p0 ->
      (match y with
       | XI q -> compare_cont Lt p0 q
       | XO q -> compare_cont r p0 q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p0 -> (match m with
                  | N0 -> n0
                  | Npos q -> Npos (Pos.add p0 q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p0 -> (match m with
                  | N0 -> N0
                  | Npos q -> Npos (Pos.mul p0 q))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')
 end

(** val compare0 : char -> char -> comparison **)

let compare0 = fun c1 c2 ->
    let cmp = Char.compare c1 c2 in
    if cmp < 0 then Lt else if cmp = 0 then Eq else Gt

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: m -> m

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f0 = function
| [] -> []
| a :: t0 -> (f0 a) :: (map f0 t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f0 l a0 =
  match l with
  | [] -> a0
  | b :: t0 -> fold_left f0 t0 (f0 a0 b)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f0 = function
| [] -> false
| a :: l0 -> (||) (f0 a) (existsb f0 l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f0 = function
| [] -> []
| x :: l0 -> if f0 x then x :: (filter f0 l0) else filter f0 l0

(** val sumbool_of_bool : bool -> bool **)

let sumbool_of_bool = function
| true -> true
| false -> false

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

(** val compare1 : char list -> char list -> comparison **)

let rec compare1 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> Eq
           | _::_ -> Lt)
  | c1::s1' ->
    (match s2 with
     | [] -> Gt
     | c2::s2' -> (match compare0 c1 c2 with
                   | Eq -> compare1 s1' s2'
                   | x -> x))

module PairOrderedType =
 functor (O1:OrderedType) ->
 functor (O2:OrderedType) ->
 struct
  type t = O1.t * O2.t

  (** val eq_dec : (O1.t * O2.t) -> (O1.t * O2.t) -> bool **)

  let eq_dec x y =
    let (a, b) = x in
    let (a0, b0) = y in
    let s = O1.eq_dec a a0 in if s then O2.eq_dec b b0 else false

  (** val compare : (O1.t * O2.t) -> (O1.t * O2.t) -> comparison **)

  let compare x y =
    match O1.compare (fst x) (fst y) with
    | Eq -> O2.compare (snd x) (snd y)
    | x0 -> x0
 end

type 'x compare2 =
| LT
| EQ
| GT

module type Coq_OrderedType =
 sig
  type t

  val compare : t -> t -> t compare2

  val eq_dec : t -> t -> bool
 end

module type OrderedTypeOrig =
 Coq_OrderedType

module Update_OT =
 functor (O:OrderedTypeOrig) ->
 struct
  type t = O.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val compare : O.t -> O.t -> comparison **)

  let compare x y =
    match O.compare x y with
    | LT -> Lt
    | EQ -> Eq
    | GT -> Gt
 end

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module String_as_OT =
 struct
  type t = char list

  (** val cmp : char list -> char list -> comparison **)

  let cmp =
    compare1

  (** val compare : char list -> char list -> char list compare2 **)

  let compare a b =
    match cmp a b with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : char list -> char list -> bool **)

  let eq_dec =
    string_dec
 end

module OrderedTypeLists =
 functor (O:OrderedType) ->
 struct
 end

module MakeRaw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module ML = OrderedTypeLists(X)

  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    []

  (** val is_empty : t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : X.t -> X.t list -> bool **)

  let rec mem x = function
  | [] -> false
  | y :: l ->
    (match X.compare x y with
     | Eq -> true
     | Lt -> false
     | Gt -> mem x l)

  (** val add : X.t -> X.t list -> X.t list **)

  let rec add x s = match s with
  | [] -> x :: []
  | y :: l ->
    (match X.compare x y with
     | Eq -> s
     | Lt -> x :: s
     | Gt -> y :: (add x l))

  (** val singleton : elt -> elt list **)

  let singleton x =
    x :: []

  (** val remove : X.t -> X.t list -> t **)

  let rec remove x s = match s with
  | [] -> []
  | y :: l ->
    (match X.compare x y with
     | Eq -> l
     | Lt -> s
     | Gt -> y :: (remove x l))

  (** val union : t -> t -> t **)

  let rec union s = match s with
  | [] -> (fun s' -> s')
  | x :: l ->
    let rec union_aux s' = match s' with
    | [] -> s
    | x' :: l' ->
      (match X.compare x x' with
       | Eq -> x :: (union l l')
       | Lt -> x :: (union l s')
       | Gt -> x' :: (union_aux l'))
    in union_aux

  (** val inter : t -> t -> t **)

  let rec inter = function
  | [] -> (fun _ -> [])
  | x :: l ->
    let rec inter_aux s' = match s' with
    | [] -> []
    | x' :: l' ->
      (match X.compare x x' with
       | Eq -> x :: (inter l l')
       | Lt -> inter l s'
       | Gt -> inter_aux l')
    in inter_aux

  (** val diff : t -> t -> t **)

  let rec diff s = match s with
  | [] -> (fun _ -> [])
  | x :: l ->
    let rec diff_aux s' = match s' with
    | [] -> s
    | x' :: l' ->
      (match X.compare x x' with
       | Eq -> diff l l'
       | Lt -> x :: (diff l s')
       | Gt -> diff_aux l')
    in diff_aux

  (** val equal : t -> t -> bool **)

  let rec equal s s' =
    match s with
    | [] -> (match s' with
             | [] -> true
             | _ :: _ -> false)
    | x :: l ->
      (match s' with
       | [] -> false
       | x' :: l' -> (match X.compare x x' with
                      | Eq -> equal l l'
                      | _ -> false))

  (** val subset : X.t list -> X.t list -> bool **)

  let rec subset s s' =
    match s with
    | [] -> true
    | x :: l ->
      (match s' with
       | [] -> false
       | x' :: l' ->
         (match X.compare x x' with
          | Eq -> subset l l'
          | Lt -> false
          | Gt -> subset s l'))

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f0 s i =
    fold_left (flip f0) s i

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f0 = function
  | [] -> []
  | x :: l -> if f0 x then x :: (filter f0 l) else filter f0 l

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f0 = function
  | [] -> true
  | x :: l -> if f0 x then for_all f0 l else false

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f0 = function
  | [] -> false
  | x :: l -> if f0 x then true else exists_ f0 l

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f0 = function
  | [] -> ([], [])
  | x :: l ->
    let (s1, s2) = partition f0 l in
    if f0 x then ((x :: s1), s2) else (s1, (x :: s2))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements x =
    x

  (** val min_elt : t -> elt option **)

  let min_elt = function
  | [] -> None
  | x :: _ -> Some x

  (** val max_elt : t -> elt option **)

  let rec max_elt = function
  | [] -> None
  | x :: l -> (match l with
               | [] -> Some x
               | _ :: _ -> max_elt l)

  (** val choose : t -> elt option **)

  let choose =
    min_elt

  (** val compare : X.t list -> X.t list -> comparison **)

  let rec compare s s' =
    match s with
    | [] -> (match s' with
             | [] -> Eq
             | _ :: _ -> Lt)
    | x :: s0 ->
      (match s' with
       | [] -> Gt
       | x' :: s'0 ->
         (match X.compare x x' with
          | Eq -> compare s0 s'0
          | x0 -> x0))

  (** val inf : X.t -> X.t list -> bool **)

  let inf x = function
  | [] -> true
  | y :: _ -> (match X.compare x y with
               | Lt -> true
               | _ -> false)

  (** val isok : X.t list -> bool **)

  let rec isok = function
  | [] -> true
  | x :: l0 -> (&&) (inf x l0) (isok l0)

  module L = MakeListOrdering(X)
 end

module Make =
 functor (X:OrderedType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f0 s =
    Raw.fold f0 (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f0 s =
    Raw.filter f0 (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f0 s =
    Raw.for_all f0 (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f0 s =
    Raw.exists_ f0 (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f0 s =
    let p0 = Raw.partition f0 (this s) in ((fst p0), (snd p0))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)
 end

type 'a c = 'a

(** val ret : 'a1 -> 'a1 c **)

let ret a =
  a

(** val bind : 'a1 c -> ('a1 -> __ -> 'a2 c) -> 'a2 c **)

let bind am bf =
  bf am __

(** val inc : nat -> 'a1 c -> 'a1 c **)

let inc _ xc =
  xc

(** val cons_ct : nat **)

let cons_ct =
  S (S (S (S (S O))))

(** val cons' : 'a1 -> 'a1 list -> 'a1 list c **)

let cons' x xs =
  inc cons_ct (ret (x :: xs))

(** val cost_andb : nat **)

let cost_andb =
  S O

(** val cost_orb : nat **)

let cost_orb =
  S O

(** val cost_existb_branch1 : nat **)

let cost_existb_branch1 =
  S O

(** val cost_existb_branch2 : nat **)

let cost_existb_branch2 =
  S O

(** val cost_existb : ('a1 -> nat) -> 'a1 list -> nat **)

let rec cost_existb cost_f0 = function
| [] -> cost_existb_branch1
| x :: l' ->
  add (add (add (cost_f0 x) cost_orb) (cost_existb cost_f0 l'))
    cost_existb_branch2

(** val existsb' :
    ('a1 -> bool) -> ('a1 -> nat) -> ('a1 -> bool c) -> 'a1 list -> bool c **)

let rec existsb' f0 cost_f0 f'0 = function
| [] -> inc cost_existb_branch1 (ret false)
| x :: l' ->
  bind (f'0 x) (fun fx _ ->
    bind (existsb' f0 cost_f0 f'0 l') (fun res _ ->
      inc (add cost_orb cost_existb_branch2) (ret ((||) fx res))))

(** val app_bt : nat **)

let app_bt =
  S O

(** val app_inner_time : nat **)

let app_inner_time =
  S O

(** val cost_app : 'a1 list -> nat **)

let cost_app l =
  add (mul (add cons_ct app_inner_time) (length l)) app_bt

(** val _app : 'a1 list -> 'a1 list -> 'a1 list c **)

let rec _app l1 l2 =
  match l1 with
  | [] -> inc app_bt (ret l2)
  | a :: l3 ->
    bind (_app l3 l2) (fun l' _ ->
      bind (cons' a l') (fun out _ -> inc app_inner_time (ret out)))

(** val concat_bt : nat **)

let concat_bt =
  S O

(** val concat_inner_time : nat **)

let concat_inner_time =
  S O

(** val cost_concat : 'a1 list list -> nat **)

let rec cost_concat = function
| [] -> concat_bt
| x :: ls' -> add (add (cost_app x) concat_inner_time) (cost_concat ls')

(** val _concat : 'a1 list list -> 'a1 list c **)

let rec _concat = function
| [] -> inc concat_bt (ret [])
| x :: l0 ->
  bind (_concat l0) (fun l' _ ->
    bind (_app x l') (fun out _ -> inc concat_inner_time (ret out)))

(** val tail_bt : nat **)

let tail_bt =
  S O

(** val tail_inner_time : nat **)

let tail_inner_time =
  S O

(** val cost_tail : 'a1 list -> nat **)

let cost_tail = function
| [] -> tail_bt
| _ :: _ -> tail_inner_time

(** val tail' : 'a1 list -> 'a1 list c **)

let tail' = function
| [] -> inc tail_bt (ret [])
| _ :: m -> inc tail_inner_time (ret m)

(** val time_map_branch1 : nat **)

let time_map_branch1 =
  S O

(** val time_map_branch2 : nat **)

let time_map_branch2 =
  S O

(** val cost_map : ('a1 -> nat) -> 'a1 list -> nat **)

let rec cost_map cost_f0 = function
| [] -> time_map_branch1
| x :: l' ->
  add (add (add (cost_f0 x) (cost_map cost_f0 l')) cons_ct) time_map_branch2

(** val map' :
    ('a1 -> 'a2) -> ('a1 -> nat) -> ('a1 -> 'a2 c) -> 'a1 list -> 'a2 list c **)

let rec map' f0 cost_f0 f'0 = function
| [] -> inc time_map_branch1 (ret [])
| x :: l' ->
  bind (map' f0 cost_f0 f'0 l') (fun res _ ->
    bind (f'0 x) (fun fx _ ->
      bind (cons' fx res) (fun out _ -> inc time_map_branch2 (ret out))))

(** val time_pair : nat **)

let time_pair =
  S O

(** val pair' : 'a1 -> 'a2 -> ('a1 * 'a2) c **)

let pair' a b =
  inc time_pair (ret (a, b))

(** val cost_fold_branch1 : nat **)

let cost_fold_branch1 =
  S O

(** val cost_fold_branch2 : nat **)

let cost_fold_branch2 =
  S O

(** val cost_fold :
    ('a1 -> 'a2 -> 'a1) -> ('a1 -> 'a2 -> nat) -> 'a2 list -> 'a1 -> nat **)

let rec cost_fold f0 cost_f0 l a =
  match l with
  | [] -> cost_fold_branch1
  | b :: t0 ->
    add (add (cost_f0 a b) (cost_fold f0 cost_f0 t0 (f0 a b)))
      cost_fold_branch2

(** val fold' :
    ('a1 -> 'a2 -> 'a1) -> ('a1 -> 'a2 -> nat) -> ('a1 -> 'a2 -> 'a1 c) ->
    'a2 list -> 'a1 -> 'a1 c **)

let rec fold' f0 cost_f0 f'0 l a =
  match l with
  | [] -> inc cost_fold_branch1 (ret a)
  | b :: t0 ->
    bind (f'0 a b) (fun fab _ ->
      bind (fold' f0 cost_f0 f'0 t0 fab) (fun out _ ->
        inc cost_fold_branch2 (ret out)))

module Coq_String_as_OT = Update_OT(String_as_OT)

(** val cost_compare_str : nat **)

let cost_compare_str =
  S O

(** val compare_str : char list -> char list -> comparison **)

let compare_str =
  Coq_String_as_OT.compare

(** val compare_str' : char list -> char list -> comparison c **)

let compare_str' x y =
  inc cost_compare_str (ret (compare_str x y))

(** val cost_eq_str : nat **)

let cost_eq_str =
  S O

(** val eq_str : char list -> char list -> bool **)

let eq_str x y =
  match compare_str x y with
  | Eq -> true
  | _ -> false

(** val eq_str' : char list -> char list -> bool c **)

let eq_str' x y =
  inc cost_eq_str (ret (eq_str x y))

module Basic =
 struct
  type terminal = char list

  type variable = char list

  module Coq_variable_as_OT =
   struct
    (** val variable_dec : variable -> variable -> bool **)

    let variable_dec =
      string_dec

    (** val compare : char list -> char list -> comparison **)

    let compare =
      compare_str
   end
 end

module Coq_vpg =
 struct
  type symbol =
  | Call of Basic.terminal
  | Plain of Basic.terminal
  | Ret of Basic.terminal

  (** val symbol_rect :
      (Basic.terminal -> 'a1) -> (Basic.terminal -> 'a1) -> (Basic.terminal
      -> 'a1) -> symbol -> 'a1 **)

  let symbol_rect f0 f1 f2 = function
  | Call t0 -> f0 t0
  | Plain t0 -> f1 t0
  | Ret t0 -> f2 t0

  (** val symbol_rec :
      (Basic.terminal -> 'a1) -> (Basic.terminal -> 'a1) -> (Basic.terminal
      -> 'a1) -> symbol -> 'a1 **)

  let symbol_rec f0 f1 f2 = function
  | Call t0 -> f0 t0
  | Plain t0 -> f1 t0
  | Ret t0 -> f2 t0

  type vpg_var =
  | V0 of Basic.variable
  | V1 of Basic.variable

  (** val vpg_var_rect :
      (Basic.variable -> 'a1) -> (Basic.variable -> 'a1) -> vpg_var -> 'a1 **)

  let vpg_var_rect f0 f1 = function
  | V0 v0 -> f0 v0
  | V1 v0 -> f1 v0

  (** val vpg_var_rec :
      (Basic.variable -> 'a1) -> (Basic.variable -> 'a1) -> vpg_var -> 'a1 **)

  let vpg_var_rec f0 f1 = function
  | V0 v0 -> f0 v0
  | V1 v0 -> f1 v0

  module Coq_symbol_as_OT =
   struct
    type t = symbol

    (** val symbol_dec : symbol -> symbol -> bool **)

    let symbol_dec c1 c2 =
      match c1 with
      | Call t0 ->
        (match c2 with
         | Call t1 -> Basic.Coq_variable_as_OT.variable_dec t0 t1
         | _ -> false)
      | Plain t0 ->
        (match c2 with
         | Plain t1 -> Basic.Coq_variable_as_OT.variable_dec t0 t1
         | _ -> false)
      | Ret t0 ->
        (match c2 with
         | Ret t1 -> Basic.Coq_variable_as_OT.variable_dec t0 t1
         | _ -> false)

    (** val eq_dec : symbol -> symbol -> bool **)

    let eq_dec =
      symbol_dec

    (** val compare : symbol -> symbol -> comparison **)

    let compare x y =
      match x with
      | Call x0 -> (match y with
                    | Call y0 -> compare_str x0 y0
                    | _ -> Lt)
      | Plain x0 ->
        (match y with
         | Call _ -> Gt
         | Plain y0 -> compare_str x0 y0
         | Ret _ -> Lt)
      | Ret x0 -> (match y with
                   | Ret y0 -> compare_str x0 y0
                   | _ -> Gt)

    (** val cost_compare_branch1 : nat **)

    let cost_compare_branch1 =
      S O

    (** val cost_compare_branch2 : nat **)

    let cost_compare_branch2 =
      S O

    (** val cost_compare_branch3 : nat **)

    let cost_compare_branch3 =
      S O

    (** val cost_compare_branch4 : nat **)

    let cost_compare_branch4 =
      S O

    (** val cost_compare_branch5 : nat **)

    let cost_compare_branch5 =
      S O

    (** val cost_compare_branch6 : nat **)

    let cost_compare_branch6 =
      S O

    (** val cost_compare_branch7 : nat **)

    let cost_compare_branch7 =
      S O

    (** val cost_compare : symbol -> symbol -> nat **)

    let cost_compare x y =
      match x with
      | Call _ ->
        (match y with
         | Call _ -> add cost_compare_branch1 cost_eq_str
         | Plain _ -> cost_compare_branch4
         | Ret _ -> cost_compare_branch5)
      | Plain _ ->
        (match y with
         | Call _ -> cost_compare_branch7
         | Plain _ -> add cost_compare_branch2 cost_eq_str
         | Ret _ -> cost_compare_branch6)
      | Ret _ ->
        (match y with
         | Ret _ -> add cost_compare_branch3 cost_eq_str
         | _ -> cost_compare_branch7)

    (** val compare' : symbol -> symbol -> comparison c **)

    let compare' x y =
      match x with
      | Call x0 ->
        (match y with
         | Call y0 ->
           bind (compare_str' x0 y0) (fun out _ ->
             inc cost_compare_branch1 (ret out))
         | Plain _ -> inc cost_compare_branch4 (ret Lt)
         | Ret _ -> inc cost_compare_branch5 (ret Lt))
      | Plain x0 ->
        (match y with
         | Call _ -> inc cost_compare_branch7 (ret Gt)
         | Plain y0 ->
           bind (compare_str' x0 y0) (fun out _ ->
             inc cost_compare_branch2 (ret out))
         | Ret _ -> inc cost_compare_branch6 (ret Lt))
      | Ret x0 ->
        (match y with
         | Ret y0 ->
           bind (compare_str' x0 y0) (fun out _ ->
             inc cost_compare_branch3 (ret out))
         | _ -> inc cost_compare_branch7 (ret Gt))
   end

  module Coq_vpg_var_as_OT =
   struct
    type t = vpg_var

    (** val vpg_var_dec : vpg_var -> vpg_var -> bool **)

    let vpg_var_dec c1 c2 =
      match c1 with
      | V0 v ->
        (match c2 with
         | V0 v0 -> Basic.Coq_variable_as_OT.variable_dec v v0
         | V1 _ -> false)
      | V1 v ->
        (match c2 with
         | V0 _ -> false
         | V1 v0 -> Basic.Coq_variable_as_OT.variable_dec v v0)

    (** val eq_dec : vpg_var -> vpg_var -> bool **)

    let eq_dec =
      vpg_var_dec

    (** val compare : vpg_var -> vpg_var -> comparison **)

    let compare x y =
      match x with
      | V0 x0 ->
        (match y with
         | V0 y0 -> Basic.Coq_variable_as_OT.compare x0 y0
         | V1 _ -> Lt)
      | V1 x0 ->
        (match y with
         | V0 _ -> Gt
         | V1 y0 -> Basic.Coq_variable_as_OT.compare x0 y0)
   end

  type alt =
  | Alt_Epsilon
  | Alt_Linear of symbol * vpg_var
  | Alt_Match of Basic.terminal * Basic.terminal * vpg_var * vpg_var

  module Coq_sot = Compare2EqBool(Coq_symbol_as_OT)

  (** val eqs : symbol -> symbol -> bool **)

  let eqs =
    Coq_sot.eqb

  module Coq_vvot = Compare2EqBool(Coq_vpg_var_as_OT)

  (** val cost_compare_vv_branch1 : nat **)

  let cost_compare_vv_branch1 =
    S O

  (** val cost_compare_vv_branch2 : nat **)

  let cost_compare_vv_branch2 =
    S O

  (** val cost_compare_vv_branch3 : nat **)

  let cost_compare_vv_branch3 =
    S O

  (** val cost_compare_vv : vpg_var -> vpg_var -> nat **)

  let cost_compare_vv x y =
    match x with
    | V0 _ ->
      (match y with
       | V0 _ -> add cost_compare_str cost_compare_vv_branch2
       | V1 _ -> cost_compare_vv_branch1)
    | V1 _ ->
      (match y with
       | V0 _ -> cost_compare_vv_branch3
       | V1 _ -> add cost_compare_str cost_compare_vv_branch2)

  (** val compare_vv' : vpg_var -> vpg_var -> comparison c **)

  let compare_vv' x y =
    match x with
    | V0 x0 ->
      (match y with
       | V0 y0 ->
         inc cost_compare_vv_branch2
           (inc cost_compare_str (ret (compare_str x0 y0)))
       | V1 _ -> inc cost_compare_vv_branch1 (ret Lt))
    | V1 x0 ->
      (match y with
       | V0 _ -> inc cost_compare_vv_branch3 (ret Gt)
       | V1 y0 ->
         inc cost_compare_vv_branch2
           (inc cost_compare_str (ret (compare_str x0 y0))))

  (** val eqvv : vpg_var -> vpg_var -> bool **)

  let eqvv a b =
    match Coq_vpg_var_as_OT.compare a b with
    | Eq -> true
    | _ -> false

  (** val cost_eqvv_branch1 : nat **)

  let cost_eqvv_branch1 =
    S O

  (** val cost_eqvv_branch2 : nat **)

  let cost_eqvv_branch2 =
    S O

  (** val cost_eqvv : vpg_var -> vpg_var -> nat **)

  let cost_eqvv a b =
    add (cost_compare_vv a b)
      (match Coq_vpg_var_as_OT.compare a b with
       | Eq -> cost_eqvv_branch1
       | _ -> cost_eqvv_branch2)

  (** val eqvv' : vpg_var -> vpg_var -> bool c **)

  let eqvv' a b =
    bind (compare_vv' a b) (fun r _ ->
      bind
        (match r with
         | Eq -> inc cost_eqvv_branch1 (ret true)
         | _ -> inc cost_eqvv_branch2 (ret false)) (fun out _ -> ret out))

  type rule = vpg_var * alt

  type rules = rule list
 end

module type VPG =
 sig
  val coq_L_0 : Coq_vpg.vpg_var

  val coq_P : Coq_vpg.rules
 end

module DEF =
 struct
  type var = Coq_vpg.vpg_var

  type coq_PlnEdge =
  | PlnE of var * Basic.terminal * var

  (** val coq_PlnEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rect f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  (** val coq_PlnEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rec f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  type coq_CalEdge =
  | PndCalE of var * Basic.terminal * var
  | MatCalE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_CalEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rect f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_CalEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rec f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_RetEdge =
  | PndRetE of var * Basic.terminal * var
  | MatRetE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_RetEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rect f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_RetEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rec f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_VE =
  | Calv of coq_CalEdge
  | Plnv of coq_PlnEdge
  | Retv of coq_RetEdge

  (** val coq_VE_rect :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rect f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  (** val coq_VE_rec :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rec f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  module Coq_ea_as_OT =
   struct
    type t = coq_CalEdge

    (** val cale_dec : t -> t -> bool **)

    let cale_dec c1 c2 =
      match c1 with
      | PndCalE (l, a, l1) ->
        (match c2 with
         | PndCalE (l0, a0, l2) ->
           if Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l l0
           then if Basic.Coq_variable_as_OT.variable_dec a a0
                then Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l1 l2
                else false
           else false
         | MatCalE (_, _, _, _, _) -> false)
      | MatCalE (l, a, l1, b, l2) ->
        (match c2 with
         | PndCalE (_, _, _) -> false
         | MatCalE (l0, a0, l3, b0, l4) ->
           if Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l l0
           then if Basic.Coq_variable_as_OT.variable_dec a a0
                then if Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l1 l3
                     then if Basic.Coq_variable_as_OT.variable_dec b b0
                          then Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l2 l4
                          else false
                     else false
                else false
           else false)

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      cale_dec

    (** val compare : coq_CalEdge -> coq_CalEdge -> comparison **)

    let compare x y =
      match x with
      | PndCalE (l1, a, l2) ->
        (match y with
         | PndCalE (l1', a', l2') ->
           if negb (eq_str a a')
           then compare_str a a'
           else if negb (Coq_vpg.Coq_vvot.eqb l1 l1')
                then Coq_vpg.Coq_vpg_var_as_OT.compare l1 l1'
                else Coq_vpg.Coq_vpg_var_as_OT.compare l2 l2'
         | MatCalE (_, _, _, _, _) -> Lt)
      | MatCalE (l1, a, l2, b, l3) ->
        (match y with
         | PndCalE (_, _, _) -> Gt
         | MatCalE (l1', a', l2', b', l3') ->
           if negb (eq_str a a')
           then compare_str a a'
           else if negb (eq_str b b')
                then compare_str b b'
                else if negb (Coq_vpg.eqvv l1 l1')
                     then Coq_vpg.Coq_vpg_var_as_OT.compare l1 l1'
                     else if negb (Coq_vpg.eqvv l2 l2')
                          then Coq_vpg.Coq_vpg_var_as_OT.compare l2 l2'
                          else Coq_vpg.Coq_vpg_var_as_OT.compare l3 l3')
   end

  module Coq_ec_as_OT =
   struct
    type t = coq_PlnEdge

    (** val plne_dec : t -> t -> bool **)

    let plne_dec c1 c2 =
      let PlnE (l, c0, l1) = c1 in
      let PlnE (l0, c3, l2) = c2 in
      if Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l l0
      then if Basic.Coq_variable_as_OT.variable_dec c0 c3
           then Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l1 l2
           else false
      else false

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      plne_dec

    (** val compare : coq_PlnEdge -> coq_PlnEdge -> comparison **)

    let compare x y =
      let PlnE (l1, a, l2) = x in
      let PlnE (l1', a', l2') = y in
      if negb (eq_str a a')
      then compare_str a a'
      else if negb (Coq_vpg.Coq_vvot.eqb l1 l1')
           then Coq_vpg.Coq_vpg_var_as_OT.compare l1 l1'
           else Coq_vpg.Coq_vpg_var_as_OT.compare l2 l2'
   end

  module Coq_eb_as_OT =
   struct
    type t = coq_RetEdge

    (** val rete_dec : t -> t -> bool **)

    let rete_dec c1 c2 =
      match c1 with
      | PndRetE (l, b, l1) ->
        (match c2 with
         | PndRetE (l0, b0, l2) ->
           if Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l l0
           then if Basic.Coq_variable_as_OT.variable_dec b b0
                then Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l1 l2
                else false
           else false
         | MatRetE (_, _, _, _, _) -> false)
      | MatRetE (l, a, l1, b, l2) ->
        (match c2 with
         | PndRetE (_, _, _) -> false
         | MatRetE (l0, a0, l3, b0, l4) ->
           if Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l l0
           then if Basic.Coq_variable_as_OT.variable_dec a a0
                then if Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l1 l3
                     then if Basic.Coq_variable_as_OT.variable_dec b b0
                          then Coq_vpg.Coq_vpg_var_as_OT.vpg_var_dec l2 l4
                          else false
                     else false
                else false
           else false)

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      rete_dec

    (** val compare : coq_RetEdge -> coq_RetEdge -> comparison **)

    let compare x y =
      match x with
      | PndRetE (l1, a, l2) ->
        (match y with
         | PndRetE (l1', a', l2') ->
           if negb (eq_str a a')
           then compare_str a a'
           else if negb (Coq_vpg.Coq_vvot.eqb l1 l1')
                then Coq_vpg.Coq_vpg_var_as_OT.compare l1 l1'
                else Coq_vpg.Coq_vpg_var_as_OT.compare l2 l2'
         | MatRetE (_, _, _, _, _) -> Lt)
      | MatRetE (l1, a, l2, b, l3) ->
        (match y with
         | PndRetE (_, _, _) -> Gt
         | MatRetE (l1', a', l2', b', l3') ->
           if negb (eq_str a a')
           then compare_str a a'
           else if negb (eq_str b b')
                then compare_str b b'
                else if negb (Coq_vpg.eqvv l1 l1')
                     then Coq_vpg.Coq_vpg_var_as_OT.compare l1 l1'
                     else if negb (Coq_vpg.eqvv l2 l2')
                          then Coq_vpg.Coq_vpg_var_as_OT.compare l2 l2'
                          else Coq_vpg.Coq_vpg_var_as_OT.compare l3 l3')
   end

  module Coq_vaot = Compare2EqBool(Coq_ea_as_OT)

  module Coq_vcot = Compare2EqBool(Coq_ec_as_OT)

  module Coq_vbot = Compare2EqBool(Coq_eb_as_OT)

  module Coq_opea_as_OT =
   struct
    type t = coq_CalEdge option

    (** val cale_dec : t -> t -> bool **)

    let cale_dec c1 c2 =
      match c1 with
      | Some a ->
        (match c2 with
         | Some a0 -> Coq_ea_as_OT.cale_dec a a0
         | None -> false)
      | None -> (match c2 with
                 | Some _ -> false
                 | None -> true)

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      cale_dec

    (** val compare :
        coq_CalEdge option -> coq_CalEdge option -> comparison **)

    let compare x y =
      match x with
      | Some v1 ->
        (match y with
         | Some v2 -> Coq_ea_as_OT.compare v1 v2
         | None -> Gt)
      | None -> (match y with
                 | Some _ -> Lt
                 | None -> Eq)
   end

  module Coq_ve_as_OT =
   struct
    type t = coq_VE

    (** val ve_dec : coq_VE -> coq_VE -> bool **)

    let ve_dec c1 c2 =
      match c1 with
      | Calv va ->
        (match c2 with
         | Calv va0 -> Coq_ea_as_OT.cale_dec va va0
         | _ -> false)
      | Plnv vc ->
        (match c2 with
         | Plnv vc0 -> Coq_ec_as_OT.plne_dec vc vc0
         | _ -> false)
      | Retv vb ->
        (match c2 with
         | Retv vb0 -> Coq_eb_as_OT.rete_dec vb vb0
         | _ -> false)

    (** val eq_dec : coq_VE -> coq_VE -> bool **)

    let eq_dec =
      ve_dec

    (** val compare : coq_VE -> coq_VE -> comparison **)

    let compare x y =
      match x with
      | Calv v1 ->
        (match y with
         | Calv v2 -> Coq_ea_as_OT.compare v1 v2
         | _ -> Lt)
      | Plnv v1 ->
        (match y with
         | Calv _ -> Gt
         | Plnv v2 -> Coq_ec_as_OT.compare v1 v2
         | Retv _ -> Lt)
      | Retv v1 ->
        (match y with
         | Retv v2 -> Coq_eb_as_OT.compare v1 v2
         | _ -> Gt)
   end

  module Coq_ra_as_OT = PairOrderedType(Coq_opea_as_OT)(Coq_ea_as_OT)

  module Coq_rc_as_OT = PairOrderedType(Coq_opea_as_OT)(Coq_ec_as_OT)

  module Coq_rb_as_OT = PairOrderedType(Coq_opea_as_OT)(Coq_eb_as_OT)

  module Coq_va_set = Make(Coq_ra_as_OT)

  module Coq_vc_set = Make(Coq_rc_as_OT)

  module Coq_vb_set = Make(Coq_rb_as_OT)

  type coq_ME =
  | CalCME of Coq_va_set.t
  | PlnCME of Coq_vc_set.t
  | RetCME of Coq_vb_set.t
 end

module Def =
 functor (G:VPG) ->
 struct
  type var = Coq_vpg.vpg_var

  type coq_PlnEdge = DEF.coq_PlnEdge =
  | PlnE of var * Basic.terminal * var

  (** val coq_PlnEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rect f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  (** val coq_PlnEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rec f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  type coq_CalEdge = DEF.coq_CalEdge =
  | PndCalE of var * Basic.terminal * var
  | MatCalE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_CalEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rect f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_CalEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rec f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_RetEdge = DEF.coq_RetEdge =
  | PndRetE of var * Basic.terminal * var
  | MatRetE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_RetEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rect f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_RetEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rec f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_VE = DEF.coq_VE =
  | Calv of coq_CalEdge
  | Plnv of coq_PlnEdge
  | Retv of coq_RetEdge

  (** val coq_VE_rect :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rect f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  (** val coq_VE_rec :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rec f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  module Coq_ea_as_OT = DEF.Coq_ea_as_OT

  module Coq_ec_as_OT = DEF.Coq_ec_as_OT

  module Coq_eb_as_OT = DEF.Coq_eb_as_OT

  module Coq_vaot = DEF.Coq_vaot

  module Coq_vcot = DEF.Coq_vcot

  module Coq_vbot = DEF.Coq_vbot

  module Coq_opea_as_OT = DEF.Coq_opea_as_OT

  module Coq_ve_as_OT = DEF.Coq_ve_as_OT

  module Coq_ra_as_OT = DEF.Coq_ra_as_OT

  module Coq_rc_as_OT = DEF.Coq_rc_as_OT

  module Coq_rb_as_OT = DEF.Coq_rb_as_OT

  module Coq_va_set = DEF.Coq_va_set

  module Coq_vc_set = DEF.Coq_vc_set

  module Coq_vb_set = DEF.Coq_vb_set

  type coq_ME = DEF.coq_ME =
  | CalCME of Coq_va_set.t
  | PlnCME of Coq_vc_set.t
  | RetCME of Coq_vb_set.t

  (** val coq_ME_rect :
      (Coq_va_set.t -> 'a1) -> (Coq_vc_set.t -> 'a1) -> (Coq_vb_set.t -> 'a1)
      -> coq_ME -> 'a1 **)

  let coq_ME_rect f0 f1 f2 = function
  | CalCME ma -> f0 ma
  | PlnCME mc -> f1 mc
  | RetCME mb -> f2 mb

  (** val coq_ME_rec :
      (Coq_va_set.t -> 'a1) -> (Coq_vc_set.t -> 'a1) -> (Coq_vb_set.t -> 'a1)
      -> coq_ME -> 'a1 **)

  let coq_ME_rec f0 f1 f2 = function
  | CalCME ma -> f0 ma
  | PlnCME mc -> f1 mc
  | RetCME mb -> f2 mb

  (** val coq_L_0 : Coq_vpg.vpg_var **)

  let coq_L_0 =
    G.coq_L_0

  (** val coq_P : Coq_vpg.rules **)

  let coq_P =
    G.coq_P

  module DM =
   struct
   end

  module DF =
   struct
    (** val getSym : DEF.coq_CalEdge -> Coq_vpg.symbol **)

    let getSym = function
    | DEF.PndCalE (_, a, _) -> Coq_vpg.Call a
    | DEF.MatCalE (_, a, _, _, _) -> Coq_vpg.Call a
   end

  module DB =
   struct
    (** val getSym : DEF.coq_RetEdge -> Coq_vpg.symbol **)

    let getSym = function
    | DEF.PndRetE (_, b, _) -> Coq_vpg.Ret b
    | DEF.MatRetE (_, _, _, b, _) -> Coq_vpg.Ret b
   end

  (** val lenM : DEF.coq_ME -> nat **)

  let lenM = function
  | DEF.CalCME m1 -> length (DEF.Coq_va_set.elements m1)
  | DEF.PlnCME m1 -> length (DEF.Coq_vc_set.elements m1)
  | DEF.RetCME m1 -> length (DEF.Coq_vb_set.elements m1)
 end

module Tac =
 functor (G:VPG) ->
 struct
  module Def = Def(G)

  module Tacs =
   struct
   end
 end

module ForwardSmallStep =
 functor (G:VPG) ->
 struct
  module Tac = Tac(G)

  module Def = Tac.Def

  type var = Coq_vpg.vpg_var

  type coq_PlnEdge = DEF.coq_PlnEdge =
  | PlnE of var * Basic.terminal * var

  (** val coq_PlnEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rect f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  (** val coq_PlnEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rec f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  type coq_CalEdge = DEF.coq_CalEdge =
  | PndCalE of var * Basic.terminal * var
  | MatCalE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_CalEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rect f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_CalEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rec f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_RetEdge = DEF.coq_RetEdge =
  | PndRetE of var * Basic.terminal * var
  | MatRetE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_RetEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rect f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_RetEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rec f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_VE = DEF.coq_VE =
  | Calv of coq_CalEdge
  | Plnv of coq_PlnEdge
  | Retv of coq_RetEdge

  (** val coq_VE_rect :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rect f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  (** val coq_VE_rec :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rec f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  module Coq_ea_as_OT = DEF.Coq_ea_as_OT

  module Coq_ec_as_OT = DEF.Coq_ec_as_OT

  module Coq_eb_as_OT = DEF.Coq_eb_as_OT

  module Coq_vaot = DEF.Coq_vaot

  module Coq_vcot = DEF.Coq_vcot

  module Coq_vbot = DEF.Coq_vbot

  module Coq_opea_as_OT = DEF.Coq_opea_as_OT

  module Coq_ve_as_OT = DEF.Coq_ve_as_OT

  module Coq_ra_as_OT = DEF.Coq_ra_as_OT

  module Coq_rc_as_OT = DEF.Coq_rc_as_OT

  module Coq_rb_as_OT = DEF.Coq_rb_as_OT

  module Coq_va_set = DEF.Coq_va_set

  module Coq_vc_set = DEF.Coq_vc_set

  module Coq_vb_set = DEF.Coq_vb_set

  type coq_ME = DEF.coq_ME =
  | CalCME of Coq_va_set.t
  | PlnCME of Coq_vc_set.t
  | RetCME of Coq_vb_set.t

  (** val coq_ME_rect :
      (Coq_va_set.t -> 'a1) -> (Coq_vc_set.t -> 'a1) -> (Coq_vb_set.t -> 'a1)
      -> coq_ME -> 'a1 **)

  let coq_ME_rect f0 f1 f2 = function
  | CalCME ma -> f0 ma
  | PlnCME mc -> f1 mc
  | RetCME mb -> f2 mb

  (** val coq_ME_rec :
      (Coq_va_set.t -> 'a1) -> (Coq_vc_set.t -> 'a1) -> (Coq_vb_set.t -> 'a1)
      -> coq_ME -> 'a1 **)

  let coq_ME_rec f0 f1 f2 = function
  | CalCME ma -> f0 ma
  | PlnCME mc -> f1 mc
  | RetCME mb -> f2 mb

  (** val coq_L_0 : Coq_vpg.vpg_var **)

  let coq_L_0 =
    G.coq_L_0

  (** val coq_P : Coq_vpg.rules **)

  let coq_P =
    G.coq_P

  module DM = Tac.Def.DM

  module DF = Tac.Def.DF

  module DB = Tac.Def.DB

  (** val lenM : DEF.coq_ME -> nat **)

  let lenM = function
  | DEF.CalCME m1 -> length (DEF.Coq_va_set.elements m1)
  | DEF.PlnCME m1 -> length (DEF.Coq_vc_set.elements m1)
  | DEF.RetCME m1 -> length (DEF.Coq_vb_set.elements m1)

  (** val getSym : DEF.coq_CalEdge -> Coq_vpg.symbol **)

  let getSym = function
  | DEF.PndCalE (_, a, _) -> Coq_vpg.Call a
  | DEF.MatCalE (_, a, _, _, _) -> Coq_vpg.Call a

  module Df2 =
   struct
   end

  module Core =
   struct
   end

  module DFX =
   struct
   end

  module Split =
   struct
   end
 end

module BackwardSmallStep =
 functor (G:VPG) ->
 struct
  module ForwardSmallStep = ForwardSmallStep(G)

  module Core =
   struct
   end
 end

module DBX =
 functor (G:VPG) ->
 struct
  module BackwardSmallStep = BackwardSmallStep(G)
 end

module PreTimed =
 functor (G:VPG) ->
 struct
  module Dbx = DBX(G)

  type var = Coq_vpg.vpg_var

  type coq_PlnEdge = DEF.coq_PlnEdge =
  | PlnE of var * Basic.terminal * var

  (** val coq_PlnEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rect f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  (** val coq_PlnEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rec f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  type coq_CalEdge = DEF.coq_CalEdge =
  | PndCalE of var * Basic.terminal * var
  | MatCalE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_CalEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rect f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_CalEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rec f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_RetEdge = DEF.coq_RetEdge =
  | PndRetE of var * Basic.terminal * var
  | MatRetE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_RetEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rect f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_RetEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rec f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_VE = DEF.coq_VE =
  | Calv of coq_CalEdge
  | Plnv of coq_PlnEdge
  | Retv of coq_RetEdge

  (** val coq_VE_rect :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rect f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  (** val coq_VE_rec :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rec f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  module Coq_ea_as_OT = DEF.Coq_ea_as_OT

  module Coq_ec_as_OT = DEF.Coq_ec_as_OT

  module Coq_eb_as_OT = DEF.Coq_eb_as_OT

  module Coq_vaot = DEF.Coq_vaot

  module Coq_vcot = DEF.Coq_vcot

  module Coq_vbot = DEF.Coq_vbot

  module Coq_opea_as_OT = DEF.Coq_opea_as_OT

  module Coq_ve_as_OT = DEF.Coq_ve_as_OT

  module Coq_ra_as_OT = DEF.Coq_ra_as_OT

  module Coq_rc_as_OT = DEF.Coq_rc_as_OT

  module Coq_rb_as_OT = DEF.Coq_rb_as_OT

  module Coq_va_set = DEF.Coq_va_set

  module Coq_vc_set = DEF.Coq_vc_set

  module Coq_vb_set = DEF.Coq_vb_set

  type coq_ME = DEF.coq_ME =
  | CalCME of Coq_va_set.t
  | PlnCME of Coq_vc_set.t
  | RetCME of Coq_vb_set.t

  (** val coq_ME_rect :
      (Coq_va_set.t -> 'a1) -> (Coq_vc_set.t -> 'a1) -> (Coq_vb_set.t -> 'a1)
      -> coq_ME -> 'a1 **)

  let coq_ME_rect f0 f1 f2 = function
  | CalCME ma -> f0 ma
  | PlnCME mc -> f1 mc
  | RetCME mb -> f2 mb

  (** val coq_ME_rec :
      (Coq_va_set.t -> 'a1) -> (Coq_vc_set.t -> 'a1) -> (Coq_vb_set.t -> 'a1)
      -> coq_ME -> 'a1 **)

  let coq_ME_rec f0 f1 f2 = function
  | CalCME ma -> f0 ma
  | PlnCME mc -> f1 mc
  | RetCME mb -> f2 mb

  (** val coq_L_0 : Coq_vpg.vpg_var **)

  let coq_L_0 =
    G.coq_L_0

  (** val coq_P : Coq_vpg.rules **)

  let coq_P =
    G.coq_P

  module DM = Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Def.DM

  module DF = Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Def.DF

  module DB = Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Def.DB

  (** val lenM : DEF.coq_ME -> nat **)

  let lenM = function
  | DEF.CalCME m1 -> length (DEF.Coq_va_set.elements m1)
  | DEF.PlnCME m1 -> length (DEF.Coq_vc_set.elements m1)
  | DEF.RetCME m1 -> length (DEF.Coq_vb_set.elements m1)

  (** val endE : coq_VE -> var **)

  let endE = function
  | Calv va ->
    (match va with
     | PndCalE (_, _, l) -> l
     | MatCalE (_, _, l, _, _) -> l)
  | Plnv vc -> let PlnE (_, _, l) = vc in l
  | Retv vb ->
    (match vb with
     | PndRetE (_, _, l) -> l
     | MatRetE (_, _, _, _, l) -> l)

  (** val beginE : coq_VE -> var **)

  let beginE = function
  | Calv va ->
    (match va with
     | PndCalE (l, _, _) -> l
     | MatCalE (l, _, _, _, _) -> l)
  | Plnv vc -> let PlnE (l, _, _) = vc in l
  | Retv vb ->
    (match vb with
     | PndRetE (l, _, _) -> l
     | MatRetE (l, _, _, _, _) -> l)

  (** val cost_endE : nat **)

  let cost_endE =
    S O

  (** val cost_beginE : nat **)

  let cost_beginE =
    S O

  (** val cons_snd : nat **)

  let cons_snd =
    S O

  (** val _endE : coq_VE -> var c **)

  let _endE = function
  | Calv va ->
    (match va with
     | PndCalE (_, _, l) -> inc cost_endE (ret l)
     | MatCalE (_, _, l, _, _) -> inc cost_endE (ret l))
  | Plnv vc -> let PlnE (_, _, l) = vc in inc cost_endE (ret l)
  | Retv vb ->
    (match vb with
     | PndRetE (_, _, l) -> inc cost_endE (ret l)
     | MatRetE (_, _, _, _, l) -> inc cost_endE (ret l))

  (** val _beginE : coq_VE -> var c **)

  let _beginE = function
  | Calv va ->
    (match va with
     | PndCalE (l, _, _) -> inc cost_beginE (ret l)
     | MatCalE (l, _, _, _, _) -> inc cost_beginE (ret l))
  | Plnv vc -> let PlnE (l, _, _) = vc in inc cost_beginE (ret l)
  | Retv vb ->
    (match vb with
     | PndRetE (l, _, _) -> inc cost_beginE (ret l)
     | MatRetE (l, _, _, _, _) -> inc cost_beginE (ret l))

  (** val ff : coq_VE -> (Coq_vpg.vpg_var * Coq_vpg.alt) -> bool **)

  let ff e = function
  | (l1, y) ->
    (match y with
     | Coq_vpg.Alt_Epsilon -> Coq_vpg.eqvv (endE e) l1
     | _ -> false)

  (** val cost_ff_branch1 : nat **)

  let cost_ff_branch1 =
    S O

  (** val cost_ff_branch2 : nat **)

  let cost_ff_branch2 =
    S O

  (** val cost_ff : coq_VE -> (Coq_vpg.vpg_var * Coq_vpg.alt) -> nat **)

  let cost_ff e = function
  | (l1, y) ->
    (match y with
     | Coq_vpg.Alt_Epsilon ->
       add (add (Coq_vpg.cost_eqvv (endE e) l1) cost_endE) cost_ff_branch1
     | _ -> cost_ff_branch2)

  (** val ff' : coq_VE -> Coq_vpg.rule -> bool c **)

  let ff' e = function
  | (l1, a) ->
    (match a with
     | Coq_vpg.Alt_Epsilon ->
       bind (_endE e) (fun end_of_e _ ->
         inc cost_ff_branch1
           (bind (Coq_vpg.eqvv' end_of_e l1) (fun out _ -> ret out)))
     | _ -> inc cost_ff_branch2 (ret false))

  (** val cost_goEps : Coq_vpg.rules -> coq_VE -> nat **)

  let cost_goEps p0 e =
    cost_existb (cost_ff e) p0

  (** val goEps : coq_VE -> bool **)

  let goEps e =
    existsb (ff e) coq_P

  (** val goEps' : coq_VE -> bool c **)

  let goEps' e =
    existsb' (ff e) (cost_ff e) (ff' e) coq_P
 end

(** val time_nodup_branch0 : nat **)

let time_nodup_branch0 =
  S O

(** val time_nodup_branch1 : nat **)

let time_nodup_branch1 =
  S O

(** val time_nodup_branch2 : nat **)

let time_nodup_branch2 =
  S O

(** val cost_nodup :
    ('a1 -> 'a1 list -> bool) -> ('a1 -> 'a1 list -> nat) -> 'a1 list -> nat **)

let rec cost_nodup inlist0 cost_inlist = function
| [] -> time_nodup_branch0
| x :: xs ->
  add (cost_inlist x xs)
    (if inlist0 x xs
     then add time_nodup_branch1 (cost_nodup inlist0 cost_inlist xs)
     else add (add time_nodup_branch2 cons_ct)
            (cost_nodup inlist0 cost_inlist xs))

(** val nodup : ('a1 -> 'a1 list -> bool) -> 'a1 list -> 'a1 list **)

let rec nodup inlist0 = function
| [] -> []
| x :: xs ->
  if inlist0 x xs
  then nodup inlist0 xs
  else let out1 = nodup inlist0 xs in x :: out1

(** val nodup' :
    ('a1 -> 'a1 list -> bool) -> ('a1 -> 'a1 list -> nat) -> ('a1 -> 'a1 list
    -> bool c) -> 'a1 list -> 'a1 list c **)

let rec nodup' inlist0 cost_inlist inlist' = function
| [] -> inc time_nodup_branch0 (ret [])
| x :: xs ->
  bind (inlist' x xs) (fun b _ ->
    if sumbool_of_bool b
    then bind (nodup' inlist0 cost_inlist inlist' xs) (fun out _ ->
           inc time_nodup_branch1 (ret out))
    else bind (nodup' inlist0 cost_inlist inlist' xs) (fun out1 _ ->
           bind (cons' x out1) (fun out2 _ ->
             inc time_nodup_branch2 (ret out2))))

module Parser =
 functor (G:VPG) ->
 struct
  module PreTimed = PreTimed(G)

  module Dbx = PreTimed.Dbx

  type var = Coq_vpg.vpg_var

  type coq_PlnEdge = DEF.coq_PlnEdge =
  | PlnE of var * Basic.terminal * var

  (** val coq_PlnEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rect f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  (** val coq_PlnEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> coq_PlnEdge -> 'a1 **)

  let coq_PlnEdge_rec f0 = function
  | PlnE (l, c0, l1) -> f0 l c0 l1

  type coq_CalEdge = DEF.coq_CalEdge =
  | PndCalE of var * Basic.terminal * var
  | MatCalE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_CalEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rect f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_CalEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_CalEdge -> 'a1 **)

  let coq_CalEdge_rec f0 f1 = function
  | PndCalE (l, a, l1) -> f0 l a l1
  | MatCalE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_RetEdge = DEF.coq_RetEdge =
  | PndRetE of var * Basic.terminal * var
  | MatRetE of var * Basic.terminal * var * Basic.terminal * var

  (** val coq_RetEdge_rect :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rect f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  (** val coq_RetEdge_rec :
      (var -> Basic.terminal -> var -> 'a1) -> (var -> Basic.terminal -> var
      -> Basic.terminal -> var -> 'a1) -> coq_RetEdge -> 'a1 **)

  let coq_RetEdge_rec f0 f1 = function
  | PndRetE (l, b, l1) -> f0 l b l1
  | MatRetE (l, a, l1, b, l2) -> f1 l a l1 b l2

  type coq_VE = DEF.coq_VE =
  | Calv of coq_CalEdge
  | Plnv of coq_PlnEdge
  | Retv of coq_RetEdge

  (** val coq_VE_rect :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rect f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  (** val coq_VE_rec :
      (coq_CalEdge -> 'a1) -> (coq_PlnEdge -> 'a1) -> (coq_RetEdge -> 'a1) ->
      coq_VE -> 'a1 **)

  let coq_VE_rec f0 f1 f2 = function
  | Calv va -> f0 va
  | Plnv vc -> f1 vc
  | Retv vb -> f2 vb

  module Coq_ea_as_OT = DEF.Coq_ea_as_OT

  module Coq_ec_as_OT = DEF.Coq_ec_as_OT

  module Coq_eb_as_OT = DEF.Coq_eb_as_OT

  module Coq_vaot = DEF.Coq_vaot

  module Coq_vcot = DEF.Coq_vcot

  module Coq_vbot = DEF.Coq_vbot

  module Coq_opea_as_OT = DEF.Coq_opea_as_OT

  module Coq_ve_as_OT = DEF.Coq_ve_as_OT

  module Coq_ra_as_OT = DEF.Coq_ra_as_OT

  module Coq_rc_as_OT = DEF.Coq_rc_as_OT

  module Coq_rb_as_OT = DEF.Coq_rb_as_OT

  module Coq_va_set = DEF.Coq_va_set

  module Coq_vc_set = DEF.Coq_vc_set

  module Coq_vb_set = DEF.Coq_vb_set

  type coq_ME = DEF.coq_ME =
  | CalCME of Coq_va_set.t
  | PlnCME of Coq_vc_set.t
  | RetCME of Coq_vb_set.t

  (** val coq_ME_rect :
      (Coq_va_set.t -> 'a1) -> (Coq_vc_set.t -> 'a1) -> (Coq_vb_set.t -> 'a1)
      -> coq_ME -> 'a1 **)

  let coq_ME_rect f0 f1 f2 = function
  | CalCME ma -> f0 ma
  | PlnCME mc -> f1 mc
  | RetCME mb -> f2 mb

  (** val coq_ME_rec :
      (Coq_va_set.t -> 'a1) -> (Coq_vc_set.t -> 'a1) -> (Coq_vb_set.t -> 'a1)
      -> coq_ME -> 'a1 **)

  let coq_ME_rec f0 f1 f2 = function
  | CalCME ma -> f0 ma
  | PlnCME mc -> f1 mc
  | RetCME mb -> f2 mb

  (** val coq_L_0 : Coq_vpg.vpg_var **)

  let coq_L_0 =
    G.coq_L_0

  (** val coq_P : Coq_vpg.rules **)

  let coq_P =
    G.coq_P

  module DM = Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Def.DM

  module DF = Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Def.DF

  module DB = Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Def.DB

  (** val lenM : DEF.coq_ME -> nat **)

  let lenM = function
  | DEF.CalCME m1 -> length (DEF.Coq_va_set.elements m1)
  | DEF.PlnCME m1 -> length (DEF.Coq_vc_set.elements m1)
  | DEF.RetCME m1 -> length (DEF.Coq_vb_set.elements m1)

  (** val endE : coq_VE -> var **)

  let endE = function
  | Calv va ->
    (match va with
     | PndCalE (_, _, l) -> l
     | MatCalE (_, _, l, _, _) -> l)
  | Plnv vc -> let PlnE (_, _, l) = vc in l
  | Retv vb ->
    (match vb with
     | PndRetE (_, _, l) -> l
     | MatRetE (_, _, _, _, l) -> l)

  (** val beginE : coq_VE -> var **)

  let beginE = function
  | Calv va ->
    (match va with
     | PndCalE (l, _, _) -> l
     | MatCalE (l, _, _, _, _) -> l)
  | Plnv vc -> let PlnE (l, _, _) = vc in l
  | Retv vb ->
    (match vb with
     | PndRetE (l, _, _) -> l
     | MatRetE (l, _, _, _, _) -> l)

  (** val cost_endE : nat **)

  let cost_endE =
    S O

  (** val cost_beginE : nat **)

  let cost_beginE =
    S O

  (** val cons_snd : nat **)

  let cons_snd =
    S O

  (** val _endE : coq_VE -> var c **)

  let _endE = function
  | Calv va ->
    (match va with
     | PndCalE (_, _, l) -> inc cost_endE (ret l)
     | MatCalE (_, _, l, _, _) -> inc cost_endE (ret l))
  | Plnv vc -> let PlnE (_, _, l) = vc in inc cost_endE (ret l)
  | Retv vb ->
    (match vb with
     | PndRetE (_, _, l) -> inc cost_endE (ret l)
     | MatRetE (_, _, _, _, l) -> inc cost_endE (ret l))

  (** val _beginE : coq_VE -> var c **)

  let _beginE = function
  | Calv va ->
    (match va with
     | PndCalE (l, _, _) -> inc cost_beginE (ret l)
     | MatCalE (l, _, _, _, _) -> inc cost_beginE (ret l))
  | Plnv vc -> let PlnE (l, _, _) = vc in inc cost_beginE (ret l)
  | Retv vb ->
    (match vb with
     | PndRetE (l, _, _) -> inc cost_beginE (ret l)
     | MatRetE (l, _, _, _, _) -> inc cost_beginE (ret l))

  (** val ff : coq_VE -> (Coq_vpg.vpg_var * Coq_vpg.alt) -> bool **)

  let ff e = function
  | (l1, y) ->
    (match y with
     | Coq_vpg.Alt_Epsilon -> Coq_vpg.eqvv (endE e) l1
     | _ -> false)

  (** val cost_ff_branch1 : nat **)

  let cost_ff_branch1 =
    S O

  (** val cost_ff_branch2 : nat **)

  let cost_ff_branch2 =
    S O

  (** val cost_ff : coq_VE -> (Coq_vpg.vpg_var * Coq_vpg.alt) -> nat **)

  let cost_ff e = function
  | (l1, y) ->
    (match y with
     | Coq_vpg.Alt_Epsilon ->
       add (add (Coq_vpg.cost_eqvv (endE e) l1) cost_endE) cost_ff_branch1
     | _ -> cost_ff_branch2)

  (** val ff' : coq_VE -> Coq_vpg.rule -> bool c **)

  let ff' e = function
  | (l1, a) ->
    (match a with
     | Coq_vpg.Alt_Epsilon ->
       bind (_endE e) (fun end_of_e _ ->
         inc cost_ff_branch1
           (bind (Coq_vpg.eqvv' end_of_e l1) (fun out _ -> ret out)))
     | _ -> inc cost_ff_branch2 (ret false))

  (** val cost_goEps : Coq_vpg.rules -> coq_VE -> nat **)

  let cost_goEps p0 e =
    cost_existb (cost_ff e) p0

  (** val goEps : coq_VE -> bool **)

  let goEps e =
    existsb (ff e) coq_P

  (** val goEps' : coq_VE -> bool c **)

  let goEps' e =
    existsb' (ff e) (cost_ff e) (ff' e) coq_P

  (** val p_sym : char list **)

  let p_sym =
    []

  (** val m0 : coq_ME **)

  let m0 =
    PlnCME (Coq_vc_set.singleton (None, (PlnE (coq_L_0, p_sym, coq_L_0))))

  (** val findRuleWithLc :
      Coq_vpg.vpg_var -> Coq_vpg.symbol -> (Coq_vpg.vpg_var * Coq_vpg.alt)
      list **)

  let findRuleWithLc l i =
    filter (fun r ->
      let (lr, y) = r in
      (match y with
       | Coq_vpg.Alt_Linear (i', _) ->
         (&&) (Coq_vpg.eqvv lr l) (Coq_vpg.eqs i i')
       | _ -> false)) coq_P

  (** val findRuleWithMa :
      Coq_vpg.vpg_var -> char list -> (Coq_vpg.vpg_var * Coq_vpg.alt) list **)

  let findRuleWithMa l i =
    filter (fun r ->
      let (lr, y) = r in
      (match y with
       | Coq_vpg.Alt_Match (i', _, _, _) ->
         (&&) (Coq_vpg.eqvv lr l) (eqb0 i i')
       | _ -> false)) coq_P

  (** val findRuleWithMb :
      Coq_vpg.vpg_var -> char list -> Coq_vpg.vpg_var -> char list ->
      (Coq_vpg.vpg_var * Coq_vpg.alt) list **)

  let findRuleWithMb l a l1 b =
    filter (fun r ->
      let (lr, y) = r in
      (match y with
       | Coq_vpg.Alt_Match (i', i2, l', _) ->
         (&&)
           ((&&) ((&&) (Coq_vpg.eqvv lr l) (Coq_vpg.eqvv l' l1)) (eqb0 i' a))
           (eqb0 i2 b)
       | _ -> false)) coq_P

  (** val convert2PlainE :
      Coq_vpg.vpg_var -> Basic.terminal -> coq_PlnEdge list **)

  let convert2PlainE l s =
    let rs = findRuleWithLc l (Coq_vpg.Plain s) in
    map (fun r ->
      let (_, y0) = r in
      (match y0 with
       | Coq_vpg.Alt_Linear (_, l') -> PlnE (l, s, l')
       | _ -> PlnE (l, s, l))) rs

  (** val convert2CallLinearE :
      Coq_vpg.vpg_var -> Basic.terminal -> coq_CalEdge list **)

  let convert2CallLinearE l s =
    let rs = findRuleWithLc l (Coq_vpg.Call s) in
    map (fun r ->
      let (_, y0) = r in
      (match y0 with
       | Coq_vpg.Alt_Linear (_, l') -> PndCalE (l, s, l')
       | _ -> PndCalE (l, s, l))) rs

  (** val convert2CallMatchE :
      Coq_vpg.vpg_var -> char list -> coq_CalEdge list **)

  let convert2CallMatchE l s =
    let rs = findRuleWithMa l s in
    map (fun r ->
      let (_, y0) = r in
      (match y0 with
       | Coq_vpg.Alt_Match (_, b, l', l2) -> MatCalE (l, s, l', b, l2)
       | _ -> MatCalE (l, s, l, s, l))) rs

  (** val convert2RetLinearE :
      Coq_vpg.vpg_var -> Basic.terminal -> coq_RetEdge list **)

  let convert2RetLinearE l s =
    let rs = findRuleWithLc l (Coq_vpg.Ret s) in
    map (fun r ->
      let (_, y0) = r in
      (match y0 with
       | Coq_vpg.Alt_Linear (_, l') -> PndRetE (l, s, l')
       | _ -> PndRetE (l, s, l))) rs

  (** val convert2RetMatchE :
      Coq_vpg.vpg_var -> char list -> Coq_vpg.vpg_var -> char list ->
      coq_RetEdge list **)

  let convert2RetMatchE l a l1 s =
    let rs = findRuleWithMb l a l1 s in
    map (fun r ->
      let (_, y0) = r in
      (match y0 with
       | Coq_vpg.Alt_Match (a0, _, _, l') -> MatRetE (l, a0, l1, s, l')
       | _ -> PndRetE (l, s, l))) rs

  (** val e2PlainE : coq_VE -> Basic.terminal -> coq_PlnEdge list **)

  let e2PlainE e' s =
    convert2PlainE (endE e') s

  (** val e2CallLinearE : coq_VE -> Basic.terminal -> coq_CalEdge list **)

  let e2CallLinearE e' s =
    convert2CallLinearE (endE e') s

  (** val e2CallMatchE : coq_VE -> char list -> coq_CalEdge list **)

  let e2CallMatchE e' s =
    convert2CallMatchE (endE e') s

  (** val e2RetLinearE : coq_VE -> Basic.terminal -> coq_RetEdge list **)

  let e2RetLinearE e' s =
    convert2RetLinearE (endE e') s

  (** val va_of_list : Coq_va_set.elt list -> Coq_va_set.t **)

  let va_of_list va =
    fold_left (fun i s -> Coq_va_set.add s i) va Coq_va_set.empty

  (** val vc_of_list : Coq_vc_set.elt list -> Coq_vc_set.t **)

  let vc_of_list vc =
    fold_left (fun i s -> Coq_vc_set.add s i) vc Coq_vc_set.empty

  (** val vb_of_list : Coq_vb_set.elt list -> Coq_vb_set.t **)

  let vb_of_list vb =
    fold_left (fun i s -> Coq_vb_set.add s i) vb Coq_vb_set.empty

  (** val m2PlainM : coq_ME -> Basic.terminal -> coq_ME **)

  let m2PlainM m' s =
    match m' with
    | CalCME m'0 ->
      PlnCME
        (vc_of_list
          (concat
            (map (fun v ->
              let (r, e) = v in map (fun x -> (r, x)) (e2PlainE (Calv e) s))
              (Coq_va_set.elements m'0))))
    | PlnCME m'0 ->
      PlnCME
        (vc_of_list
          (concat
            (map (fun v ->
              let (r, e) = v in map (fun x -> (r, x)) (e2PlainE (Plnv e) s))
              (Coq_vc_set.elements m'0))))
    | RetCME m'0 ->
      PlnCME
        (vc_of_list
          (concat
            (map (fun v ->
              let (r, e) = v in map (fun x -> (r, x)) (e2PlainE (Retv e) s))
              (Coq_vb_set.elements m'0))))

  (** val m2CallM : coq_ME -> Basic.terminal -> coq_ME **)

  let m2CallM m' s =
    match m' with
    | CalCME m'0 ->
      CalCME
        (va_of_list
          (concat
            (map (fun v ->
              let (r, e) = v in
              (match r with
               | Some c0 ->
                 (match c0 with
                  | PndCalE (_, _, _) ->
                    map (fun x -> ((Some x), x))
                      (app (e2CallLinearE (Calv e) s)
                        (e2CallMatchE (Calv e) s))
                  | MatCalE (_, _, _, _, _) ->
                    map (fun x -> ((Some x), x)) (e2CallMatchE (Calv e) s))
               | None ->
                 map (fun x -> ((Some x), x))
                   (app (e2CallLinearE (Calv e) s) (e2CallMatchE (Calv e) s))))
              (Coq_va_set.elements m'0))))
    | PlnCME m'0 ->
      CalCME
        (va_of_list
          (concat
            (map (fun v ->
              let (r, e) = v in
              (match r with
               | Some c0 ->
                 (match c0 with
                  | PndCalE (_, _, _) ->
                    map (fun x -> ((Some x), x))
                      (app (e2CallLinearE (Plnv e) s)
                        (e2CallMatchE (Plnv e) s))
                  | MatCalE (_, _, _, _, _) ->
                    map (fun x -> ((Some x), x)) (e2CallMatchE (Plnv e) s))
               | None ->
                 map (fun x -> ((Some x), x))
                   (app (e2CallLinearE (Plnv e) s) (e2CallMatchE (Plnv e) s))))
              (Coq_vc_set.elements m'0))))
    | RetCME m'0 ->
      CalCME
        (va_of_list
          (concat
            (map (fun v ->
              let (r, e) = v in
              (match r with
               | Some c0 ->
                 (match c0 with
                  | PndCalE (_, _, _) ->
                    map (fun x -> ((Some x), x))
                      (app (e2CallLinearE (Retv e) s)
                        (e2CallMatchE (Retv e) s))
                  | MatCalE (_, _, _, _, _) ->
                    map (fun x -> ((Some x), x)) (e2CallMatchE (Retv e) s))
               | None ->
                 map (fun x -> ((Some x), x))
                   (app (e2CallLinearE (Retv e) s) (e2CallMatchE (Retv e) s))))
              (Coq_vb_set.elements m'0))))

  (** val filter_map :
      'a1 list -> ('a1 -> bool) -> ('a1 -> 'a2) -> 'a2 list **)

  let filter_map l f0 g =
    let l' = filter f0 l in map g l'

  (** val m2RetM : coq_ME -> coq_ME option -> Basic.terminal -> coq_ME **)

  let m2RetM m' t0 s =
    match m' with
    | CalCME m'0 ->
      let m'1 = Coq_va_set.elements m'0 in
      RetCME
      (vb_of_list
        (match t0 with
         | Some m ->
           (match m with
            | CalCME t1 ->
              let t2 = Coq_va_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Calv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Calv te)) lr)
                              (goEps (Calv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Calv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Calv e) s)))))
                  t2)
            | PlnCME t1 ->
              let t2 = Coq_vc_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Plnv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Plnv te)) lr)
                              (goEps (Calv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Calv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Calv e) s)))))
                  t2)
            | RetCME t1 ->
              let t2 = Coq_vb_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Retv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Retv te)) lr)
                              (goEps (Calv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Calv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Calv e) s)))))
                  t2))
         | None ->
           concat
             (map (fun v ->
               let (_, e) = v in
               map (fun e0 -> (None, e0)) (e2RetLinearE (Calv e) s)) m'1)))
    | PlnCME m'0 ->
      let m'1 = Coq_vc_set.elements m'0 in
      RetCME
      (vb_of_list
        (match t0 with
         | Some m ->
           (match m with
            | CalCME t1 ->
              let t2 = Coq_va_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Calv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Calv te)) lr)
                              (goEps (Plnv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Plnv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Plnv e) s)))))
                  t2)
            | PlnCME t1 ->
              let t2 = Coq_vc_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Plnv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Plnv te)) lr)
                              (goEps (Plnv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Plnv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Plnv e) s)))))
                  t2)
            | RetCME t1 ->
              let t2 = Coq_vb_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Retv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Retv te)) lr)
                              (goEps (Plnv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Plnv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Plnv e) s)))))
                  t2))
         | None ->
           concat
             (map (fun v ->
               let (_, e) = v in
               map (fun e0 -> (None, e0)) (e2RetLinearE (Plnv e) s)) m'1)))
    | RetCME m'0 ->
      let m'1 = Coq_vb_set.elements m'0 in
      RetCME
      (vb_of_list
        (match t0 with
         | Some m ->
           (match m with
            | CalCME t1 ->
              let t2 = Coq_va_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Calv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Calv te)) lr)
                              (goEps (Retv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Retv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Retv e) s)))))
                  t2)
            | PlnCME t1 ->
              let t2 = Coq_vc_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Plnv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Plnv te)) lr)
                              (goEps (Retv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Retv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Retv e) s)))))
                  t2)
            | RetCME t1 ->
              let t2 = Coq_vb_set.elements t1 in
              concat
                (map (fun tre ->
                  let (tr, te) = tre in
                  concat
                    (filter_map m'1 (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (lr, _, _) ->
                            Coq_vpg.eqvv (endE (Retv te)) lr
                          | MatCalE (lr, _, _, _, _) ->
                            (&&) (Coq_vpg.eqvv (endE (Retv te)) lr)
                              (goEps (Retv e)))
                       | None -> false)) (fun v ->
                      let (r, e) = v in
                      (match r with
                       | Some c0 ->
                         (match c0 with
                          | PndCalE (_, _, _) ->
                            map (fun e0 -> (tr, e0)) (e2RetLinearE (Retv e) s)
                          | MatCalE (l, a, l1, b, l2) ->
                            if eqb0 s b
                            then (tr, (MatRetE (l, a, l1, b, l2))) :: []
                            else [])
                       | None ->
                         map (fun e0 -> (tr, e0)) (e2RetLinearE (Retv e) s)))))
                  t2))
         | None ->
           concat
             (map (fun v ->
               let (_, e) = v in
               map (fun e0 -> (None, e0)) (e2RetLinearE (Retv e) s)) m'1)))

  (** val p :
      coq_ME -> coq_ME list -> Coq_vpg.symbol -> coq_ME * coq_ME list **)

  let p m t0 = function
  | Coq_vpg.Call s -> let res = m2CallM m s in (res, (m :: t0))
  | Coq_vpg.Plain s -> let res = m2PlainM m s in (res, t0)
  | Coq_vpg.Ret s ->
    (match t0 with
     | [] -> ((m2RetM m None s), [])
     | t1 :: t2 -> ((m2RetM m (Some t1) s), t2))
 end

module TimedSets =
 functor (G:VPG) ->
 struct
  module Parser = Parser(G)

  (** val cost_negb : nat **)

  let cost_negb =
    S O

  module Coq_timed_ea =
   struct
    (** val compare_branch1 : nat **)

    let compare_branch1 =
      S O

    (** val compare_branch2 : nat **)

    let compare_branch2 =
      S O

    (** val compare_branch3 : nat **)

    let compare_branch3 =
      S O

    (** val compare_branch4 : nat **)

    let compare_branch4 =
      S O

    (** val compare_branch5 : nat **)

    let compare_branch5 =
      S O

    (** val compare_branch6 : nat **)

    let compare_branch6 =
      S O

    (** val compare_branch7 : nat **)

    let compare_branch7 =
      S O

    (** val compare_branch8 : nat **)

    let compare_branch8 =
      S O

    (** val compare_branch9 : nat **)

    let compare_branch9 =
      S O

    (** val compare_branch10 : nat **)

    let compare_branch10 =
      S O

    (** val cost_compare : Parser.coq_CalEdge -> Parser.coq_CalEdge -> nat **)

    let cost_compare x y =
      match x with
      | Parser.PndCalE (l1, a, l2) ->
        (match y with
         | Parser.PndCalE (l1', a', l2') ->
           add (add cost_eq_str cost_negb)
             (if negb (eq_str a a')
              then add cost_compare_str compare_branch2
              else add (add (Coq_vpg.cost_eqvv l1 l1') cost_negb)
                     (if negb (Coq_vpg.eqvv l1 l1')
                      then add (Coq_vpg.cost_compare_vv l1 l1')
                             compare_branch3
                      else add (Coq_vpg.cost_compare_vv l2 l2')
                             compare_branch4))
         | Parser.MatCalE (_, _, _, _, _) -> compare_branch1)
      | Parser.MatCalE (l1, a, l2, b, l3) ->
        (match y with
         | Parser.PndCalE (_, _, _) -> compare_branch10
         | Parser.MatCalE (l1', a', l2', b', l3') ->
           add (add cost_eq_str cost_negb)
             (if negb (eq_str a a')
              then add cost_compare_str compare_branch5
              else add (add cost_eq_str cost_negb)
                     (if negb (eq_str b b')
                      then add cost_compare_str compare_branch6
                      else add (add (Coq_vpg.cost_eqvv l1 l1') cost_negb)
                             (if negb (Coq_vpg.eqvv l1 l1')
                              then add (Coq_vpg.cost_compare_vv l1 l1')
                                     compare_branch7
                              else add
                                     (add (Coq_vpg.cost_eqvv l2 l2')
                                       cost_negb)
                                     (if negb (Coq_vpg.eqvv l2 l2')
                                      then add
                                             (Coq_vpg.cost_compare_vv l2 l2')
                                             compare_branch8
                                      else add
                                             (Coq_vpg.cost_compare_vv l3 l3')
                                             compare_branch9)))))

    (** val compare' :
        Parser.coq_CalEdge -> Parser.coq_CalEdge -> comparison c **)

    let compare' a b =
      match a with
      | Parser.PndCalE (l1, a0, l2) ->
        (match b with
         | Parser.PndCalE (l1', a', l2') ->
           if sumbool_of_bool (negb (eq_str a0 a'))
           then inc
                  (add (add (add cost_negb cost_eq_str) cost_compare_str)
                    compare_branch2) (ret (compare_str a0 a'))
           else bind (Coq_vpg.eqvv' l1 l1') (fun res _ ->
                  if sumbool_of_bool (negb res)
                  then bind (Coq_vpg.compare_vv' l1 l1') (fun out _ ->
                         inc
                           (add (add (add cost_negb cost_eq_str) cost_negb)
                             compare_branch3) (ret out))
                  else bind (Coq_vpg.compare_vv' l2 l2') (fun out _ ->
                         inc
                           (add (add (add cost_negb cost_eq_str) cost_negb)
                             compare_branch4) (ret out)))
         | Parser.MatCalE (_, _, _, _, _) -> inc compare_branch1 (ret Lt))
      | Parser.MatCalE (l1, a0, l2, b0, l3) ->
        (match b with
         | Parser.PndCalE (_, _, _) -> inc compare_branch10 (ret Gt)
         | Parser.MatCalE (l1', a', l2', b', l3') ->
           if sumbool_of_bool (negb (eq_str a0 a'))
           then inc
                  (add (add (add cost_negb cost_eq_str) cost_compare_str)
                    compare_branch5) (ret (compare_str a0 a'))
           else if sumbool_of_bool (negb (eq_str b0 b'))
                then inc
                       (add
                         (add
                           (add (add (add cost_negb cost_eq_str) cost_negb)
                             cost_eq_str) cost_compare_str) compare_branch6)
                       (ret (compare_str b0 b'))
                else if sumbool_of_bool (negb (Coq_vpg.eqvv l1 l1'))
                     then bind (Coq_vpg.compare_vv' l1 l1') (fun out _ ->
                            inc
                              (add
                                (add
                                  (add
                                    (add
                                      (add (add cost_negb cost_eq_str)
                                        cost_negb) cost_eq_str) cost_negb)
                                  (Coq_vpg.cost_eqvv l1 l1')) compare_branch7)
                              (ret out))
                     else if sumbool_of_bool (negb (Coq_vpg.eqvv l2 l2'))
                          then bind (Coq_vpg.compare_vv' l2 l2')
                                 (fun out _ ->
                                 inc
                                   (add
                                     (add
                                       (add
                                         (add
                                           (add
                                             (add
                                               (add
                                                 (add cost_negb cost_eq_str)
                                                 cost_negb) cost_eq_str)
                                             cost_negb)
                                           (Coq_vpg.cost_eqvv l1 l1'))
                                         cost_negb)
                                       (Coq_vpg.cost_eqvv l2 l2'))
                                     compare_branch8) (ret out))
                          else bind (Coq_vpg.compare_vv' l3 l3')
                                 (fun out _ ->
                                 inc
                                   (add
                                     (add
                                       (add
                                         (add
                                           (add
                                             (add
                                               (add
                                                 (add cost_negb cost_eq_str)
                                                 cost_negb) cost_eq_str)
                                             cost_negb)
                                           (Coq_vpg.cost_eqvv l1 l1'))
                                         cost_negb)
                                       (Coq_vpg.cost_eqvv l2 l2'))
                                     compare_branch9) (ret out)))
   end

  module Coq_timed_eb =
   struct
    (** val compare_branch1 : nat **)

    let compare_branch1 =
      S O

    (** val compare_branch2 : nat **)

    let compare_branch2 =
      S O

    (** val compare_branch3 : nat **)

    let compare_branch3 =
      S O

    (** val compare_branch4 : nat **)

    let compare_branch4 =
      S O

    (** val compare_branch5 : nat **)

    let compare_branch5 =
      S O

    (** val compare_branch6 : nat **)

    let compare_branch6 =
      S O

    (** val compare_branch7 : nat **)

    let compare_branch7 =
      S O

    (** val compare_branch8 : nat **)

    let compare_branch8 =
      S O

    (** val compare_branch9 : nat **)

    let compare_branch9 =
      S O

    (** val compare_branch10 : nat **)

    let compare_branch10 =
      S O

    (** val cost_compare : Parser.coq_RetEdge -> Parser.coq_RetEdge -> nat **)

    let cost_compare x y =
      match x with
      | Parser.PndRetE (l1, a, l2) ->
        (match y with
         | Parser.PndRetE (l1', a', l2') ->
           add (add cost_eq_str cost_negb)
             (if negb (eq_str a a')
              then add cost_compare_str compare_branch2
              else add (add (Coq_vpg.cost_eqvv l1 l1') cost_negb)
                     (if negb (Coq_vpg.eqvv l1 l1')
                      then add (Coq_vpg.cost_compare_vv l1 l1')
                             compare_branch3
                      else add (Coq_vpg.cost_compare_vv l2 l2')
                             compare_branch4))
         | Parser.MatRetE (_, _, _, _, _) -> compare_branch1)
      | Parser.MatRetE (l1, a, l2, b, l3) ->
        (match y with
         | Parser.PndRetE (_, _, _) -> compare_branch10
         | Parser.MatRetE (l1', a', l2', b', l3') ->
           add (add cost_eq_str cost_negb)
             (if negb (eq_str a a')
              then add cost_compare_str compare_branch5
              else add (add cost_eq_str cost_negb)
                     (if negb (eq_str b b')
                      then add cost_compare_str compare_branch6
                      else add (add (Coq_vpg.cost_eqvv l1 l1') cost_negb)
                             (if negb (Coq_vpg.eqvv l1 l1')
                              then add (Coq_vpg.cost_compare_vv l1 l1')
                                     compare_branch7
                              else add
                                     (add (Coq_vpg.cost_eqvv l2 l2')
                                       cost_negb)
                                     (if negb (Coq_vpg.eqvv l2 l2')
                                      then add
                                             (Coq_vpg.cost_compare_vv l2 l2')
                                             compare_branch8
                                      else add
                                             (Coq_vpg.cost_compare_vv l3 l3')
                                             compare_branch9)))))

    (** val compare' :
        Parser.coq_RetEdge -> Parser.coq_RetEdge -> comparison c **)

    let compare' a b =
      match a with
      | Parser.PndRetE (l1, a0, l2) ->
        (match b with
         | Parser.PndRetE (l1', a', l2') ->
           if sumbool_of_bool (negb (eq_str a0 a'))
           then inc
                  (add (add (add cost_negb cost_eq_str) cost_compare_str)
                    compare_branch2) (ret (compare_str a0 a'))
           else bind (Coq_vpg.eqvv' l1 l1') (fun res _ ->
                  if sumbool_of_bool (negb res)
                  then bind (Coq_vpg.compare_vv' l1 l1') (fun out _ ->
                         inc
                           (add (add (add cost_negb cost_eq_str) cost_negb)
                             compare_branch3) (ret out))
                  else bind (Coq_vpg.compare_vv' l2 l2') (fun out _ ->
                         inc
                           (add (add (add cost_negb cost_eq_str) cost_negb)
                             compare_branch4) (ret out)))
         | Parser.MatRetE (_, _, _, _, _) -> inc compare_branch1 (ret Lt))
      | Parser.MatRetE (l1, a0, l2, b0, l3) ->
        (match b with
         | Parser.PndRetE (_, _, _) -> inc compare_branch10 (ret Gt)
         | Parser.MatRetE (l1', a', l2', b', l3') ->
           if sumbool_of_bool (negb (eq_str a0 a'))
           then inc
                  (add (add (add cost_negb cost_eq_str) cost_compare_str)
                    compare_branch5) (ret (compare_str a0 a'))
           else if sumbool_of_bool (negb (eq_str b0 b'))
                then inc
                       (add
                         (add
                           (add (add (add cost_negb cost_eq_str) cost_negb)
                             cost_eq_str) cost_compare_str) compare_branch6)
                       (ret (compare_str b0 b'))
                else if sumbool_of_bool (negb (Coq_vpg.eqvv l1 l1'))
                     then bind (Coq_vpg.compare_vv' l1 l1') (fun out _ ->
                            inc
                              (add
                                (add
                                  (add
                                    (add
                                      (add (add cost_negb cost_eq_str)
                                        cost_negb) cost_eq_str) cost_negb)
                                  (Coq_vpg.cost_eqvv l1 l1')) compare_branch7)
                              (ret out))
                     else if sumbool_of_bool (negb (Coq_vpg.eqvv l2 l2'))
                          then bind (Coq_vpg.compare_vv' l2 l2')
                                 (fun out _ ->
                                 inc
                                   (add
                                     (add
                                       (add
                                         (add
                                           (add
                                             (add
                                               (add
                                                 (add cost_negb cost_eq_str)
                                                 cost_negb) cost_eq_str)
                                             cost_negb)
                                           (Coq_vpg.cost_eqvv l1 l1'))
                                         cost_negb)
                                       (Coq_vpg.cost_eqvv l2 l2'))
                                     compare_branch8) (ret out))
                          else bind (Coq_vpg.compare_vv' l3 l3')
                                 (fun out _ ->
                                 inc
                                   (add
                                     (add
                                       (add
                                         (add
                                           (add
                                             (add
                                               (add
                                                 (add cost_negb cost_eq_str)
                                                 cost_negb) cost_eq_str)
                                             cost_negb)
                                           (Coq_vpg.cost_eqvv l1 l1'))
                                         cost_negb)
                                       (Coq_vpg.cost_eqvv l2 l2'))
                                     compare_branch9) (ret out)))
   end

  module Coq_timed_ec =
   struct
    (** val compare_branch1 : nat **)

    let compare_branch1 =
      S O

    (** val compare_branch2 : nat **)

    let compare_branch2 =
      S O

    (** val compare_branch3 : nat **)

    let compare_branch3 =
      S O

    (** val compare_branch4 : nat **)

    let compare_branch4 =
      S O

    (** val cost_compare : Parser.coq_PlnEdge -> Parser.coq_PlnEdge -> nat **)

    let cost_compare x y =
      let Parser.PlnE (l1, a, l2) = x in
      let Parser.PlnE (l1', a', l2') = y in
      add (add cost_eq_str cost_negb)
        (if negb (eq_str a a')
         then add cost_compare_str compare_branch2
         else add (add (Coq_vpg.cost_eqvv l1 l1') cost_negb)
                (if negb (Coq_vpg.eqvv l1 l1')
                 then add (Coq_vpg.cost_compare_vv l1 l1') compare_branch3
                 else add (Coq_vpg.cost_compare_vv l2 l2') compare_branch4))

    (** val compare' :
        Parser.coq_PlnEdge -> Parser.coq_PlnEdge -> comparison c **)

    let compare' a b =
      let Parser.PlnE (l1, a0, l2) = a in
      let Parser.PlnE (l1', a', l2') = b in
      if sumbool_of_bool (negb (eq_str a0 a'))
      then inc
             (add (add (add cost_negb cost_eq_str) cost_compare_str)
               compare_branch2) (ret (compare_str a0 a'))
      else bind (Coq_vpg.eqvv' l1 l1') (fun res _ ->
             if sumbool_of_bool (negb res)
             then bind (Coq_vpg.compare_vv' l1 l1') (fun out _ ->
                    inc
                      (add (add (add cost_negb cost_eq_str) cost_negb)
                        compare_branch3) (ret out))
             else bind (Coq_vpg.compare_vv' l2 l2') (fun out _ ->
                    inc
                      (add (add (add cost_negb cost_eq_str) cost_negb)
                        compare_branch4) (ret out)))
   end

  module Coq_timed_op_ea =
   struct
    (** val compare_branch1 : nat **)

    let compare_branch1 =
      S O

    (** val compare_branch2 : nat **)

    let compare_branch2 =
      S O

    (** val compare_branch3 : nat **)

    let compare_branch3 =
      S O

    (** val compare_branch4 : nat **)

    let compare_branch4 =
      S O

    (** val cost_compare :
        Parser.Coq_ea_as_OT.t option -> Parser.Coq_ea_as_OT.t option -> nat **)

    let cost_compare a b =
      match a with
      | Some a0 ->
        (match b with
         | Some b0 -> add (Coq_timed_ea.cost_compare a0 b0) compare_branch4
         | None -> compare_branch3)
      | None ->
        (match b with
         | Some _ -> compare_branch2
         | None -> compare_branch1)

    (** val compare' :
        Parser.Coq_ea_as_OT.t option -> Parser.Coq_ea_as_OT.t option ->
        comparison c **)

    let compare' a b =
      match a with
      | Some a0 ->
        (match b with
         | Some b0 ->
           bind (Coq_timed_ea.compare' a0 b0) (fun out _ ->
             inc compare_branch4 (ret out))
         | None -> inc compare_branch3 (ret Gt))
      | None ->
        (match b with
         | Some _ -> inc compare_branch2 (ret Lt)
         | None -> inc compare_branch1 (ret Eq))
   end

  module Coq_timed_ra =
   struct
    (** val va_compare :
        Parser.Coq_va_set.t -> Parser.Coq_va_set.t -> comparison **)

    let va_compare =
      Parser.Coq_va_set.compare

    (** val compare :
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) ->
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) -> comparison **)

    let compare x y =
      match Parser.Coq_opea_as_OT.compare (fst x) (fst y) with
      | Eq -> Parser.Coq_ea_as_OT.compare (snd x) (snd y)
      | x0 -> x0

    (** val compare_branch1 : nat **)

    let compare_branch1 =
      S O

    (** val compare_branch2 : nat **)

    let compare_branch2 =
      S O

    (** val compare_branch3 : nat **)

    let compare_branch3 =
      S O

    (** val cost_compare :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_CalEdge) ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_CalEdge) -> nat **)

    let cost_compare x y =
      add (Coq_timed_op_ea.cost_compare (fst x) (fst y))
        (match Parser.Coq_opea_as_OT.compare (fst x) (fst y) with
         | Eq ->
           add compare_branch1 (Coq_timed_ea.cost_compare (snd x) (snd y))
         | Lt -> compare_branch2
         | Gt -> compare_branch3)

    (** val compare' :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_CalEdge) ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_CalEdge) -> comparison c **)

    let compare' x y =
      bind (Coq_timed_op_ea.compare' (fst x) (fst y)) (fun out1 _ ->
        bind
          (match out1 with
           | Eq ->
             bind (Coq_timed_ea.compare' (snd x) (snd y)) (fun out _ ->
               inc compare_branch1 (ret out))
           | Lt -> inc compare_branch2 (ret Lt)
           | Gt -> inc compare_branch3 (ret Gt)) (fun out _ -> ret out))
   end

  module Coq_timed_va_set =
   struct
    (** val raw_equal :
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) list ->
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) list -> bool **)

    let rec raw_equal s s' =
      match s with
      | [] -> (match s' with
               | [] -> true
               | _ :: _ -> false)
      | x :: l ->
        (match s' with
         | [] -> false
         | x' :: l' ->
           (match Coq_timed_ra.compare x x' with
            | Eq -> raw_equal l l'
            | _ -> false))

    (** val cost_branch1 : nat **)

    let cost_branch1 =
      S O

    (** val cost_branch2 : nat **)

    let cost_branch2 =
      S O

    (** val cost_branch3 : nat **)

    let cost_branch3 =
      S O

    (** val cost_branch4 : nat **)

    let cost_branch4 =
      S O

    (** val cost_raw_equal :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_CalEdge) list ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_CalEdge) list -> nat **)

    let rec cost_raw_equal s s' =
      match s with
      | [] -> (match s' with
               | [] -> cost_branch1
               | _ :: _ -> cost_branch4)
      | x :: l ->
        (match s' with
         | [] -> cost_branch4
         | x' :: l' ->
           add (Coq_timed_ra.cost_compare x x')
             (match Coq_timed_ra.compare x x' with
              | Eq -> add cost_branch2 (cost_raw_equal l l')
              | _ -> cost_branch3))

    (** val raw_equal' :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_CalEdge) list ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_CalEdge) list -> bool c **)

    let rec raw_equal' s s' =
      match s with
      | [] ->
        (match s' with
         | [] -> inc cost_branch1 (ret true)
         | _ :: _ -> inc cost_branch4 (ret false))
      | x :: l ->
        (match s' with
         | [] -> inc cost_branch4 (ret false)
         | x' :: l' ->
           bind (Coq_timed_ra.compare' x x') (fun out1 _ ->
             bind
               (match out1 with
                | Eq ->
                  bind (raw_equal' l l') (fun out _ ->
                    inc cost_branch2 (ret out))
                | _ -> inc cost_branch3 (ret false)) (fun out _ -> ret out)))

    (** val equal : Parser.Coq_va_set.t_ -> Parser.Coq_va_set.t_ -> bool **)

    let equal s s' =
      raw_equal (Parser.Coq_va_set.this s) (Parser.Coq_va_set.this s')

    (** val cost_equal :
        Parser.Coq_va_set.t_ -> Parser.Coq_va_set.t_ -> nat **)

    let cost_equal s s' =
      cost_raw_equal (Parser.Coq_va_set.this s) (Parser.Coq_va_set.this s')

    (** val equal' :
        Parser.Coq_va_set.t_ -> Parser.Coq_va_set.t_ -> bool c **)

    let equal' s s' =
      raw_equal' (Parser.Coq_va_set.this s) (Parser.Coq_va_set.this s')
   end

  module Coq_timed_rb =
   struct
    (** val vb_compare :
        Parser.Coq_vb_set.t -> Parser.Coq_vb_set.t -> comparison **)

    let vb_compare =
      Parser.Coq_vb_set.compare

    (** val compare :
        (Parser.coq_CalEdge option * Parser.coq_RetEdge) ->
        (Parser.coq_CalEdge option * Parser.coq_RetEdge) -> comparison **)

    let compare x y =
      match Parser.Coq_opea_as_OT.compare (fst x) (fst y) with
      | Eq -> Parser.Coq_eb_as_OT.compare (snd x) (snd y)
      | x0 -> x0

    (** val compare_branch1 : nat **)

    let compare_branch1 =
      S O

    (** val compare_branch2 : nat **)

    let compare_branch2 =
      S O

    (** val compare_branch3 : nat **)

    let compare_branch3 =
      S O

    (** val cost_compare :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_RetEdge) ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_RetEdge) -> nat **)

    let cost_compare x y =
      add (Coq_timed_op_ea.cost_compare (fst x) (fst y))
        (match Parser.Coq_opea_as_OT.compare (fst x) (fst y) with
         | Eq ->
           add compare_branch1 (Coq_timed_eb.cost_compare (snd x) (snd y))
         | Lt -> compare_branch2
         | Gt -> compare_branch3)

    (** val compare' :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_RetEdge) ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_RetEdge) -> comparison c **)

    let compare' x y =
      bind (Coq_timed_op_ea.compare' (fst x) (fst y)) (fun out1 _ ->
        bind
          (match out1 with
           | Eq ->
             bind (Coq_timed_eb.compare' (snd x) (snd y)) (fun out _ ->
               inc compare_branch1 (ret out))
           | Lt -> inc compare_branch2 (ret Lt)
           | Gt -> inc compare_branch3 (ret Gt)) (fun out _ -> ret out))
   end

  module Coq_timed_vb_set =
   struct
    (** val raw_equal :
        (Parser.coq_CalEdge option * Parser.coq_RetEdge) list ->
        (Parser.coq_CalEdge option * Parser.coq_RetEdge) list -> bool **)

    let rec raw_equal s s' =
      match s with
      | [] -> (match s' with
               | [] -> true
               | _ :: _ -> false)
      | x :: l ->
        (match s' with
         | [] -> false
         | x' :: l' ->
           (match Coq_timed_rb.compare x x' with
            | Eq -> raw_equal l l'
            | _ -> false))

    (** val cost_branch1 : nat **)

    let cost_branch1 =
      S O

    (** val cost_branch2 : nat **)

    let cost_branch2 =
      S O

    (** val cost_branch3 : nat **)

    let cost_branch3 =
      S O

    (** val cost_branch4 : nat **)

    let cost_branch4 =
      S O

    (** val cost_raw_equal :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_RetEdge) list ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_RetEdge) list -> nat **)

    let rec cost_raw_equal s s' =
      match s with
      | [] -> (match s' with
               | [] -> cost_branch1
               | _ :: _ -> cost_branch4)
      | x :: l ->
        (match s' with
         | [] -> cost_branch4
         | x' :: l' ->
           add (Coq_timed_rb.cost_compare x x')
             (match Coq_timed_rb.compare x x' with
              | Eq -> add cost_branch2 (cost_raw_equal l l')
              | _ -> cost_branch3))

    (** val raw_equal' :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_RetEdge) list ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_RetEdge) list -> bool c **)

    let rec raw_equal' s s' =
      match s with
      | [] ->
        (match s' with
         | [] -> inc cost_branch1 (ret true)
         | _ :: _ -> inc cost_branch4 (ret false))
      | x :: l ->
        (match s' with
         | [] -> inc cost_branch4 (ret false)
         | x' :: l' ->
           bind (Coq_timed_rb.compare' x x') (fun out1 _ ->
             bind
               (match out1 with
                | Eq ->
                  bind (raw_equal' l l') (fun out _ ->
                    inc cost_branch2 (ret out))
                | _ -> inc cost_branch3 (ret false)) (fun out _ -> ret out)))

    (** val equal : Parser.Coq_vb_set.t_ -> Parser.Coq_vb_set.t_ -> bool **)

    let equal s s' =
      raw_equal (Parser.Coq_vb_set.this s) (Parser.Coq_vb_set.this s')

    (** val cost_equal :
        Parser.Coq_vb_set.t_ -> Parser.Coq_vb_set.t_ -> nat **)

    let cost_equal s s' =
      cost_raw_equal (Parser.Coq_vb_set.this s) (Parser.Coq_vb_set.this s')

    (** val equal' :
        Parser.Coq_vb_set.t_ -> Parser.Coq_vb_set.t_ -> bool c **)

    let equal' s s' =
      raw_equal' (Parser.Coq_vb_set.this s) (Parser.Coq_vb_set.this s')
   end

  module Coq_timed_rc =
   struct
    (** val va_compare :
        Parser.Coq_va_set.t -> Parser.Coq_va_set.t -> comparison **)

    let va_compare =
      Parser.Coq_va_set.compare

    (** val compare :
        (Parser.coq_CalEdge option * Parser.coq_PlnEdge) ->
        (Parser.coq_CalEdge option * Parser.coq_PlnEdge) -> comparison **)

    let compare x y =
      match Parser.Coq_opea_as_OT.compare (fst x) (fst y) with
      | Eq -> Parser.Coq_ec_as_OT.compare (snd x) (snd y)
      | x0 -> x0

    (** val compare_branch1 : nat **)

    let compare_branch1 =
      S O

    (** val compare_branch2 : nat **)

    let compare_branch2 =
      S O

    (** val compare_branch3 : nat **)

    let compare_branch3 =
      S O

    (** val cost_compare :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_PlnEdge) ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_PlnEdge) -> nat **)

    let cost_compare x y =
      add (Coq_timed_op_ea.cost_compare (fst x) (fst y))
        (match Parser.Coq_opea_as_OT.compare (fst x) (fst y) with
         | Eq ->
           add compare_branch1 (Coq_timed_ec.cost_compare (snd x) (snd y))
         | Lt -> compare_branch2
         | Gt -> compare_branch3)

    (** val compare' :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_PlnEdge) ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_PlnEdge) -> comparison c **)

    let compare' x y =
      bind (Coq_timed_op_ea.compare' (fst x) (fst y)) (fun out1 _ ->
        bind
          (match out1 with
           | Eq ->
             bind (Coq_timed_ec.compare' (snd x) (snd y)) (fun out _ ->
               inc compare_branch1 (ret out))
           | Lt -> inc compare_branch2 (ret Lt)
           | Gt -> inc compare_branch3 (ret Gt)) (fun out _ -> ret out))
   end

  module Coq_timed_vc_set =
   struct
    (** val raw_equal :
        (Parser.coq_CalEdge option * Parser.coq_PlnEdge) list ->
        (Parser.coq_CalEdge option * Parser.coq_PlnEdge) list -> bool **)

    let rec raw_equal s s' =
      match s with
      | [] -> (match s' with
               | [] -> true
               | _ :: _ -> false)
      | x :: l ->
        (match s' with
         | [] -> false
         | x' :: l' ->
           (match Coq_timed_rc.compare x x' with
            | Eq -> raw_equal l l'
            | _ -> false))

    (** val cost_branch1 : nat **)

    let cost_branch1 =
      S O

    (** val cost_branch2 : nat **)

    let cost_branch2 =
      S O

    (** val cost_branch3 : nat **)

    let cost_branch3 =
      S O

    (** val cost_branch4 : nat **)

    let cost_branch4 =
      S O

    (** val cost_raw_equal :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_PlnEdge) list ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_PlnEdge) list -> nat **)

    let rec cost_raw_equal s s' =
      match s with
      | [] -> (match s' with
               | [] -> cost_branch1
               | _ :: _ -> cost_branch4)
      | x :: l ->
        (match s' with
         | [] -> cost_branch4
         | x' :: l' ->
           add (Coq_timed_rc.cost_compare x x')
             (match Coq_timed_rc.compare x x' with
              | Eq -> add cost_branch2 (cost_raw_equal l l')
              | _ -> cost_branch3))

    (** val raw_equal' :
        (Parser.Coq_ea_as_OT.t option * Parser.coq_PlnEdge) list ->
        (Parser.Coq_ea_as_OT.t option * Parser.coq_PlnEdge) list -> bool c **)

    let rec raw_equal' s s' =
      match s with
      | [] ->
        (match s' with
         | [] -> inc cost_branch1 (ret true)
         | _ :: _ -> inc cost_branch4 (ret false))
      | x :: l ->
        (match s' with
         | [] -> inc cost_branch4 (ret false)
         | x' :: l' ->
           bind (Coq_timed_rc.compare' x x') (fun out1 _ ->
             bind
               (match out1 with
                | Eq ->
                  bind (raw_equal' l l') (fun out _ ->
                    inc cost_branch2 (ret out))
                | _ -> inc cost_branch3 (ret false)) (fun out _ -> ret out)))

    (** val equal : Parser.Coq_vc_set.t_ -> Parser.Coq_vc_set.t_ -> bool **)

    let equal s s' =
      raw_equal (Parser.Coq_vc_set.this s) (Parser.Coq_vc_set.this s')

    (** val cost_equal :
        Parser.Coq_vc_set.t_ -> Parser.Coq_vc_set.t_ -> nat **)

    let cost_equal s s' =
      cost_raw_equal (Parser.Coq_vc_set.this s) (Parser.Coq_vc_set.this s')

    (** val equal' :
        Parser.Coq_vc_set.t_ -> Parser.Coq_vc_set.t_ -> bool c **)

    let equal' s s' =
      raw_equal' (Parser.Coq_vc_set.this s) (Parser.Coq_vc_set.this s')
   end

  module Coq_va_of_list =
   struct
    (** val va_set_raw_add :
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) ->
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) list ->
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) list **)

    let rec va_set_raw_add x s = match s with
    | [] -> x :: []
    | y :: l ->
      (match Parser.Coq_ra_as_OT.compare x y with
       | Eq -> s
       | Lt -> x :: s
       | Gt -> y :: (va_set_raw_add x l))

    (** val cost_va_set_raw_add_branch1 : nat **)

    let cost_va_set_raw_add_branch1 =
      S O

    (** val cost_va_set_raw_add_branch2 : nat **)

    let cost_va_set_raw_add_branch2 =
      S O

    (** val cost_va_set_raw_add_branch3 : nat **)

    let cost_va_set_raw_add_branch3 =
      S O

    (** val cost_va_set_raw_add_branch4 : nat **)

    let cost_va_set_raw_add_branch4 =
      S O

    (** val cost_va_set_raw_add_branch5 : nat **)

    let cost_va_set_raw_add_branch5 =
      S O

    (** val cost_va_set_raw_add :
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) ->
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) list -> nat **)

    let rec cost_va_set_raw_add x = function
    | [] -> add cons_ct cost_va_set_raw_add_branch1
    | y :: l ->
      (match Parser.Coq_ra_as_OT.compare x y with
       | Eq -> cost_va_set_raw_add_branch2
       | Lt -> add cons_ct cost_va_set_raw_add_branch3
       | Gt ->
         add (add cons_ct cost_va_set_raw_add_branch4)
           (cost_va_set_raw_add x l))

    (** val va_set_raw_add' :
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) ->
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) list ->
        (Parser.coq_CalEdge option * Parser.coq_CalEdge) list c **)

    let rec va_set_raw_add' x s = match s with
    | [] ->
      bind (cons' x []) (fun out _ ->
        inc cost_va_set_raw_add_branch1 (ret out))
    | y :: l ->
      let filtered_var = Parser.Coq_ra_as_OT.compare x y in
      (match filtered_var with
       | Eq -> inc cost_va_set_raw_add_branch2 (ret s)
       | Lt ->
         bind (cons' x s) (fun out _ ->
           inc cost_va_set_raw_add_branch3 (ret out))
       | Gt ->
         bind (va_set_raw_add' x l) (fun out1 _ ->
           bind (cons' y out1) (fun out2 _ ->
             inc cost_va_set_raw_add_branch4 (ret out2))))

    (** val va_set_add :
        Parser.Coq_va_set.t -> Parser.Coq_va_set.elt -> Parser.Coq_va_set.t_ **)

    let va_set_add s x =
      va_set_raw_add x s

    (** val cost_va_set_add_branch1 : nat **)

    let cost_va_set_add_branch1 =
      S O

    (** val cost_va_set_add :
        Parser.Coq_va_set.t -> Parser.Coq_va_set.elt -> nat **)

    let cost_va_set_add s x =
      add cost_va_set_add_branch1 (cost_va_set_raw_add x s)

    (** val va_set_add' :
        Parser.Coq_va_set.t -> Parser.Coq_va_set.elt -> Parser.Coq_va_set.t c **)

    let va_set_add' s x =
      bind (va_set_raw_add' x s) (fun out _ ->
        inc cost_va_set_add_branch1 (ret out))

    (** val cost_va_of_list : Parser.Coq_va_set.elt list -> nat **)

    let cost_va_of_list va =
      cost_fold va_set_add cost_va_set_add va Parser.Coq_va_set.empty

    (** val va_of_list' :
        Parser.Coq_va_set.elt list -> Parser.Coq_va_set.t c **)

    let va_of_list' va =
      bind
        (fold' va_set_add cost_va_set_add va_set_add' va
          Parser.Coq_va_set.empty) (fun out _ -> ret out)
   end

  (** val vb_compare :
      Parser.Coq_vb_set.t -> Parser.Coq_vb_set.t -> comparison **)

  let vb_compare =
    Parser.Coq_vb_set.compare

  (** val cost_eb_as_OT__compare_branch1 : nat **)

  let cost_eb_as_OT__compare_branch1 =
    S O

  (** val cost_eb_as_OT__compare_branch2 : nat **)

  let cost_eb_as_OT__compare_branch2 =
    S O

  (** val cost_eb_as_OT__compare_branch3 : nat **)

  let cost_eb_as_OT__compare_branch3 =
    S O

  (** val cost_eb_as_OT__compare_branch4 : nat **)

  let cost_eb_as_OT__compare_branch4 =
    S O

  (** val cost_eb_as_OT__compare_branch5 : nat **)

  let cost_eb_as_OT__compare_branch5 =
    S O

  (** val cost_eb_as_OT__compare_branch6 : nat **)

  let cost_eb_as_OT__compare_branch6 =
    S O

  (** val cost_eb_as_OT__compare_branch7 : nat **)

  let cost_eb_as_OT__compare_branch7 =
    S O

  (** val cost_eb_as_OT__compare_branch8 : nat **)

  let cost_eb_as_OT__compare_branch8 =
    S O

  (** val cost_eb_as_OT__compare_branch9 : nat **)

  let cost_eb_as_OT__compare_branch9 =
    S O

  (** val cost_eb_as_OT__compare_branch10 : nat **)

  let cost_eb_as_OT__compare_branch10 =
    S O

  (** val cost_eb_as_OT__compare :
      Parser.coq_RetEdge -> Parser.coq_RetEdge -> nat **)

  let cost_eb_as_OT__compare x y =
    match x with
    | Parser.PndRetE (l1, a, l2) ->
      (match y with
       | Parser.PndRetE (l1', a', l2') ->
         add (add cost_eq_str cost_negb)
           (if negb (eq_str a a')
            then add cost_compare_str cost_eb_as_OT__compare_branch2
            else add (add (Coq_vpg.cost_eqvv l1 l1') cost_negb)
                   (if negb (Coq_vpg.eqvv l1 l1')
                    then add (Coq_vpg.cost_compare_vv l1 l1')
                           cost_eb_as_OT__compare_branch3
                    else add (Coq_vpg.cost_compare_vv l2 l2')
                           cost_eb_as_OT__compare_branch4))
       | Parser.MatRetE (_, _, _, _, _) -> cost_eb_as_OT__compare_branch1)
    | Parser.MatRetE (l1, a, l2, b, l3) ->
      (match y with
       | Parser.PndRetE (_, _, _) -> cost_eb_as_OT__compare_branch10
       | Parser.MatRetE (l1', a', l2', b', l3') ->
         add (add cost_eq_str cost_negb)
           (if negb (eq_str a a')
            then add cost_compare_str cost_eb_as_OT__compare_branch5
            else add (add cost_eq_str cost_negb)
                   (if negb (eq_str b b')
                    then add cost_compare_str cost_eb_as_OT__compare_branch6
                    else add (add (Coq_vpg.cost_eqvv l1 l1') cost_negb)
                           (if negb (Coq_vpg.eqvv l1 l1')
                            then add (Coq_vpg.cost_compare_vv l1 l1')
                                   cost_eb_as_OT__compare_branch7
                            else add
                                   (add (Coq_vpg.cost_eqvv l2 l2') cost_negb)
                                   (if negb (Coq_vpg.eqvv l2 l2')
                                    then add (Coq_vpg.cost_compare_vv l2 l2')
                                           cost_eb_as_OT__compare_branch8
                                    else add (Coq_vpg.cost_compare_vv l3 l3')
                                           cost_eb_as_OT__compare_branch9)))))

  (** val eb_as_OT__compare' :
      Parser.coq_RetEdge -> Parser.coq_RetEdge -> comparison c **)

  let eb_as_OT__compare' a b =
    match a with
    | Parser.PndRetE (l1, a0, l2) ->
      (match b with
       | Parser.PndRetE (l1', a', l2') ->
         if sumbool_of_bool (negb (eq_str a0 a'))
         then inc
                (add (add (add cost_negb cost_eq_str) cost_compare_str)
                  cost_eb_as_OT__compare_branch2) (ret (compare_str a0 a'))
         else bind (Coq_vpg.eqvv' l1 l1') (fun res _ ->
                if sumbool_of_bool (negb res)
                then bind (Coq_vpg.compare_vv' l1 l1') (fun out _ ->
                       inc
                         (add (add (add cost_negb cost_eq_str) cost_negb)
                           cost_eb_as_OT__compare_branch3) (ret out))
                else bind (Coq_vpg.compare_vv' l2 l2') (fun out _ ->
                       inc
                         (add (add (add cost_negb cost_eq_str) cost_negb)
                           cost_eb_as_OT__compare_branch4) (ret out)))
       | Parser.MatRetE (_, _, _, _, _) ->
         inc cost_eb_as_OT__compare_branch1 (ret Lt))
    | Parser.MatRetE (l1, a0, l2, b0, l3) ->
      (match b with
       | Parser.PndRetE (_, _, _) ->
         inc cost_eb_as_OT__compare_branch10 (ret Gt)
       | Parser.MatRetE (l1', a', l2', b', l3') ->
         if sumbool_of_bool (negb (eq_str a0 a'))
         then inc
                (add (add (add cost_negb cost_eq_str) cost_compare_str)
                  cost_eb_as_OT__compare_branch5) (ret (compare_str a0 a'))
         else if sumbool_of_bool (negb (eq_str b0 b'))
              then inc
                     (add
                       (add
                         (add (add (add cost_negb cost_eq_str) cost_negb)
                           cost_eq_str) cost_compare_str)
                       cost_eb_as_OT__compare_branch6)
                     (ret (compare_str b0 b'))
              else if sumbool_of_bool (negb (Coq_vpg.eqvv l1 l1'))
                   then bind (Coq_vpg.compare_vv' l1 l1') (fun out _ ->
                          inc
                            (add
                              (add
                                (add
                                  (add
                                    (add (add cost_negb cost_eq_str)
                                      cost_negb) cost_eq_str) cost_negb)
                                (Coq_vpg.cost_eqvv l1 l1'))
                              cost_eb_as_OT__compare_branch7) (ret out))
                   else if sumbool_of_bool (negb (Coq_vpg.eqvv l2 l2'))
                        then bind (Coq_vpg.compare_vv' l2 l2') (fun out _ ->
                               inc
                                 (add
                                   (add
                                     (add
                                       (add
                                         (add
                                           (add
                                             (add (add cost_negb cost_eq_str)
                                               cost_negb) cost_eq_str)
                                           cost_negb)
                                         (Coq_vpg.cost_eqvv l1 l1'))
                                       cost_negb) (Coq_vpg.cost_eqvv l2 l2'))
                                   cost_eb_as_OT__compare_branch8) (ret out))
                        else bind (Coq_vpg.compare_vv' l3 l3') (fun out _ ->
                               inc
                                 (add
                                   (add
                                     (add
                                       (add
                                         (add
                                           (add
                                             (add (add cost_negb cost_eq_str)
                                               cost_negb) cost_eq_str)
                                           cost_negb)
                                         (Coq_vpg.cost_eqvv l1 l1'))
                                       cost_negb) (Coq_vpg.cost_eqvv l2 l2'))
                                   cost_eb_as_OT__compare_branch9) (ret out)))

  (** val rb_as_OT_compare :
      (Parser.coq_CalEdge option * Parser.coq_RetEdge) -> (Parser.coq_CalEdge
      option * Parser.coq_RetEdge) -> comparison **)

  let rb_as_OT_compare x y =
    match Parser.Coq_opea_as_OT.compare (fst x) (fst y) with
    | Eq -> Parser.Coq_eb_as_OT.compare (snd x) (snd y)
    | x0 -> x0

  (** val vb_set_raw_add :
      (Parser.coq_CalEdge option * Parser.coq_RetEdge) -> (Parser.coq_CalEdge
      option * Parser.coq_RetEdge) list -> (Parser.coq_CalEdge
      option * Parser.coq_RetEdge) list **)

  let rec vb_set_raw_add x s = match s with
  | [] -> x :: []
  | y :: l ->
    (match Parser.Coq_rb_as_OT.compare x y with
     | Eq -> s
     | Lt -> x :: s
     | Gt -> y :: (vb_set_raw_add x l))

  (** val cost_vb_set_raw_add_branch1 : nat **)

  let cost_vb_set_raw_add_branch1 =
    S O

  (** val cost_vb_set_raw_add_branch2 : nat **)

  let cost_vb_set_raw_add_branch2 =
    S O

  (** val cost_vb_set_raw_add_branch3 : nat **)

  let cost_vb_set_raw_add_branch3 =
    S O

  (** val cost_vb_set_raw_add_branch4 : nat **)

  let cost_vb_set_raw_add_branch4 =
    S O

  (** val cost_vb_set_raw_add_branch5 : nat **)

  let cost_vb_set_raw_add_branch5 =
    S O

  (** val cost_vb_set_raw_add :
      (Parser.coq_CalEdge option * Parser.coq_RetEdge) -> (Parser.coq_CalEdge
      option * Parser.coq_RetEdge) list -> nat **)

  let rec cost_vb_set_raw_add x = function
  | [] -> add cons_ct cost_vb_set_raw_add_branch1
  | y :: l ->
    (match Parser.Coq_rb_as_OT.compare x y with
     | Eq -> cost_vb_set_raw_add_branch2
     | Lt -> add cons_ct cost_vb_set_raw_add_branch3
     | Gt ->
       add (add cons_ct cost_vb_set_raw_add_branch4) (cost_vb_set_raw_add x l))

  (** val vb_set_raw_add' :
      (Parser.coq_CalEdge option * Parser.coq_RetEdge) -> (Parser.coq_CalEdge
      option * Parser.coq_RetEdge) list -> (Parser.coq_CalEdge
      option * Parser.coq_RetEdge) list c **)

  let rec vb_set_raw_add' x s = match s with
  | [] ->
    bind (cons' x []) (fun out _ -> inc cost_vb_set_raw_add_branch1 (ret out))
  | y :: l ->
    let filtered_var = Parser.Coq_rb_as_OT.compare x y in
    (match filtered_var with
     | Eq -> inc cost_vb_set_raw_add_branch2 (ret s)
     | Lt ->
       bind (cons' x s) (fun out _ ->
         inc cost_vb_set_raw_add_branch3 (ret out))
     | Gt ->
       bind (vb_set_raw_add' x l) (fun out1 _ ->
         bind (cons' y out1) (fun out2 _ ->
           inc cost_vb_set_raw_add_branch4 (ret out2))))

  (** val vb_set_add :
      Parser.Coq_vb_set.t -> Parser.Coq_vb_set.elt -> Parser.Coq_vb_set.t_ **)

  let vb_set_add s x =
    vb_set_raw_add x s

  (** val cost_vb_set_add_branch1 : nat **)

  let cost_vb_set_add_branch1 =
    S O

  (** val cost_vb_set_add :
      Parser.Coq_vb_set.t -> Parser.Coq_vb_set.elt -> nat **)

  let cost_vb_set_add s x =
    add cost_vb_set_add_branch1 (cost_vb_set_raw_add x s)

  (** val vb_set_add' :
      Parser.Coq_vb_set.t -> Parser.Coq_vb_set.elt -> Parser.Coq_vb_set.t c **)

  let vb_set_add' s x =
    bind (vb_set_raw_add' x s) (fun out _ ->
      inc cost_vb_set_add_branch1 (ret out))

  (** val cost_vb_of_list : Parser.Coq_vb_set.elt list -> nat **)

  let cost_vb_of_list vb =
    cost_fold vb_set_add cost_vb_set_add vb Parser.Coq_vb_set.empty

  (** val vb_of_list' :
      Parser.Coq_vb_set.elt list -> Parser.Coq_vb_set.t c **)

  let vb_of_list' vb =
    bind
      (fold' vb_set_add cost_vb_set_add vb_set_add' vb
        Parser.Coq_vb_set.empty) (fun out _ -> ret out)

  (** val vc_compare :
      Parser.Coq_vc_set.t -> Parser.Coq_vc_set.t -> comparison **)

  let vc_compare =
    Parser.Coq_vc_set.compare

  (** val cost_ec_as_OT__compare_branch1 : nat **)

  let cost_ec_as_OT__compare_branch1 =
    S O

  (** val cost_ec_as_OT__compare_branch2 : nat **)

  let cost_ec_as_OT__compare_branch2 =
    S O

  (** val cost_ec_as_OT__compare_branch3 : nat **)

  let cost_ec_as_OT__compare_branch3 =
    S O

  (** val cost_ec_as_OT__compare :
      Parser.coq_PlnEdge -> Parser.coq_PlnEdge -> nat **)

  let cost_ec_as_OT__compare x y =
    let Parser.PlnE (l1, a, l2) = x in
    let Parser.PlnE (l1', a', l2') = y in
    if negb (eq_str a a')
    then add (add cost_negb cost_eq_str) cost_ec_as_OT__compare_branch1
    else if negb (Coq_vpg.Coq_vvot.eqb l1 l1')
         then add
                (add
                  (add (add (add cost_negb cost_eq_str) cost_negb)
                    (Coq_vpg.cost_eqvv l1 l1'))
                  (Coq_vpg.cost_compare_vv l1 l1'))
                cost_ec_as_OT__compare_branch2
         else add
                (add
                  (add (add (add cost_negb cost_eq_str) cost_negb)
                    (Coq_vpg.cost_eqvv l1 l1'))
                  (Coq_vpg.cost_compare_vv l2 l2'))
                cost_ec_as_OT__compare_branch3

  (** val ec_as_OT__compare' :
      Parser.coq_PlnEdge -> Parser.coq_PlnEdge -> comparison c **)

  let ec_as_OT__compare' a b =
    let Parser.PlnE (l1, a0, l2) = a in
    let Parser.PlnE (l1', a', l2') = b in
    if sumbool_of_bool (negb (eq_str a0 a'))
    then inc (add (add cost_negb cost_eq_str) cost_ec_as_OT__compare_branch1)
           (ret (compare_str a0 a'))
    else bind (Coq_vpg.eqvv' l1 l1') (fun out _ ->
           if sumbool_of_bool (negb out)
           then bind (Coq_vpg.compare_vv' l1 l1') (fun out0 _ ->
                  inc
                    (add (add (add cost_negb cost_eq_str) cost_negb)
                      cost_ec_as_OT__compare_branch2) (ret out0))
           else bind (Coq_vpg.compare_vv' l2 l2') (fun out0 _ ->
                  inc
                    (add (add (add cost_negb cost_eq_str) cost_negb)
                      cost_ec_as_OT__compare_branch3) (ret out0)))

  (** val rc_as_OT_compare :
      (Parser.coq_CalEdge option * Parser.coq_PlnEdge) -> (Parser.coq_CalEdge
      option * Parser.coq_PlnEdge) -> comparison **)

  let rc_as_OT_compare x y =
    match Parser.Coq_opea_as_OT.compare (fst x) (fst y) with
    | Eq -> Parser.Coq_ec_as_OT.compare (snd x) (snd y)
    | x0 -> x0

  (** val vc_set_raw_add :
      (Parser.coq_CalEdge option * Parser.coq_PlnEdge) -> (Parser.coq_CalEdge
      option * Parser.coq_PlnEdge) list -> (Parser.coq_CalEdge
      option * Parser.coq_PlnEdge) list **)

  let rec vc_set_raw_add x s = match s with
  | [] -> x :: []
  | y :: l ->
    (match Parser.Coq_rc_as_OT.compare x y with
     | Eq -> s
     | Lt -> x :: s
     | Gt -> y :: (vc_set_raw_add x l))

  (** val cost_vc_set_raw_add_branch1 : nat **)

  let cost_vc_set_raw_add_branch1 =
    S O

  (** val cost_vc_set_raw_add_branch2 : nat **)

  let cost_vc_set_raw_add_branch2 =
    S O

  (** val cost_vc_set_raw_add_branch3 : nat **)

  let cost_vc_set_raw_add_branch3 =
    S O

  (** val cost_vc_set_raw_add_branch4 : nat **)

  let cost_vc_set_raw_add_branch4 =
    S O

  (** val cost_vc_set_raw_add_branch5 : nat **)

  let cost_vc_set_raw_add_branch5 =
    S O

  (** val cost_vc_set_raw_add :
      (Parser.coq_CalEdge option * Parser.coq_PlnEdge) -> (Parser.coq_CalEdge
      option * Parser.coq_PlnEdge) list -> nat **)

  let rec cost_vc_set_raw_add x = function
  | [] -> add cons_ct cost_vc_set_raw_add_branch1
  | y :: l ->
    (match Parser.Coq_rc_as_OT.compare x y with
     | Eq -> cost_vc_set_raw_add_branch2
     | Lt -> add cons_ct cost_vc_set_raw_add_branch3
     | Gt ->
       add (add cons_ct cost_vc_set_raw_add_branch4) (cost_vc_set_raw_add x l))

  (** val vc_set_raw_add' :
      (Parser.coq_CalEdge option * Parser.coq_PlnEdge) -> (Parser.coq_CalEdge
      option * Parser.coq_PlnEdge) list -> (Parser.coq_CalEdge
      option * Parser.coq_PlnEdge) list c **)

  let rec vc_set_raw_add' x s = match s with
  | [] ->
    bind (cons' x []) (fun out _ -> inc cost_vc_set_raw_add_branch1 (ret out))
  | y :: l ->
    let filtered_var = Parser.Coq_rc_as_OT.compare x y in
    (match filtered_var with
     | Eq -> inc cost_vc_set_raw_add_branch2 (ret s)
     | Lt ->
       bind (cons' x s) (fun out _ ->
         inc cost_vc_set_raw_add_branch3 (ret out))
     | Gt ->
       bind (vc_set_raw_add' x l) (fun out1 _ ->
         bind (cons' y out1) (fun out2 _ ->
           inc cost_vc_set_raw_add_branch4 (ret out2))))

  (** val vc_set_add :
      Parser.Coq_vc_set.t -> Parser.Coq_vc_set.elt -> Parser.Coq_vc_set.t_ **)

  let vc_set_add s x =
    vc_set_raw_add x s

  (** val cost_vc_set_add_branch1 : nat **)

  let cost_vc_set_add_branch1 =
    S O

  (** val cost_vc_set_add :
      Parser.Coq_vc_set.t -> Parser.Coq_vc_set.elt -> nat **)

  let cost_vc_set_add s x =
    add cost_vc_set_add_branch1 (cost_vc_set_raw_add x s)

  (** val vc_set_add' :
      Parser.Coq_vc_set.t -> Parser.Coq_vc_set.elt -> Parser.Coq_vc_set.t c **)

  let vc_set_add' s x =
    bind (vc_set_raw_add' x s) (fun out _ ->
      inc cost_vc_set_add_branch1 (ret out))

  (** val cost_vc_of_list : Parser.Coq_vc_set.elt list -> nat **)

  let cost_vc_of_list vc =
    cost_fold vc_set_add cost_vc_set_add vc Parser.Coq_vc_set.empty

  (** val vc_of_list' :
      Parser.Coq_vc_set.elt list -> Parser.Coq_vc_set.t c **)

  let vc_of_list' vc =
    bind
      (fold' vc_set_add cost_vc_set_add vc_set_add' vc
        Parser.Coq_vc_set.empty) (fun out _ -> ret out)
 end

module Transducer =
 functor (G:VPG) ->
 struct
  module TimedSets = TimedSets(G)

  module PreTransducer =
   struct
    (** val getSymVE : TimedSets.Parser.coq_VE -> Coq_vpg.symbol **)

    let getSymVE = function
    | TimedSets.Parser.Calv va ->
      (match va with
       | TimedSets.Parser.PndCalE (_, i, _) -> Coq_vpg.Call i
       | TimedSets.Parser.MatCalE (_, i, _, _, _) -> Coq_vpg.Call i)
    | TimedSets.Parser.Plnv vc ->
      let TimedSets.Parser.PlnE (_, i, _) = vc in Coq_vpg.Plain i
    | TimedSets.Parser.Retv vb ->
      (match vb with
       | TimedSets.Parser.PndRetE (_, i, _) -> Coq_vpg.Ret i
       | TimedSets.Parser.MatRetE (_, _, _, i, _) -> Coq_vpg.Ret i)
   end

  module Transducer2 =
   struct
    (** val rci_eq_dec :
        (TimedSets.Parser.coq_PlnEdge * nat) ->
        (TimedSets.Parser.coq_PlnEdge * nat) -> bool **)

    let rci_eq_dec x y =
      let (a, b) = x in
      let (a0, b0) = y in
      if TimedSets.Parser.Coq_ec_as_OT.plne_dec a a0
      then Nat.eq_dec b b0
      else false

    (** val rai_eq_dec :
        (TimedSets.Parser.coq_CalEdge * nat) ->
        (TimedSets.Parser.coq_CalEdge * nat) -> bool **)

    let rai_eq_dec x y =
      let (a, b) = x in
      let (a0, b0) = y in
      if TimedSets.Parser.Coq_ea_as_OT.cale_dec a a0
      then Nat.eq_dec b b0
      else false

    (** val rbi_eq_dec :
        (TimedSets.Parser.coq_RetEdge * nat) ->
        (TimedSets.Parser.coq_RetEdge * nat) -> bool **)

    let rbi_eq_dec x y =
      let (a, b) = x in
      let (a0, b0) = y in
      if TimedSets.Parser.Coq_eb_as_OT.rete_dec a a0
      then Nat.eq_dec b b0
      else false

    (** val rc_eq_dec :
        (TimedSets.Parser.coq_CalEdge option * TimedSets.Parser.coq_PlnEdge)
        -> (TimedSets.Parser.coq_CalEdge
        option * TimedSets.Parser.coq_PlnEdge) -> bool **)

    let rc_eq_dec x y =
      let (a, b) = x in
      let (a0, b0) = y in
      if TimedSets.Parser.Coq_opea_as_OT.cale_dec a a0
      then TimedSets.Parser.Coq_ec_as_OT.plne_dec b b0
      else false

    (** val ra_eq_dec :
        (TimedSets.Parser.coq_CalEdge option * TimedSets.Parser.coq_CalEdge)
        -> (TimedSets.Parser.coq_CalEdge
        option * TimedSets.Parser.coq_CalEdge) -> bool **)

    let ra_eq_dec x y =
      let (a, b) = x in
      let (a0, b0) = y in
      if TimedSets.Parser.Coq_opea_as_OT.cale_dec a a0
      then TimedSets.Parser.Coq_ea_as_OT.cale_dec b b0
      else false

    (** val la_eq_dec :
        TimedSets.Parser.coq_CalEdge list -> TimedSets.Parser.coq_CalEdge
        list -> bool **)

    let rec la_eq_dec l x0 =
      match l with
      | [] -> (match x0 with
               | [] -> true
               | _ :: _ -> false)
      | y :: l0 ->
        (match x0 with
         | [] -> false
         | a :: l1 ->
           if TimedSets.Parser.Coq_ea_as_OT.cale_dec y a
           then la_eq_dec l0 l1
           else false)

    (** val lb_eq_dec :
        TimedSets.Parser.coq_RetEdge list -> TimedSets.Parser.coq_RetEdge
        list -> bool **)

    let rec lb_eq_dec l x0 =
      match l with
      | [] -> (match x0 with
               | [] -> true
               | _ :: _ -> false)
      | y :: l0 ->
        (match x0 with
         | [] -> false
         | a :: l1 ->
           if TimedSets.Parser.Coq_eb_as_OT.rete_dec y a
           then lb_eq_dec l0 l1
           else false)

    (** val lc_eq_dec :
        TimedSets.Parser.coq_PlnEdge list -> TimedSets.Parser.coq_PlnEdge
        list -> bool **)

    let rec lc_eq_dec l x0 =
      match l with
      | [] -> (match x0 with
               | [] -> true
               | _ :: _ -> false)
      | y :: l0 ->
        (match x0 with
         | [] -> false
         | a :: l1 ->
           if TimedSets.Parser.Coq_ec_as_OT.plne_dec y a
           then lc_eq_dec l0 l1
           else false)

    (** val ve_eq_dec :
        TimedSets.Parser.coq_VE -> TimedSets.Parser.coq_VE -> bool **)

    let ve_eq_dec x y =
      TimedSets.Parser.coq_VE_rec (fun va x0 ->
        match x0 with
        | TimedSets.Parser.Calv va0 ->
          TimedSets.Parser.Coq_ea_as_OT.cale_dec va va0
        | _ -> false) (fun vc x0 ->
        match x0 with
        | TimedSets.Parser.Plnv vc0 ->
          TimedSets.Parser.Coq_ec_as_OT.plne_dec vc vc0
        | _ -> false) (fun vb x0 ->
        match x0 with
        | TimedSets.Parser.Retv vb0 ->
          TimedSets.Parser.Coq_eb_as_OT.rete_dec vb vb0
        | _ -> false) x y

    (** val lve_eq_dec :
        TimedSets.Parser.coq_VE list -> TimedSets.Parser.coq_VE list -> bool **)

    let rec lve_eq_dec l x0 =
      match l with
      | [] -> (match x0 with
               | [] -> true
               | _ :: _ -> false)
      | y :: l0 ->
        (match x0 with
         | [] -> false
         | a :: l1 ->
           if TimedSets.Parser.Coq_ve_as_OT.ve_dec y a
           then lve_eq_dec l0 l1
           else false)

    (** val inlist : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 list -> bool **)

    let rec inlist compareA x = function
    | [] -> false
    | y :: l' ->
      (match compareA x y with
       | Eq -> true
       | _ -> inlist compareA x l')

    (** val ec_inlist :
        TimedSets.Parser.coq_PlnEdge -> TimedSets.Parser.coq_PlnEdge list ->
        bool **)

    let ec_inlist =
      inlist TimedSets.Parser.Coq_ec_as_OT.compare

    (** val ea_inlist :
        TimedSets.Parser.coq_CalEdge -> TimedSets.Parser.coq_CalEdge list ->
        bool **)

    let ea_inlist =
      inlist TimedSets.Parser.Coq_ea_as_OT.compare

    (** val eb_inlist :
        TimedSets.Parser.coq_RetEdge -> TimedSets.Parser.coq_RetEdge list ->
        bool **)

    let eb_inlist =
      inlist TimedSets.Parser.Coq_eb_as_OT.compare

    (** val f_b :
        TimedSets.Parser.coq_ME -> (TimedSets.Parser.coq_VE
        list * TimedSets.Parser.coq_RetEdge list) list ->
        (TimedSets.Parser.coq_VE list * TimedSets.Parser.coq_RetEdge list)
        list **)

    let f_b m v =
      match m with
      | TimedSets.Parser.CalCME m1 ->
        let m2 = TimedSets.Parser.Coq_va_set.elements m1 in
        let sth =
          map (fun vt ->
            let (v0, t0) = vt in
            let f0 = fun rr ->
              let (r, e) = rr in
              (match r with
               | Some c0 ->
                 (match c0 with
                  | TimedSets.Parser.PndCalE (_, _, _) ->
                    (match t0 with
                     | [] ->
                       (match v0 with
                        | [] -> false
                        | ve :: _ ->
                          Coq_vpg.eqvv
                            (TimedSets.Parser.endE (TimedSets.Parser.Calv e))
                            (TimedSets.Parser.beginE ve))
                     | r0 :: _ ->
                       (match r0 with
                        | TimedSets.Parser.PndRetE (_, _, _) ->
                          (match v0 with
                           | [] -> false
                           | ve :: _ ->
                             Coq_vpg.eqvv
                               (TimedSets.Parser.endE (TimedSets.Parser.Calv
                                 e)) (TimedSets.Parser.beginE ve))
                        | TimedSets.Parser.MatRetE (_, _, _, _, _) -> false))
                  | TimedSets.Parser.MatCalE (l, a, l1, b, l2) ->
                    (match t0 with
                     | [] -> false
                     | r0 :: _ ->
                       (match r0 with
                        | TimedSets.Parser.PndRetE (_, _, _) -> false
                        | TimedSets.Parser.MatRetE (l', a', l1', b', l2') ->
                          (&&)
                            ((&&)
                              ((&&)
                                ((&&)
                                  ((&&) (Coq_vpg.eqvv l l')
                                    (Coq_vpg.eqvv l1 l1'))
                                  (Coq_vpg.eqvv l2 l2')) (eq_str a a'))
                              (eq_str b b'))
                            (match v0 with
                             | [] -> false
                             | ve :: _ ->
                               (match ve with
                                | TimedSets.Parser.Retv _ ->
                                  TimedSets.Parser.goEps
                                    (TimedSets.Parser.Calv e)
                                | _ ->
                                  Coq_vpg.eqvv
                                    (TimedSets.Parser.endE
                                      (TimedSets.Parser.Calv e))
                                    (TimedSets.Parser.beginE ve))))))
               | None ->
                 (match t0 with
                  | [] ->
                    (match v0 with
                     | [] -> false
                     | ve :: _ ->
                       Coq_vpg.eqvv
                         (TimedSets.Parser.endE (TimedSets.Parser.Calv e))
                         (TimedSets.Parser.beginE ve))
                  | r0 :: _ ->
                    (match r0 with
                     | TimedSets.Parser.PndRetE (_, _, _) ->
                       (match v0 with
                        | [] -> false
                        | ve :: _ ->
                          Coq_vpg.eqvv
                            (TimedSets.Parser.endE (TimedSets.Parser.Calv e))
                            (TimedSets.Parser.beginE ve))
                     | TimedSets.Parser.MatRetE (_, _, _, _, _) -> false)))
            in
            let ms = nodup ea_inlist (TimedSets.Parser.filter_map m2 f0 snd)
            in
            map (fun e -> (((TimedSets.Parser.Calv e) :: v0), (tl t0))) ms) v
        in
        concat sth
      | TimedSets.Parser.PlnCME m1 ->
        let m2 = TimedSets.Parser.Coq_vc_set.elements m1 in
        let sth =
          map (fun vt ->
            let (v0, t0) = vt in
            let f0 = fun rr ->
              let (r, e) = rr in
              (match r with
               | Some c0 ->
                 (match c0 with
                  | TimedSets.Parser.PndCalE (_, _, _) ->
                    (match t0 with
                     | [] ->
                       (match v0 with
                        | [] -> false
                        | ve :: _ ->
                          Coq_vpg.eqvv
                            (TimedSets.Parser.endE (TimedSets.Parser.Plnv e))
                            (TimedSets.Parser.beginE ve))
                     | r0 :: _ ->
                       (match r0 with
                        | TimedSets.Parser.PndRetE (_, _, _) ->
                          (match v0 with
                           | [] -> false
                           | ve :: _ ->
                             Coq_vpg.eqvv
                               (TimedSets.Parser.endE (TimedSets.Parser.Plnv
                                 e)) (TimedSets.Parser.beginE ve))
                        | TimedSets.Parser.MatRetE (_, _, _, _, _) -> false))
                  | TimedSets.Parser.MatCalE (l, a, l1, b, l2) ->
                    (match t0 with
                     | [] -> false
                     | r0 :: _ ->
                       (match r0 with
                        | TimedSets.Parser.PndRetE (_, _, _) -> false
                        | TimedSets.Parser.MatRetE (l', a', l1', b', l2') ->
                          (&&)
                            ((&&)
                              ((&&)
                                ((&&)
                                  ((&&) (Coq_vpg.eqvv l l')
                                    (Coq_vpg.eqvv l1 l1'))
                                  (Coq_vpg.eqvv l2 l2')) (eq_str a a'))
                              (eq_str b b'))
                            (match v0 with
                             | [] -> false
                             | ve :: _ ->
                               (match ve with
                                | TimedSets.Parser.Retv _ ->
                                  TimedSets.Parser.goEps
                                    (TimedSets.Parser.Plnv e)
                                | _ ->
                                  Coq_vpg.eqvv
                                    (TimedSets.Parser.endE
                                      (TimedSets.Parser.Plnv e))
                                    (TimedSets.Parser.beginE ve))))))
               | None ->
                 (match t0 with
                  | [] ->
                    (match v0 with
                     | [] -> false
                     | ve :: _ ->
                       Coq_vpg.eqvv
                         (TimedSets.Parser.endE (TimedSets.Parser.Plnv e))
                         (TimedSets.Parser.beginE ve))
                  | r0 :: _ ->
                    (match r0 with
                     | TimedSets.Parser.PndRetE (_, _, _) ->
                       (match v0 with
                        | [] -> false
                        | ve :: _ ->
                          Coq_vpg.eqvv
                            (TimedSets.Parser.endE (TimedSets.Parser.Plnv e))
                            (TimedSets.Parser.beginE ve))
                     | TimedSets.Parser.MatRetE (_, _, _, _, _) -> false)))
            in
            let ms = nodup ec_inlist (TimedSets.Parser.filter_map m2 f0 snd)
            in
            map (fun e -> (((TimedSets.Parser.Plnv e) :: v0), t0)) ms) v
        in
        concat sth
      | TimedSets.Parser.RetCME m1 ->
        let m2 = TimedSets.Parser.Coq_vb_set.elements m1 in
        let sth =
          map (fun vt ->
            let (v0, t0) = vt in
            let f0 = fun rr ->
              let (r, e) = rr in
              (match r with
               | Some c0 ->
                 (match c0 with
                  | TimedSets.Parser.PndCalE (_, _, _) ->
                    (match t0 with
                     | [] ->
                       (match v0 with
                        | [] -> false
                        | ve :: _ ->
                          Coq_vpg.eqvv
                            (TimedSets.Parser.endE (TimedSets.Parser.Retv e))
                            (TimedSets.Parser.beginE ve))
                     | r0 :: _ ->
                       (match r0 with
                        | TimedSets.Parser.PndRetE (_, _, _) ->
                          (match v0 with
                           | [] -> false
                           | ve :: _ ->
                             Coq_vpg.eqvv
                               (TimedSets.Parser.endE (TimedSets.Parser.Retv
                                 e)) (TimedSets.Parser.beginE ve))
                        | TimedSets.Parser.MatRetE (_, _, _, _, _) -> false))
                  | TimedSets.Parser.MatCalE (l, a, l1, b, l2) ->
                    (match t0 with
                     | [] -> false
                     | r0 :: _ ->
                       (match r0 with
                        | TimedSets.Parser.PndRetE (_, _, _) -> false
                        | TimedSets.Parser.MatRetE (l', a', l1', b', l2') ->
                          (&&)
                            ((&&)
                              ((&&)
                                ((&&)
                                  ((&&) (Coq_vpg.eqvv l l')
                                    (Coq_vpg.eqvv l1 l1'))
                                  (Coq_vpg.eqvv l2 l2')) (eq_str a a'))
                              (eq_str b b'))
                            (match v0 with
                             | [] -> false
                             | ve :: _ ->
                               (match ve with
                                | TimedSets.Parser.Retv _ ->
                                  TimedSets.Parser.goEps
                                    (TimedSets.Parser.Retv e)
                                | _ ->
                                  Coq_vpg.eqvv
                                    (TimedSets.Parser.endE
                                      (TimedSets.Parser.Retv e))
                                    (TimedSets.Parser.beginE ve))))))
               | None ->
                 (match t0 with
                  | [] ->
                    (match v0 with
                     | [] -> false
                     | ve :: _ ->
                       Coq_vpg.eqvv
                         (TimedSets.Parser.endE (TimedSets.Parser.Retv e))
                         (TimedSets.Parser.beginE ve))
                  | r0 :: _ ->
                    (match r0 with
                     | TimedSets.Parser.PndRetE (_, _, _) ->
                       (match v0 with
                        | [] -> false
                        | ve :: _ ->
                          Coq_vpg.eqvv
                            (TimedSets.Parser.endE (TimedSets.Parser.Retv e))
                            (TimedSets.Parser.beginE ve))
                     | TimedSets.Parser.MatRetE (_, _, _, _, _) -> false)))
            in
            let ms = nodup eb_inlist (TimedSets.Parser.filter_map m2 f0 snd)
            in
            map (fun e -> (((TimedSets.Parser.Retv e) :: v0), (e :: t0))) ms)
            v
        in
        concat sth

    (** val lvb_eq_dec :
        (TimedSets.Parser.coq_VE list * TimedSets.Parser.coq_RetEdge list) ->
        (TimedSets.Parser.coq_VE list * TimedSets.Parser.coq_RetEdge list) ->
        bool **)

    let lvb_eq_dec x y =
      let (a, b) = x in
      let (a0, b0) = y in if lve_eq_dec a a0 then lb_eq_dec b b0 else false

    (** val lva_eq_dec :
        (TimedSets.Parser.coq_VE list * TimedSets.Parser.coq_CalEdge list) ->
        (TimedSets.Parser.coq_VE list * TimedSets.Parser.coq_CalEdge list) ->
        bool **)

    let lva_eq_dec x y =
      let (a, b) = x in
      let (a0, b0) = y in if lve_eq_dec a a0 then la_eq_dec b b0 else false

    (** val lvc_eq_dec :
        (TimedSets.Parser.coq_VE list * TimedSets.Parser.coq_PlnEdge list) ->
        (TimedSets.Parser.coq_VE list * TimedSets.Parser.coq_PlnEdge list) ->
        bool **)

    let lvc_eq_dec x y =
      let (a, b) = x in
      let (a0, b0) = y in if lve_eq_dec a a0 then lc_eq_dec b b0 else false

    (** val f_init :
        TimedSets.Parser.coq_ME -> (TimedSets.Parser.coq_VE
        list * TimedSets.Parser.coq_RetEdge list) list **)

    let f_init = function
    | TimedSets.Parser.CalCME m1 ->
      let m2 = TimedSets.Parser.Coq_va_set.elements m1 in
      let f0 = fun v ->
        let (r, e) = v in
        (match r with
         | Some c0 ->
           (match c0 with
            | TimedSets.Parser.PndCalE (_, _, _) ->
              TimedSets.Parser.goEps (TimedSets.Parser.Calv e)
            | TimedSets.Parser.MatCalE (_, _, _, _, _) -> false)
         | None -> TimedSets.Parser.goEps (TimedSets.Parser.Calv e))
      in
      let g = fun v -> let (_, e) = v in e in
      map (fun e -> (((TimedSets.Parser.Calv e) :: []), []))
        (nodup ea_inlist (TimedSets.Parser.filter_map m2 f0 g))
    | TimedSets.Parser.PlnCME m1 ->
      let m2 = TimedSets.Parser.Coq_vc_set.elements m1 in
      let f0 = fun v ->
        let (r, e) = v in
        (match r with
         | Some c0 ->
           (match c0 with
            | TimedSets.Parser.PndCalE (_, _, _) ->
              TimedSets.Parser.goEps (TimedSets.Parser.Plnv e)
            | TimedSets.Parser.MatCalE (_, _, _, _, _) -> false)
         | None -> TimedSets.Parser.goEps (TimedSets.Parser.Plnv e))
      in
      let g = fun v -> let (_, e) = v in e in
      let es = TimedSets.Parser.filter_map m2 f0 g in
      map (fun e -> (((TimedSets.Parser.Plnv e) :: []), []))
        (nodup ec_inlist es)
    | TimedSets.Parser.RetCME m1 ->
      let m2 = TimedSets.Parser.Coq_vb_set.elements m1 in
      let f0 = fun v ->
        let (r, e) = v in
        (match r with
         | Some c0 ->
           (match c0 with
            | TimedSets.Parser.PndCalE (_, _, _) ->
              TimedSets.Parser.goEps (TimedSets.Parser.Retv e)
            | TimedSets.Parser.MatCalE (_, _, _, _, _) -> false)
         | None -> TimedSets.Parser.goEps (TimedSets.Parser.Retv e))
      in
      let g = fun v -> let (_, e) = v in e in
      map (fun e -> (((TimedSets.Parser.Retv e) :: []), (e :: [])))
        (nodup eb_inlist (TimedSets.Parser.filter_map m2 f0 g))
   end
 end

module ExtractionWNoDup =
 functor (G:VPG) ->
 struct
  module Transducer = Transducer(G)

  (** val extraction :
      Transducer.TimedSets.Parser.coq_ME list ->
      (Transducer.TimedSets.Parser.coq_VE
      list * Transducer.TimedSets.Parser.coq_RetEdge list) list ->
      (Transducer.TimedSets.Parser.coq_VE
      list * Transducer.TimedSets.Parser.coq_RetEdge list) list **)

  let rec extraction m v =
    match m with
    | [] -> v
    | m1 :: m' ->
      (match m' with
       | [] -> v
       | _ :: _ ->
         let v' = Transducer.Transducer2.f_b m1 v in extraction m' v')
 end

module TimedExtractionPln =
 functor (G:VPG) ->
 struct
  module ExtractionWNoDup = ExtractionWNoDup(G)

  (** val cost_if_stmt : nat **)

  let cost_if_stmt =
    S O

  (** val cost_filter_reti_var : nat **)

  let cost_filter_reti_var =
    S O

  (** val time_filter_reti_base : nat **)

  let time_filter_reti_base =
    S O

  (** val cost_snd : nat **)

  let cost_snd =
    S O

  (** val cost_var_f_pln_branch1_Pln : nat **)

  let cost_var_f_pln_branch1_Pln =
    S O

  (** val cost_var_f_pln_branch2_Pln : nat **)

  let cost_var_f_pln_branch2_Pln =
    S O

  (** val cost_var_f_pln_branch3_Pln : nat **)

  let cost_var_f_pln_branch3_Pln =
    S O

  (** val cost_var_f_pln_branch4_Pln : nat **)

  let cost_var_f_pln_branch4_Pln =
    S O

  (** val cost_var_f_pln_branch5_Pln : nat **)

  let cost_var_f_pln_branch5_Pln =
    S O

  (** val f_Pln :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE list ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) ->
      bool **)

  let f_Pln v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (_, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> false
              | ve :: _ ->
                Coq_vpg.eqvv
                  (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                    (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
                  (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE ve))
           | y :: _ ->
             (match y with
              | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> false
                 | ve :: _ ->
                   Coq_vpg.eqvv
                     (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                       (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
                     (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE ve))
              | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                false))
        | ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (l, a, l1, b,
                                                                l2) ->
          (match t0 with
           | [] -> false
           | r0 :: _ ->
             (match r0 with
              | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                false
              | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', a', l1', b', l2') ->
                (&&)
                  ((&&)
                    ((&&)
                      ((&&) ((&&) (Coq_vpg.eqvv l l') (Coq_vpg.eqvv l1 l1'))
                        (Coq_vpg.eqvv l2 l2')) (eq_str a a')) (eq_str b b'))
                  (match v with
                   | [] -> false
                   | ve :: _ ->
                     (match ve with
                      | ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                        ExtractionWNoDup.Transducer.TimedSets.Parser.goEps
                          (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                          e)
                      | _ ->
                        Coq_vpg.eqvv
                          (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                            (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                            e))
                          (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                            ve))))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> false
           | ve :: _ ->
             Coq_vpg.eqvv
               (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                 (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
               (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE ve))
        | r0 :: _ ->
          (match r0 with
           | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (_, _, _) ->
             (match v with
              | [] -> false
              | ve :: _ ->
                Coq_vpg.eqvv
                  (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                    (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
                  (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE ve))
           | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (_, _, _,
                                                                   _, _) ->
             false)))

  (** val cost_f_pln_branch1 : nat **)

  let cost_f_pln_branch1 =
    S O

  (** val cost_f_pln_branch2 : nat **)

  let cost_f_pln_branch2 =
    S O

  (** val cost_f_pln_branch3 : nat **)

  let cost_f_pln_branch3 =
    S O

  (** val cost_f_pln_branch4 : nat **)

  let cost_f_pln_branch4 =
    S O

  (** val cost_f_pln_branch5 : nat **)

  let cost_f_pln_branch5 =
    S O

  (** val cost_f_pln_branch6 : nat **)

  let cost_f_pln_branch6 =
    S O

  (** val cost_f_pln_branch7 : nat **)

  let cost_f_pln_branch7 =
    S O

  (** val cost_f_pln_branch8 : nat **)

  let cost_f_pln_branch8 =
    S O

  (** val cost_f_pln_branch9 : nat **)

  let cost_f_pln_branch9 =
    S O

  (** val cost_f_Pln :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE list ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) ->
      nat **)

  let cost_f_Pln v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (_, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> cost_f_pln_branch6
              | ve :: _ ->
                add ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                  (add
                    ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                    (add
                      (Coq_vpg.cost_eqvv
                        (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                          (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                          e))
                        (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                          ve)) cost_f_pln_branch5)))
           | r0 :: _ ->
             (match r0 with
              | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> cost_f_pln_branch8
                 | ve :: _ ->
                   add ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                     (add
                       ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                       (add
                         (Coq_vpg.cost_eqvv
                           (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                             (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                             e))
                           (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                             ve)) cost_f_pln_branch7)))
              | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                cost_f_pln_branch9))
        | ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (l, _, l1, _,
                                                                l2) ->
          (match t0 with
           | [] -> cost_f_pln_branch4
           | r0 :: _ ->
             (match r0 with
              | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                cost_f_pln_branch4
              | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', _, l1', _, l2') ->
                (match v with
                 | [] -> cost_f_pln_branch3
                 | ve :: _ ->
                   (match ve with
                    | ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                      add
                        (add
                          (add
                            (add
                              (add
                                (add
                                  (ExtractionWNoDup.Transducer.TimedSets.Parser.cost_goEps
                                    ExtractionWNoDup.Transducer.TimedSets.Parser.coq_P
                                    (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                                    e)) (Coq_vpg.cost_eqvv l l'))
                                (Coq_vpg.cost_eqvv l1 l1'))
                              (Coq_vpg.cost_eqvv l2 l2'))
                            (mul (S (S (S (S (S O))))) cost_andb))
                          (mul (S (S O)) cost_eq_str)) cost_f_pln_branch1
                    | _ ->
                      add
                        (add
                          (add
                            (add
                              (add
                                (add
                                  (add
                                    (add
                                      ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                                      ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE)
                                    (Coq_vpg.cost_eqvv
                                      (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                                        (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                                        e))
                                      (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                                        ve))) (Coq_vpg.cost_eqvv l l'))
                                (Coq_vpg.cost_eqvv l1 l1'))
                              (Coq_vpg.cost_eqvv l2 l2'))
                            (mul (S (S O)) cost_eq_str))
                          (mul (S (S (S (S (S O))))) cost_andb))
                        cost_f_pln_branch2)))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> cost_f_pln_branch6
           | ve :: _ ->
             add ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
               (add ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                 (add
                   (Coq_vpg.cost_eqvv
                     (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                       (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
                     (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE ve))
                   cost_f_pln_branch5)))
        | r0 :: _ ->
          (match r0 with
           | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (_, _, _) ->
             (match v with
              | [] -> cost_f_pln_branch8
              | ve :: _ ->
                add ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                  (add
                    ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                    (add
                      (Coq_vpg.cost_eqvv
                        (ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                          (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                          e))
                        (ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                          ve)) cost_f_pln_branch7)))
           | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (_, _, _,
                                                                   _, _) ->
             cost_f_pln_branch9)))

  (** val f_Pln' :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE list ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) ->
      bool c **)

  let f_Pln' v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (_, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> inc cost_f_pln_branch6 (ret false)
              | ve :: _ ->
                bind
                  (ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                    (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
                  (fun _l1 _ ->
                  bind
                    (ExtractionWNoDup.Transducer.TimedSets.Parser._beginE ve)
                    (fun _l2 _ ->
                    bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                      inc cost_f_pln_branch5 (ret out)))))
           | r0 :: _ ->
             (match r0 with
              | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> inc cost_f_pln_branch8 (ret false)
                 | ve :: _ ->
                   bind
                     (ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                       (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
                     (fun _l1 _ ->
                     bind
                       (ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                         ve) (fun _l2 _ ->
                       bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                         inc cost_f_pln_branch7 (ret out)))))
              | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                inc cost_f_pln_branch9 (ret false)))
        | ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (l, a, l1, b,
                                                                l2) ->
          (match t0 with
           | [] -> inc cost_f_pln_branch4 (ret false)
           | r0 :: _ ->
             (match r0 with
              | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                inc cost_f_pln_branch4 (ret false)
              | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', a', l1', b', l2') ->
                (match v with
                 | [] -> inc cost_f_pln_branch3 (ret false)
                 | ve :: _ ->
                   (match ve with
                    | ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                      bind
                        (ExtractionWNoDup.Transducer.TimedSets.Parser.goEps'
                          (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                          e)) (fun bb _ ->
                        bind (Coq_vpg.eqvv' l l') (fun out1 _ ->
                          bind (Coq_vpg.eqvv' l1 l1') (fun out2 _ ->
                            bind (Coq_vpg.eqvv' l2 l2') (fun out3 _ ->
                              bind (eq_str' a a') (fun out4 _ ->
                                bind (eq_str' b b') (fun out5 _ ->
                                  inc
                                    (add
                                      (mul (S (S (S (S (S O))))) cost_andb)
                                      cost_f_pln_branch1)
                                    (ret
                                      ((&&)
                                        ((&&)
                                          ((&&) ((&&) ((&&) bb out1) out2)
                                            out3) out4) out5))))))))
                    | x ->
                      bind (Coq_vpg.eqvv' l l') (fun out1 _ ->
                        bind (Coq_vpg.eqvv' l1 l1') (fun out2 _ ->
                          bind (Coq_vpg.eqvv' l2 l2') (fun out3 _ ->
                            bind (eq_str' a a') (fun out4 _ ->
                              bind (eq_str' b b') (fun out5 _ ->
                                bind
                                  (ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                                    (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
                                    e)) (fun _l1 _ ->
                                  bind
                                    (ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                                      x) (fun _l2 _ ->
                                    bind (Coq_vpg.eqvv' _l1 _l2)
                                      (fun out0 _ ->
                                      inc
                                        (add
                                          (mul (S (S (S (S (S O)))))
                                            cost_andb) cost_f_pln_branch2)
                                        (ret
                                          ((&&)
                                            ((&&)
                                              ((&&)
                                                ((&&) ((&&) out0 out1) out2)
                                                out3) out4) out5)))))))))))))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> inc cost_f_pln_branch6 (ret false)
           | ve :: _ ->
             bind
               (ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                 (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
               (fun _l1 _ ->
               bind (ExtractionWNoDup.Transducer.TimedSets.Parser._beginE ve)
                 (fun _l2 _ ->
                 bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                   inc cost_f_pln_branch5 (ret out)))))
        | r0 :: _ ->
          (match r0 with
           | ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (_, _, _) ->
             (match v with
              | [] -> inc cost_f_pln_branch8 (ret false)
              | ve :: _ ->
                bind
                  (ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                    (ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv e))
                  (fun _l1 _ ->
                  bind
                    (ExtractionWNoDup.Transducer.TimedSets.Parser._beginE ve)
                    (fun _l2 _ ->
                    bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                      inc cost_f_pln_branch7 (ret out)))))
           | ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (_, _, _,
                                                                   _, _) ->
             inc cost_f_pln_branch9 (ret false))))

  (** val cost_g_Pln : nat **)

  let cost_g_Pln =
    cost_snd

  (** val g_Pln' :
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge c **)

  let g_Pln' rr =
    inc cost_snd (ret (snd rr))

  (** val cost_filter_Pln_branch1 : nat **)

  let cost_filter_Pln_branch1 =
    S O

  (** val cost_filter_Pln_branch2 : nat **)

  let cost_filter_Pln_branch2 =
    S O

  (** val cost_filter_Pln :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE list ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> nat **)

  let rec cost_filter_Pln v t0 = function
  | [] -> cost_filter_Pln_branch1
  | x :: m' ->
    add (add (add (cost_f_Pln v t0 x) cost_if_stmt) cost_filter_Pln_branch2)
      (if f_Pln v t0 x
       then add (add cost_g_Pln (cost_filter_Pln v t0 m')) cons_ct
       else cost_filter_Pln v t0 m')

  (** val filter_Pln :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE list ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge list **)

  let filter_Pln v t0 m =
    ExtractionWNoDup.Transducer.TimedSets.Parser.filter_map m (f_Pln v t0) snd

  (** val filter_Pln' :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE list ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge list c **)

  let rec filter_Pln' v t0 = function
  | [] -> inc cost_filter_Pln_branch1 (ret [])
  | x :: m' ->
    bind (f_Pln' v t0 x) (fun fx _ ->
      if sumbool_of_bool fx
      then bind (g_Pln' x) (fun gx _ ->
             bind (filter_Pln' v t0 m') (fun res _ ->
               bind (cons' gx res) (fun out _ ->
                 inc (add cost_filter_Pln_branch2 cost_if_stmt) (ret out))))
      else bind (filter_Pln' v t0 m') (fun out _ ->
             inc (add cost_filter_Pln_branch2 cost_if_stmt) (ret out)))

  (** val cost_ec_inlist_branch1 : nat **)

  let cost_ec_inlist_branch1 =
    S O

  (** val cost_ec_inlist_branch2 : nat **)

  let cost_ec_inlist_branch2 =
    S O

  (** val cost_ec_inlist_branch3 : nat **)

  let cost_ec_inlist_branch3 =
    S O

  (** val cost_ec_inlist :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge list -> nat **)

  let rec cost_ec_inlist x = function
  | [] -> cost_ec_inlist_branch1
  | y :: l' ->
    add (ExtractionWNoDup.Transducer.TimedSets.Coq_timed_ec.cost_compare x y)
      (match ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_ec_as_OT.compare
               x y with
       | Eq -> cost_ec_inlist_branch2
       | _ -> add (cost_ec_inlist x l') cost_ec_inlist_branch3)

  (** val ec_inlist' :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge list -> bool c **)

  let rec ec_inlist' x = function
  | [] -> inc cost_ec_inlist_branch1 (ret false)
  | y :: l' ->
    bind (ExtractionWNoDup.Transducer.TimedSets.Coq_timed_ec.compare' x y)
      (fun out1 _ ->
      bind
        (match out1 with
         | Eq -> inc cost_ec_inlist_branch2 (ret true)
         | _ ->
           bind (ec_inlist' x l') (fun out _ ->
             inc cost_ec_inlist_branch3 (ret out))) (fun out _ -> ret out))

  (** val cost_nodup_Pln :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE list ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> nat **)

  let cost_nodup_Pln v t0 m =
    add (cost_filter_Pln v t0 m)
      (cost_nodup ExtractionWNoDup.Transducer.Transducer2.ec_inlist
        cost_ec_inlist (filter_Pln v t0 m))

  (** val nodup_Pln' :
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE list ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge list c **)

  let nodup_Pln' v t0 m =
    bind (filter_Pln' v t0 m) (fun m' _ ->
      bind
        (nodup' ExtractionWNoDup.Transducer.Transducer2.ec_inlist
          cost_ec_inlist ec_inlist' m') (fun out _ -> ret out))

  (** val cost_map_sub_Pln :
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      -> (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> nat **)

  let cost_map_sub_Pln vt m =
    let (v, t0) = vt in
    add (cost_nodup_Pln v t0 m)
      (cost_map (fun _ -> add cons_ct time_pair)
        (nodup ExtractionWNoDup.Transducer.Transducer2.ec_inlist
          (filter_Pln v t0 m)))

  (** val map_sub_Pln :
      (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      -> (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list **)

  let map_sub_Pln vt m =
    let (v, t0) = vt in
    map (fun e ->
      (((ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Plnv e) :: v),
      t0))
      (nodup ExtractionWNoDup.Transducer.Transducer2.ec_inlist
        (filter_Pln v t0 m))

  (** val map_sub_Pln' :
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      -> (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list c **)

  let map_sub_Pln' vt m =
    let (v, t0) = vt in
    bind (nodup_Pln' v t0 m) (fun m1 _ ->
      bind
        (map' (fun e ->
          (((ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Plnv
          e) :: v), t0)) (fun _ -> add cons_ct time_pair) (fun e ->
          bind
            (cons'
              (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Plnv e)
              v) (fun ve _ -> bind (pair' ve t0) (fun out _ -> ret out))) m1)
        (fun out _ -> ret out))

  (** val cost_map_v_Pln :
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list -> nat **)

  let cost_map_v_Pln m v =
    cost_map (fun vt -> cost_map_sub_Pln vt m) v

  (** val map_v_Pln :
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list -> (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list list **)

  let map_v_Pln m v =
    map (fun vt -> map_sub_Pln vt m) v

  (** val map_v_Pln' :
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_PlnEdge) list
      -> (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list -> (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list list c **)

  let map_v_Pln' m v =
    map' (fun vt -> map_sub_Pln vt m) (fun vt -> cost_map_sub_Pln vt m)
      (fun vt -> map_sub_Pln' vt m) v

  (** val cost_elements_Pln : nat **)

  let cost_elements_Pln =
    S O

  (** val cost_inner_Pln :
      ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.t ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list -> nat **)

  let cost_inner_Pln m v =
    add
      (add cost_elements_Pln
        (cost_map_v_Pln
          (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.elements
            m) v))
      (cost_concat
        (map_v_Pln
          (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.elements
            m) v))

  (** val inner_Pln :
      ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.t ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list -> (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list **)

  let inner_Pln m v =
    concat
      (map_v_Pln
        (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.elements
          m) v)

  (** val vc_elements :
      ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.t ->
      ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.elt
      list c **)

  let vc_elements m =
    inc cost_elements_Pln
      (ret
        (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.elements
          m))

  (** val inner_Pln' :
      ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Coq_vc_set.t ->
      (ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list -> (ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.coq_VE
      list * ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge list)
      list c **)

  let inner_Pln' m v =
    bind (vc_elements m) (fun m' _ ->
      bind (map_v_Pln' m' v) (fun m'0 _ ->
        bind (_concat m'0) (fun out _ -> ret out)))
 end

module TimedExtractionCal =
 functor (G:VPG) ->
 struct
  module TimedExtractionPln = TimedExtractionPln(G)

  (** val cost_if_stmt : nat **)

  let cost_if_stmt =
    S O

  (** val cost_filter_reti_var : nat **)

  let cost_filter_reti_var =
    S O

  (** val time_filter_reti_base : nat **)

  let time_filter_reti_base =
    S O

  (** val cost_snd : nat **)

  let cost_snd =
    S O

  (** val cost_var_f_Cal_branch1_Cal : nat **)

  let cost_var_f_Cal_branch1_Cal =
    S O

  (** val cost_var_f_Cal_branch2_Cal : nat **)

  let cost_var_f_Cal_branch2_Cal =
    S O

  (** val cost_var_f_Cal_branch3_Cal : nat **)

  let cost_var_f_Cal_branch3_Cal =
    S O

  (** val cost_var_f_Cal_branch4_Cal : nat **)

  let cost_var_f_Cal_branch4_Cal =
    S O

  (** val cost_var_f_Cal_branch5_Cal : nat **)

  let cost_var_f_Cal_branch5_Cal =
    S O

  (** val f_Cal :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      -> bool **)

  let f_Cal v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (
            _, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> false
              | ve :: _ ->
                Coq_vpg.eqvv
                  (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                    e))
                  (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                    ve))
           | y :: _ ->
             (match y with
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> false
                 | ve :: _ ->
                   Coq_vpg.eqvv
                     (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                       (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                       e))
                     (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                       ve))
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                false))
        | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (
            l, a, l1, b, l2) ->
          (match t0 with
           | [] -> false
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                false
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', a', l1', b', l2') ->
                (&&)
                  ((&&)
                    ((&&)
                      ((&&) ((&&) (Coq_vpg.eqvv l l') (Coq_vpg.eqvv l1 l1'))
                        (Coq_vpg.eqvv l2 l2')) (eq_str a a')) (eq_str b b'))
                  (match v with
                   | [] -> false
                   | ve :: _ ->
                     (match ve with
                      | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                        TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.goEps
                          (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                          e)
                      | _ ->
                        Coq_vpg.eqvv
                          (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                            (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                            e))
                          (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                            ve))))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> false
           | ve :: _ ->
             Coq_vpg.eqvv
               (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                 (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                 e))
               (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                 ve))
        | r0 :: _ ->
          (match r0 with
           | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
               _, _, _) ->
             (match v with
              | [] -> false
              | ve :: _ ->
                Coq_vpg.eqvv
                  (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                    e))
                  (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                    ve))
           | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
               _, _, _, _, _) ->
             false)))

  (** val cost_f_Cal_branch1 : nat **)

  let cost_f_Cal_branch1 =
    S O

  (** val cost_f_Cal_branch2 : nat **)

  let cost_f_Cal_branch2 =
    S O

  (** val cost_f_Cal_branch3 : nat **)

  let cost_f_Cal_branch3 =
    S O

  (** val cost_f_Cal_branch4 : nat **)

  let cost_f_Cal_branch4 =
    S O

  (** val cost_f_Cal_branch5 : nat **)

  let cost_f_Cal_branch5 =
    S O

  (** val cost_f_Cal_branch6 : nat **)

  let cost_f_Cal_branch6 =
    S O

  (** val cost_f_Cal_branch7 : nat **)

  let cost_f_Cal_branch7 =
    S O

  (** val cost_f_Cal_branch8 : nat **)

  let cost_f_Cal_branch8 =
    S O

  (** val cost_f_Cal_branch9 : nat **)

  let cost_f_Cal_branch9 =
    S O

  (** val cost_f_Cal :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      -> nat **)

  let cost_f_Cal v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (
            _, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> cost_f_Cal_branch6
              | ve :: _ ->
                add
                  TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                  (add
                    TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                    (add
                      (Coq_vpg.cost_eqvv
                        (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                          (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                          e))
                        (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                          ve)) cost_f_Cal_branch5)))
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> cost_f_Cal_branch8
                 | ve :: _ ->
                   add
                     TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                     (add
                       TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                       (add
                         (Coq_vpg.cost_eqvv
                           (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                             (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                             e))
                           (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                             ve)) cost_f_Cal_branch7)))
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                cost_f_Cal_branch9))
        | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (
            l, _, l1, _, l2) ->
          (match t0 with
           | [] -> cost_f_Cal_branch4
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                cost_f_Cal_branch4
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', _, l1', _, l2') ->
                (match v with
                 | [] -> cost_f_Cal_branch3
                 | ve :: _ ->
                   (match ve with
                    | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                      add
                        (add
                          (add
                            (add
                              (add
                                (add
                                  (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_goEps
                                    TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_P
                                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                                    e)) (Coq_vpg.cost_eqvv l l'))
                                (Coq_vpg.cost_eqvv l1 l1'))
                              (Coq_vpg.cost_eqvv l2 l2'))
                            (mul (S (S (S (S (S O))))) cost_andb))
                          (mul (S (S O)) cost_eq_str)) cost_f_Cal_branch1
                    | _ ->
                      add
                        (add
                          (add
                            (add
                              (add
                                (add
                                  (add
                                    (add
                                      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                                      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE)
                                    (Coq_vpg.cost_eqvv
                                      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                                        (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                                        e))
                                      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                                        ve))) (Coq_vpg.cost_eqvv l l'))
                                (Coq_vpg.cost_eqvv l1 l1'))
                              (Coq_vpg.cost_eqvv l2 l2'))
                            (mul (S (S O)) cost_eq_str))
                          (mul (S (S (S (S (S O))))) cost_andb))
                        cost_f_Cal_branch2)))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> cost_f_Cal_branch6
           | ve :: _ ->
             add
               TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
               (add
                 TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                 (add
                   (Coq_vpg.cost_eqvv
                     (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                       (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                       e))
                     (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                       ve)) cost_f_Cal_branch5)))
        | r0 :: _ ->
          (match r0 with
           | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
               _, _, _) ->
             (match v with
              | [] -> cost_f_Cal_branch8
              | ve :: _ ->
                add
                  TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                  (add
                    TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                    (add
                      (Coq_vpg.cost_eqvv
                        (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                          (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                          e))
                        (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                          ve)) cost_f_Cal_branch7)))
           | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
               _, _, _, _, _) ->
             cost_f_Cal_branch9)))

  (** val f_Cal' :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      -> bool c **)

  let f_Cal' v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (
            _, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> inc cost_f_Cal_branch6 (ret false)
              | ve :: _ ->
                bind
                  (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                    e)) (fun _l1 _ ->
                  bind
                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                      ve) (fun _l2 _ ->
                    bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                      inc cost_f_Cal_branch5 (ret out)))))
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> inc cost_f_Cal_branch8 (ret false)
                 | ve :: _ ->
                   bind
                     (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                       (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                       e)) (fun _l1 _ ->
                     bind
                       (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                         ve) (fun _l2 _ ->
                       bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                         inc cost_f_Cal_branch7 (ret out)))))
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                inc cost_f_Cal_branch9 (ret false)))
        | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (
            l, a, l1, b, l2) ->
          (match t0 with
           | [] -> inc cost_f_Cal_branch4 (ret false)
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                inc cost_f_Cal_branch4 (ret false)
              | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', a', l1', b', l2') ->
                (match v with
                 | [] -> inc cost_f_Cal_branch3 (ret false)
                 | ve :: _ ->
                   (match ve with
                    | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                      bind
                        (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.goEps'
                          (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                          e)) (fun bb _ ->
                        bind (Coq_vpg.eqvv' l l') (fun out1 _ ->
                          bind (Coq_vpg.eqvv' l1 l1') (fun out2 _ ->
                            bind (Coq_vpg.eqvv' l2 l2') (fun out3 _ ->
                              bind (eq_str' a a') (fun out4 _ ->
                                bind (eq_str' b b') (fun out5 _ ->
                                  inc
                                    (add
                                      (mul (S (S (S (S (S O))))) cost_andb)
                                      cost_f_Cal_branch1)
                                    (ret
                                      ((&&)
                                        ((&&)
                                          ((&&) ((&&) ((&&) bb out1) out2)
                                            out3) out4) out5))))))))
                    | x ->
                      bind (Coq_vpg.eqvv' l l') (fun out1 _ ->
                        bind (Coq_vpg.eqvv' l1 l1') (fun out2 _ ->
                          bind (Coq_vpg.eqvv' l2 l2') (fun out3 _ ->
                            bind (eq_str' a a') (fun out4 _ ->
                              bind (eq_str' b b') (fun out5 _ ->
                                bind
                                  (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                                    e)) (fun _l1 _ ->
                                  bind
                                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                                      x) (fun _l2 _ ->
                                    bind (Coq_vpg.eqvv' _l1 _l2)
                                      (fun out0 _ ->
                                      inc
                                        (add
                                          (mul (S (S (S (S (S O)))))
                                            cost_andb) cost_f_Cal_branch2)
                                        (ret
                                          ((&&)
                                            ((&&)
                                              ((&&)
                                                ((&&) ((&&) out0 out1) out2)
                                                out3) out4) out5)))))))))))))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> inc cost_f_Cal_branch6 (ret false)
           | ve :: _ ->
             bind
               (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                 (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                 e)) (fun _l1 _ ->
               bind
                 (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                   ve) (fun _l2 _ ->
                 bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                   inc cost_f_Cal_branch5 (ret out)))))
        | r0 :: _ ->
          (match r0 with
           | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
               _, _, _) ->
             (match v with
              | [] -> inc cost_f_Cal_branch8 (ret false)
              | ve :: _ ->
                bind
                  (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
                    e)) (fun _l1 _ ->
                  bind
                    (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                      ve) (fun _l2 _ ->
                    bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                      inc cost_f_Cal_branch7 (ret out)))))
           | TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
               _, _, _, _, _) ->
             inc cost_f_Cal_branch9 (ret false))))

  (** val cost_g_Cal : nat **)

  let cost_g_Cal =
    cost_snd

  (** val g_Cal' :
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      c **)

  let g_Cal' rr =
    inc
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cons_snd
      (ret (snd rr))

  (** val cost_filter_Cal_branch1 : nat **)

  let cost_filter_Cal_branch1 =
    S O

  (** val cost_filter_Cal_branch2 : nat **)

  let cost_filter_Cal_branch2 =
    S O

  (** val cost_filter_Cal :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list -> nat **)

  let rec cost_filter_Cal v t0 = function
  | [] -> cost_filter_Cal_branch1
  | x :: m' ->
    add (add (add (cost_f_Cal v t0 x) cost_if_stmt) cost_filter_Cal_branch2)
      (if f_Cal v t0 x
       then add (add cost_g_Cal (cost_filter_Cal v t0 m')) cons_ct
       else cost_filter_Cal v t0 m')

  (** val filter_Cal :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      list **)

  let filter_Cal v t0 m =
    TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.filter_map
      m (f_Cal v t0) snd

  (** val filter_Cal' :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      list c **)

  let rec filter_Cal' v t0 = function
  | [] -> inc cost_filter_Cal_branch1 (ret [])
  | x :: m' ->
    bind (f_Cal' v t0 x) (fun fx _ ->
      if sumbool_of_bool fx
      then bind (g_Cal' x) (fun gx _ ->
             bind (filter_Cal' v t0 m') (fun res _ ->
               bind (cons' gx res) (fun out _ ->
                 inc (add cost_filter_Cal_branch2 cost_if_stmt) (ret out))))
      else bind (filter_Cal' v t0 m') (fun out _ ->
             inc (add cost_filter_Cal_branch2 cost_if_stmt) (ret out)))

  (** val cost_ea_inlist_branch1 : nat **)

  let cost_ea_inlist_branch1 =
    S O

  (** val cost_ea_inlist_branch2 : nat **)

  let cost_ea_inlist_branch2 =
    S O

  (** val cost_ea_inlist_branch3 : nat **)

  let cost_ea_inlist_branch3 =
    S O

  (** val cost_ea_inlist :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      list -> nat **)

  let rec cost_ea_inlist x = function
  | [] -> cost_ea_inlist_branch1
  | y :: l' ->
    add
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Coq_timed_ea.cost_compare
        x y)
      (match TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_ea_as_OT.compare
               x y with
       | Eq -> cost_ea_inlist_branch2
       | _ -> add (cost_ea_inlist x l') cost_ea_inlist_branch3)

  (** val ea_inlist' :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      list -> bool c **)

  let rec ea_inlist' x = function
  | [] -> inc cost_ea_inlist_branch1 (ret false)
  | y :: l' ->
    bind
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Coq_timed_ea.compare'
        x y) (fun out1 _ ->
      bind
        (match out1 with
         | Eq -> inc cost_ea_inlist_branch2 (ret true)
         | _ ->
           bind (ea_inlist' x l') (fun out _ ->
             inc cost_ea_inlist_branch3 (ret out))) (fun out _ -> ret out))

  (** val cost_nodup_Cal :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list -> nat **)

  let cost_nodup_Cal v t0 m =
    add (cost_filter_Cal v t0 m)
      (cost_nodup
        TimedExtractionPln.ExtractionWNoDup.Transducer.Transducer2.ea_inlist
        cost_ea_inlist (filter_Cal v t0 m))

  (** val nodup_Cal' :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      list c **)

  let nodup_Cal' v t0 m =
    bind (filter_Cal' v t0 m) (fun m' _ ->
      bind
        (nodup'
          TimedExtractionPln.ExtractionWNoDup.Transducer.Transducer2.ea_inlist
          cost_ea_inlist ea_inlist' m') (fun out _ -> ret out))

  (** val cost_map_sub_Cal :
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list -> nat **)

  let cost_map_sub_Cal vt m =
    let (v, t0) = vt in
    add (cost_nodup_Cal v t0 m)
      (cost_map (fun _ -> add (add cons_ct time_pair) (cost_tail t0))
        (nodup
          TimedExtractionPln.ExtractionWNoDup.Transducer.Transducer2.ea_inlist
          (filter_Cal v t0 m)))

  (** val map_sub_Cal :
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list **)

  let map_sub_Cal vt m =
    let (v, t0) = vt in
    map (fun e ->
      (((TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
      e) :: v), (tl t0)))
      (nodup
        TimedExtractionPln.ExtractionWNoDup.Transducer.Transducer2.ea_inlist
        (filter_Cal v t0 m))

  (** val map_sub_Cal' :
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list c **)

  let map_sub_Cal' vt m =
    let (v, t0) = vt in
    bind (nodup_Cal' v t0 m) (fun m1 _ ->
      bind
        (map' (fun e ->
          (((TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
          e) :: v), (tl t0))) (fun _ ->
          add (add cons_ct time_pair) (cost_tail t0)) (fun e ->
          bind
            (cons'
              (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
              e) v) (fun ve _ ->
            bind (tail' t0) (fun t' _ ->
              bind (pair' ve t') (fun out _ -> ret out)))) m1) (fun out _ ->
        ret out))

  (** val cost_map_v_Cal :
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list -> nat **)

  let cost_map_v_Cal m v =
    cost_map (fun vt -> cost_map_sub_Cal vt m) v

  (** val map_v_Cal :
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list list **)

  let map_v_Cal m v =
    map (fun vt -> map_sub_Cal vt m) v

  (** val map_v_Cal' :
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge)
      list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list list c **)

  let map_v_Cal' m v =
    map' (fun vt -> map_sub_Cal vt m) (fun vt -> cost_map_sub_Cal vt m)
      (fun vt -> map_sub_Cal' vt m) v

  (** val cost_elements_Cal : nat **)

  let cost_elements_Cal =
    S O

  (** val cost_inner_Cal :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.t
      ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list -> nat **)

  let cost_inner_Cal m v =
    add
      (add cost_elements_Cal
        (cost_map_v_Cal
          (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.elements
            m) v))
      (cost_concat
        (map_v_Cal
          (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.elements
            m) v))

  (** val inner_Cal :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.t
      ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list **)

  let inner_Cal m v =
    concat
      (map_v_Cal
        (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.elements
          m) v)

  (** val va_elements :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.t
      ->
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.elt
      list c **)

  let va_elements m =
    inc cost_elements_Cal
      (ret
        (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.elements
          m))

  (** val inner_Cal' :
      TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.t
      ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list c **)

  let inner_Cal' m v =
    bind (va_elements m) (fun m' _ ->
      bind (map_v_Cal' m' v) (fun m'0 _ ->
        bind (_concat m'0) (fun out _ -> ret out)))
 end

module TimedExtractionRet =
 functor (G:VPG) ->
 struct
  module TimedExtractionCal = TimedExtractionCal(G)

  (** val cost_if_stmt : nat **)

  let cost_if_stmt =
    S O

  (** val cost_filter_reti_var : nat **)

  let cost_filter_reti_var =
    S O

  (** val time_filter_reti_base : nat **)

  let time_filter_reti_base =
    S O

  (** val cost_var_f_branch1_Ret : nat **)

  let cost_var_f_branch1_Ret =
    S O

  (** val cost_var_f_branch2_Ret : nat **)

  let cost_var_f_branch2_Ret =
    S O

  (** val cost_var_f_branch3_Ret : nat **)

  let cost_var_f_branch3_Ret =
    S O

  (** val cost_var_f_branch4_Ret : nat **)

  let cost_var_f_branch4_Ret =
    S O

  (** val cost_var_f_branch5_Ret : nat **)

  let cost_var_f_branch5_Ret =
    S O

  (** val f :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      -> bool **)

  let f v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (
            _, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> false
              | ve :: _ ->
                Coq_vpg.eqvv
                  (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                    e))
                  (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                    ve))
           | y :: _ ->
             (match y with
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> false
                 | ve :: _ ->
                   Coq_vpg.eqvv
                     (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                       (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                       e))
                     (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                       ve))
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                false))
        | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (
            l, a, l1, b, l2) ->
          (match t0 with
           | [] -> false
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                false
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', a', l1', b', l2') ->
                (&&)
                  ((&&)
                    ((&&)
                      ((&&) ((&&) (Coq_vpg.eqvv l l') (Coq_vpg.eqvv l1 l1'))
                        (Coq_vpg.eqvv l2 l2')) (eq_str a a')) (eq_str b b'))
                  (match v with
                   | [] -> false
                   | ve :: _ ->
                     (match ve with
                      | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                        TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.goEps
                          (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                          e)
                      | _ ->
                        Coq_vpg.eqvv
                          (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                            (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                            e))
                          (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                            ve))))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> false
           | ve :: _ ->
             Coq_vpg.eqvv
               (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                 (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                 e))
               (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                 ve))
        | r0 :: _ ->
          (match r0 with
           | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
               _, _, _) ->
             (match v with
              | [] -> false
              | ve :: _ ->
                Coq_vpg.eqvv
                  (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                    e))
                  (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                    ve))
           | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
               _, _, _, _, _) ->
             false)))

  (** val cost_f_branch1 : nat **)

  let cost_f_branch1 =
    S O

  (** val cost_f_branch2 : nat **)

  let cost_f_branch2 =
    S O

  (** val cost_f_branch3 : nat **)

  let cost_f_branch3 =
    S O

  (** val cost_f_branch4 : nat **)

  let cost_f_branch4 =
    S O

  (** val cost_f_branch5 : nat **)

  let cost_f_branch5 =
    S O

  (** val cost_f_branch6 : nat **)

  let cost_f_branch6 =
    S O

  (** val cost_f_branch7 : nat **)

  let cost_f_branch7 =
    S O

  (** val cost_f_branch8 : nat **)

  let cost_f_branch8 =
    S O

  (** val cost_f_branch9 : nat **)

  let cost_f_branch9 =
    S O

  (** val cost_f :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      -> nat **)

  let cost_f v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (
            _, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> cost_f_branch6
              | ve :: _ ->
                add
                  TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                  (add
                    TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                    (add
                      (Coq_vpg.cost_eqvv
                        (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                          (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                          e))
                        (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                          ve)) cost_f_branch5)))
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> cost_f_branch8
                 | ve :: _ ->
                   add
                     TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                     (add
                       TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                       (add
                         (Coq_vpg.cost_eqvv
                           (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                             (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                             e))
                           (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                             ve)) cost_f_branch7)))
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                cost_f_branch9))
        | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (
            l, _, l1, _, l2) ->
          (match t0 with
           | [] -> cost_f_branch4
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                cost_f_branch4
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', _, l1', _, l2') ->
                (match v with
                 | [] -> cost_f_branch3
                 | ve :: _ ->
                   (match ve with
                    | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                      add
                        (add
                          (add
                            (add
                              (add
                                (add
                                  (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_goEps
                                    TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_P
                                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                                    e)) (Coq_vpg.cost_eqvv l l'))
                                (Coq_vpg.cost_eqvv l1 l1'))
                              (Coq_vpg.cost_eqvv l2 l2'))
                            (mul (S (S (S (S (S O))))) cost_andb))
                          (mul (S (S O)) cost_eq_str)) cost_f_branch1
                    | _ ->
                      add
                        (add
                          (add
                            (add
                              (add
                                (add
                                  (add
                                    (add
                                      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                                      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE)
                                    (Coq_vpg.cost_eqvv
                                      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                                        (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                                        e))
                                      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                                        ve))) (Coq_vpg.cost_eqvv l l'))
                                (Coq_vpg.cost_eqvv l1 l1'))
                              (Coq_vpg.cost_eqvv l2 l2'))
                            (mul (S (S O)) cost_eq_str))
                          (mul (S (S (S (S (S O))))) cost_andb))
                        cost_f_branch2)))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> cost_f_branch6
           | ve :: _ ->
             add
               TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
               (add
                 TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                 (add
                   (Coq_vpg.cost_eqvv
                     (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                       (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                       e))
                     (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                       ve)) cost_f_branch5)))
        | r0 :: _ ->
          (match r0 with
           | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
               _, _, _) ->
             (match v with
              | [] -> cost_f_branch8
              | ve :: _ ->
                add
                  TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_endE
                  (add
                    TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.cost_beginE
                    (add
                      (Coq_vpg.cost_eqvv
                        (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.endE
                          (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                          e))
                        (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.beginE
                          ve)) cost_f_branch7)))
           | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
               _, _, _, _, _) ->
             cost_f_branch9)))

  (** val f' :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      -> bool c **)

  let f' v t0 = function
  | (r, e) ->
    (match r with
     | Some c0 ->
       (match c0 with
        | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE (
            _, _, _) ->
          (match t0 with
           | [] ->
             (match v with
              | [] -> inc cost_f_branch6 (ret false)
              | ve :: _ ->
                bind
                  (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                    e)) (fun _l1 _ ->
                  bind
                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                      ve) (fun _l2 _ ->
                    bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                      inc cost_f_branch5 (ret out)))))
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                (match v with
                 | [] -> inc cost_f_branch8 (ret false)
                 | ve :: _ ->
                   bind
                     (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                       (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                       e)) (fun _l1 _ ->
                     bind
                       (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                         ve) (fun _l2 _ ->
                       bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                         inc cost_f_branch7 (ret out)))))
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  _, _, _, _, _) ->
                inc cost_f_branch9 (ret false)))
        | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE (
            l, a, l1, b, l2) ->
          (match t0 with
           | [] -> inc cost_f_branch4 (ret false)
           | r0 :: _ ->
             (match r0 with
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
                  _, _, _) ->
                inc cost_f_branch4 (ret false)
              | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
                  l', a', l1', b', l2') ->
                (match v with
                 | [] -> inc cost_f_branch3 (ret false)
                 | ve :: _ ->
                   (match ve with
                    | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv _ ->
                      bind
                        (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.goEps'
                          (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                          e)) (fun bb _ ->
                        bind (Coq_vpg.eqvv' l l') (fun out1 _ ->
                          bind (Coq_vpg.eqvv' l1 l1') (fun out2 _ ->
                            bind (Coq_vpg.eqvv' l2 l2') (fun out3 _ ->
                              bind (eq_str' a a') (fun out4 _ ->
                                bind (eq_str' b b') (fun out5 _ ->
                                  inc
                                    (add
                                      (mul (S (S (S (S (S O))))) cost_andb)
                                      cost_f_branch1)
                                    (ret
                                      ((&&)
                                        ((&&)
                                          ((&&) ((&&) ((&&) bb out1) out2)
                                            out3) out4) out5))))))))
                    | x ->
                      bind (Coq_vpg.eqvv' l l') (fun out1 _ ->
                        bind (Coq_vpg.eqvv' l1 l1') (fun out2 _ ->
                          bind (Coq_vpg.eqvv' l2 l2') (fun out3 _ ->
                            bind (eq_str' a a') (fun out4 _ ->
                              bind (eq_str' b b') (fun out5 _ ->
                                bind
                                  (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                                    e)) (fun _l1 _ ->
                                  bind
                                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                                      x) (fun _l2 _ ->
                                    bind (Coq_vpg.eqvv' _l1 _l2)
                                      (fun out0 _ ->
                                      inc
                                        (add
                                          (mul (S (S (S (S (S O)))))
                                            cost_andb) cost_f_branch2)
                                        (ret
                                          ((&&)
                                            ((&&)
                                              ((&&)
                                                ((&&) ((&&) out0 out1) out2)
                                                out3) out4) out5)))))))))))))))
     | None ->
       (match t0 with
        | [] ->
          (match v with
           | [] -> inc cost_f_branch6 (ret false)
           | ve :: _ ->
             bind
               (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                 (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                 e)) (fun _l1 _ ->
               bind
                 (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                   ve) (fun _l2 _ ->
                 bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                   inc cost_f_branch5 (ret out)))))
        | r0 :: _ ->
          (match r0 with
           | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE (
               _, _, _) ->
             (match v with
              | [] -> inc cost_f_branch8 (ret false)
              | ve :: _ ->
                bind
                  (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._endE
                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
                    e)) (fun _l1 _ ->
                  bind
                    (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser._beginE
                      ve) (fun _l2 _ ->
                    bind (Coq_vpg.eqvv' _l1 _l2) (fun out _ ->
                      inc cost_f_branch7 (ret out)))))
           | TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE (
               _, _, _, _, _) ->
             inc cost_f_branch9 (ret false))))

  (** val cost_g : nat **)

  let cost_g =
    TimedExtractionCal.TimedExtractionPln.cost_snd

  (** val g' :
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      c **)

  let g' rr =
    inc TimedExtractionCal.TimedExtractionPln.cost_snd (ret (snd rr))

  (** val cost_filter_Ret_branch1 : nat **)

  let cost_filter_Ret_branch1 =
    S O

  (** val cost_filter_Ret_branch2 : nat **)

  let cost_filter_Ret_branch2 =
    S O

  (** val cost_filter_Ret :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list -> nat **)

  let rec cost_filter_Ret v t0 = function
  | [] -> cost_filter_Ret_branch1
  | x :: m' ->
    add (add (add (cost_f v t0 x) cost_if_stmt) cost_filter_Ret_branch2)
      (if f v t0 x
       then add (add cost_g (cost_filter_Ret v t0 m')) cons_ct
       else cost_filter_Ret v t0 m')

  (** val filter_Ret :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list **)

  let filter_Ret v t0 m =
    TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.filter_map
      m (f v t0) snd

  (** val filter_Ret' :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list c **)

  let rec filter_Ret' v t0 = function
  | [] -> inc cost_filter_Ret_branch1 (ret [])
  | x :: m' ->
    bind (f' v t0 x) (fun fx _ ->
      if sumbool_of_bool fx
      then bind (g' x) (fun gx _ ->
             bind (filter_Ret' v t0 m') (fun res _ ->
               bind (cons' gx res) (fun out _ ->
                 inc (add cost_filter_Ret_branch2 cost_if_stmt) (ret out))))
      else bind (filter_Ret' v t0 m') (fun out _ ->
             inc (add cost_filter_Ret_branch2 cost_if_stmt) (ret out)))

  (** val cost_eb_inlist_branch1 : nat **)

  let cost_eb_inlist_branch1 =
    S O

  (** val cost_eb_inlist_branch2 : nat **)

  let cost_eb_inlist_branch2 =
    S O

  (** val cost_eb_inlist_branch3 : nat **)

  let cost_eb_inlist_branch3 =
    S O

  (** val cost_eb_inlist :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list -> nat **)

  let rec cost_eb_inlist x = function
  | [] -> cost_eb_inlist_branch1
  | y :: l' ->
    add
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Coq_timed_eb.cost_compare
        x y)
      (match TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_eb_as_OT.compare
               x y with
       | Eq -> cost_eb_inlist_branch2
       | _ -> add (cost_eb_inlist x l') cost_eb_inlist_branch3)

  (** val eb_inlist' :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list -> bool c **)

  let rec eb_inlist' x = function
  | [] -> inc cost_eb_inlist_branch1 (ret false)
  | y :: l' ->
    bind
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Coq_timed_eb.compare'
        x y) (fun out1 _ ->
      bind
        (match out1 with
         | Eq -> inc cost_eb_inlist_branch2 (ret true)
         | _ ->
           bind (eb_inlist' x l') (fun out _ ->
             inc cost_eb_inlist_branch3 (ret out))) (fun out _ -> ret out))

  (** val cost_nodup_Ret :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list -> nat **)

  let cost_nodup_Ret v t0 m =
    add (cost_filter_Ret v t0 m)
      (cost_nodup
        TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.Transducer2.eb_inlist
        cost_eb_inlist (filter_Ret v t0 m))

  (** val nodup_Ret' :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list c **)

  let nodup_Ret' v t0 m =
    bind (filter_Ret' v t0 m) (fun m' _ ->
      bind
        (nodup'
          TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.Transducer2.eb_inlist
          cost_eb_inlist eb_inlist' m') (fun out _ -> ret out))

  (** val cost_map_sub :
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list -> nat **)

  let cost_map_sub vt m =
    let (v, t0) = vt in
    add (cost_nodup_Ret v t0 m)
      (cost_map (fun _ -> add (mul (S (S O)) cons_ct) time_pair)
        (nodup
          TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.Transducer2.eb_inlist
          (filter_Ret v t0 m)))

  (** val map_sub :
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list **)

  let map_sub vt m =
    let (v, t0) = vt in
    map (fun e ->
      (((TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
      e) :: v), (e :: t0)))
      (nodup
        TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.Transducer2.eb_inlist
        (filter_Ret v t0 m))

  (** val map_sub' :
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list c **)

  let map_sub' vt m =
    let (v, t0) = vt in
    bind (nodup_Ret' v t0 m) (fun m1 _ ->
      bind
        (map' (fun e ->
          (((TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
          e) :: v), (e :: t0))) (fun _ ->
          add (mul (S (S O)) cons_ct) time_pair) (fun e ->
          bind
            (cons'
              (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
              e) v) (fun ve _ ->
            bind (cons' e t0) (fun t' _ ->
              bind (pair' ve t') (fun out _ -> ret out)))) m1) (fun out _ ->
        ret out))

  (** val cost_map_v :
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list -> nat **)

  let cost_map_v m v =
    cost_map (fun vt -> cost_map_sub vt m) v

  (** val map_v :
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list list **)

  let map_v m v =
    map (fun vt -> map_sub vt m) v

  (** val map_v' :
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_CalEdge
      option * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge)
      list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list list c **)

  let map_v' m v =
    map' (fun vt -> map_sub vt m) (fun vt -> cost_map_sub vt m) (fun vt ->
      map_sub' vt m) v

  (** val cost_elements_Ret : nat **)

  let cost_elements_Ret =
    S O

  (** val cost_inner :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.t
      ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list -> nat **)

  let cost_inner m v =
    add
      (add cost_elements_Ret
        (cost_map_v
          (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.elements
            m) v))
      (cost_concat
        (map_v
          (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.elements
            m) v))

  (** val inner :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.t
      ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list **)

  let inner m v =
    concat
      (map_v
        (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.elements
          m) v)

  (** val vb_elements :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.t
      ->
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.elt
      list c **)

  let vb_elements m =
    inc cost_elements_Ret
      (ret
        (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.elements
          m))

  (** val inner' :
      TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.t
      ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list c **)

  let inner' m v =
    bind (vb_elements m) (fun m' _ ->
      bind (map_v' m' v) (fun m'0 _ ->
        bind (_concat m'0) (fun out _ -> ret out)))
 end

module TimedExtraction =
 functor (G:VPG) ->
 struct
  module TimedExtractionRet = TimedExtractionRet(G)

  (** val cost_extraction_one_step :
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_ME
      ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list -> nat **)

  let cost_extraction_one_step m v =
    match m with
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.CalCME m1 ->
      TimedExtractionRet.TimedExtractionCal.cost_inner_Cal m1 v
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PlnCME m1 ->
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.cost_inner_Pln
        m1 v
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.RetCME m1 ->
      TimedExtractionRet.cost_inner m1 v

  (** val extraction_one_step :
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_ME
      ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list **)

  let extraction_one_step m v =
    match m with
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.CalCME m1 ->
      TimedExtractionRet.TimedExtractionCal.inner_Cal m1 v
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PlnCME m1 ->
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.inner_Pln m1 v
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.RetCME m1 ->
      TimedExtractionRet.inner m1 v

  (** val extraction_one_step' :
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_ME
      ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list c **)

  let extraction_one_step' m v =
    match m with
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.CalCME m1 ->
      bind (TimedExtractionRet.TimedExtractionCal.inner_Cal' m1 v)
        (fun out _ -> ret out)
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PlnCME m1 ->
      bind
        (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.inner_Pln'
          m1 v) (fun out _ -> ret out)
    | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.RetCME m1 ->
      bind (TimedExtractionRet.inner' m1 v) (fun out _ -> ret out)

  (** val cost_extraction_bt : nat **)

  let cost_extraction_bt =
    S O

  (** val cost_extraction_inner : nat **)

  let cost_extraction_inner =
    S O

  (** val cost_extraction :
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_ME
      list ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list -> nat **)

  let rec cost_extraction m v =
    match m with
    | [] -> cost_extraction_bt
    | m1 :: m' ->
      (match m' with
       | [] -> cost_extraction_bt
       | _ :: _ ->
         add (cost_extraction_one_step m1 v)
           (let v' = extraction_one_step m1 v in
            add (cost_extraction m' v') cost_extraction_inner))

  (** val extraction' :
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_ME
      list ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      list * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_RetEdge
      list) list c **)

  let rec extraction' m v =
    match m with
    | [] -> inc cost_extraction_bt (ret v)
    | m1 :: m' ->
      (match m' with
       | [] -> inc cost_extraction_bt (ret v)
       | _ :: _ ->
         bind (extraction_one_step' m1 v) (fun v' _ ->
           bind (extraction' m' v') (fun out _ ->
             inc cost_extraction_inner (ret out))))

  (** val map_r_to_edge1 :
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.var * Coq_vpg.alt)
      ->
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      option **)

  let map_r_to_edge1 = function
  | (l, alt0) ->
    (match alt0 with
     | Coq_vpg.Alt_Epsilon -> None
     | Coq_vpg.Alt_Linear (t0, v) ->
       (match t0 with
        | Coq_vpg.Call a ->
          Some
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE
            (l, a, v)))
        | Coq_vpg.Plain c0 ->
          Some
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PlnE
            (l, c0, v)))
        | Coq_vpg.Ret b ->
          Some
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE
            (l, b, v))))
     | Coq_vpg.Alt_Match (t1, t2, v1, v2) ->
       Some
         (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
         (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatCalE
         (l, t1, v1, t2, v2))))

  (** val map_r_to_edge2 :
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.var * Coq_vpg.alt)
      ->
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      option **)

  let map_r_to_edge2 = function
  | (l, alt0) ->
    (match alt0 with
     | Coq_vpg.Alt_Epsilon -> None
     | Coq_vpg.Alt_Linear (t0, v) ->
       (match t0 with
        | Coq_vpg.Call a ->
          Some
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndCalE
            (l, a, v)))
        | Coq_vpg.Plain c0 ->
          Some
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PlnE
            (l, c0, v)))
        | Coq_vpg.Ret b ->
          Some
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
            (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PndRetE
            (l, b, v))))
     | Coq_vpg.Alt_Match (t1, t2, v1, v2) ->
       Some
         (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
         (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.MatRetE
         (l, t1, v1, t2, v2))))

  (** val map_P_to_edge :
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      option list **)

  let map_P_to_edge =
    app
      (map map_r_to_edge1
        TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_P)
      (map map_r_to_edge2
        TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_P)

  (** val m_to_PE :
      TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_ME
      ->
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      option * TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.coq_VE
      option) list **)

  let m_to_PE = function
  | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.CalCME m1 ->
    map (fun e ->
      let (y, e0) = e in
      (match y with
       | Some r ->
         ((Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
           r)), (Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
           e0)))
       | None ->
         (None, (Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
           e0)))))
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_va_set.elements
        m1)
  | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.PlnCME m1 ->
    map (fun e ->
      let (y, e0) = e in
      (match y with
       | Some r ->
         ((Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
           r)), (Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
           e0)))
       | None ->
         (None, (Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Plnv
           e0)))))
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vc_set.elements
        m1)
  | TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.RetCME m1 ->
    map (fun e ->
      let (y, e0) = e in
      (match y with
       | Some r ->
         ((Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Calv
           r)), (Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
           e0)))
       | None ->
         (None, (Some
           (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Retv
           e0)))))
      (TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup.Transducer.TimedSets.Parser.Coq_vb_set.elements
        m1)
 end
