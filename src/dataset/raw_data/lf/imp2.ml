
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type 'a option =
| Some of 'a
| None

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> m)
      (fun p -> (fun x -> x + 1) (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> n)
      (fun k ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val eqb : int -> int -> bool **)

  let rec eqb n m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n

  (** val leb : int -> int -> bool **)

  let rec leb n m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  if if if if if if if eqb a0 b0 then eqb a1 b1 else false
                 then eqb a2 b2
                 else false
              then eqb a3 b3
              else false
           then eqb a4 b4
           else false
        then eqb a5 b5
        else false
     then eqb a6 b6
     else false
  then eqb a7 b7
  else false

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> true
     | String (_, _) -> false)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> false
     | String (c2, s2') -> if eqb0 c1 c2 then eqb1 s1' s2' else false)

type 'a total_map = string -> 'a

(** val t_update : 'a1 total_map -> string -> 'a1 -> string -> 'a1 **)

let t_update m x v x' =
  if eqb1 x x' then v else m x'

type state = int total_map

type aexp =
| ANum of int
| AId of string
| APlus of aexp * aexp
| AMinus of aexp * aexp
| AMult of aexp * aexp

type bexp =
| BTrue
| BFalse
| BEq of aexp * aexp
| BNeq of aexp * aexp
| BLe of aexp * aexp
| BGt of aexp * aexp
| BNot of bexp
| BAnd of bexp * bexp

(** val aeval : state -> aexp -> int **)

let rec aeval st = function
| ANum n -> n
| AId x -> st x
| APlus (a1, a2) -> Nat.add (aeval st a1) (aeval st a2)
| AMinus (a1, a2) -> Nat.sub (aeval st a1) (aeval st a2)
| AMult (a1, a2) -> Nat.mul (aeval st a1) (aeval st a2)

(** val beval : state -> bexp -> bool **)

let rec beval st = function
| BTrue -> true
| BFalse -> false
| BEq (a1, a2) -> Nat.eqb (aeval st a1) (aeval st a2)
| BNeq (a1, a2) -> negb (Nat.eqb (aeval st a1) (aeval st a2))
| BLe (a1, a2) -> Nat.leb (aeval st a1) (aeval st a2)
| BGt (a1, a2) -> negb (Nat.leb (aeval st a1) (aeval st a2))
| BNot b1 -> negb (beval st b1)
| BAnd (b1, b2) -> if beval st b1 then beval st b2 else false

type com =
| CSkip
| CAsgn of string * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

(** val ceval_step : state -> com -> int -> state option **)

let rec ceval_step st c i =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> None)
    (fun i' ->
    match c with
    | CSkip -> Some st
    | CAsgn (l, a1) -> Some (t_update st l (aeval st a1))
    | CSeq (c1, c2) ->
      (match ceval_step st c1 i' with
       | Some st' -> ceval_step st' c2 i'
       | None -> None)
    | CIf (b, c1, c2) ->
      if beval st b then ceval_step st c1 i' else ceval_step st c2 i'
    | CWhile (b1, c1) ->
      if beval st b1
      then (match ceval_step st c1 i' with
            | Some st' -> ceval_step st' c i'
            | None -> None)
      else Some st)
    i
