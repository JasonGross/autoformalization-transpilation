
val negb : bool -> bool

type 'a option =
| Some of 'a
| None

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val eqb : int -> int -> bool

  val leb : int -> int -> bool
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

type 'a total_map = string -> 'a

val t_update : 'a1 total_map -> string -> 'a1 -> string -> 'a1

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

val aeval : state -> aexp -> int

val beval : state -> bexp -> bool

type com =
| CSkip
| CAsgn of string * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

val ceval_step : state -> com -> int -> state option
