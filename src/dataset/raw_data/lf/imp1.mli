
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool
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

type state = nat total_map

type aexp =
| ANum of nat
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

val aeval : state -> aexp -> nat

val beval : state -> bexp -> bool

type com =
| CSkip
| CAsgn of string * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

val ceval_step : state -> com -> nat -> state option
