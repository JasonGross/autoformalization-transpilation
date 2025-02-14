
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : int -> int -> int **)

let rec add = ( + )

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> n0)
    (fun k ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> n0)
      (fun l -> sub k l)
      m)
    n0

(** val eqb : int -> int -> bool **)

let rec eqb = ( = )

(** val leb : int -> int -> bool **)

let rec leb n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> true)
    (fun n' ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m)
    n0

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n0 m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> m)
      (fun p -> (fun x -> x + 1) (add p m))
      n0

  (** val mul : int -> int -> int **)

  let rec mul n0 m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n0

  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val eqb : int -> int -> bool **)

  let rec eqb n0 m =
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
      n0

  (** val leb : int -> int -> bool **)

  let rec leb n0 m =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n0
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op add x ((fun x -> x + 1) 0)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val to_nat : n -> int **)

  let to_nat = function
  | N0 -> 0
  | Npos p -> Pos.to_nat p
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b :: l' ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

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

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

type 'a total_map = char list -> 'a

(** val t_empty : 'a1 -> 'a1 total_map **)

let t_empty v _ =
  v

(** val t_update : 'a1 total_map -> char list -> 'a1 -> char list -> 'a1 **)

let t_update m x v x' =
  if eqb0 x x' then v else m x'

type state = int total_map

type aexp =
| ANum of int
| AId of char list
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
| ANum n0 -> n0
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
| BAnd (b1, b2) -> (&&) (beval st b1) (beval st b2)

(** val empty_st : int total_map **)

let empty_st =
  t_empty 0

type com =
| CSkip
| CAsgn of char list * aexp
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

(** val isWhite : char -> bool **)

let isWhite c =
  let n0 = nat_of_ascii c in
  (||)
    ((||)
      (eqb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) 0)))))))))))))))))))))))))))))))))
      (eqb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) 0)))))))))))
    ((||)
      (eqb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))
      (eqb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))

(** val isLowerAlpha : char -> bool **)

let isLowerAlpha c =
  let n0 = nat_of_ascii c in
  (&&)
    (leb ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      n0)
    (leb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val isAlpha : char -> bool **)

let isAlpha c =
  let n0 = nat_of_ascii c in
  (||)
    ((&&)
      (leb ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1)
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) n0)
      (leb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((&&)
      (leb ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1)
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        n0)
      (leb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1)
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val isDigit : char -> bool **)

let isDigit c =
  let n0 = nat_of_ascii c in
  (&&)
    (leb ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) 0)))))))))))))))))))))))))))))))))))))))))))))))) n0)
    (leb n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type chartype =
| White
| Alpha
| Digit
| Other

(** val classifyChar : char -> chartype **)

let classifyChar c =
  if isWhite c
  then White
  else if isAlpha c then Alpha else if isDigit c then Digit else Other

(** val list_of_string : char list -> char list **)

let rec list_of_string = function
| [] -> []
| c::s0 -> c :: (list_of_string s0)

(** val string_of_list : char list -> char list **)

let string_of_list xs =
  fold_right (fun x x0 -> x::x0) [] xs

type token = char list

(** val tokenize_helper :
    chartype -> char list -> char list -> char list list **)

let rec tokenize_helper cls acc xs =
  let tk = match acc with
           | [] -> []
           | _ :: _ -> (rev acc) :: [] in
  (match xs with
   | [] -> tk
   | x :: xs' ->
     (match cls with
      | White ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x
         | x0 ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper x0 (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x0 (x :: [])
                                               xs')
                            else app tk (tokenize_helper x0 (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper x0 (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x0 (x :: [])
                                               xs')
                            else app tk (tokenize_helper x0 (x :: []) xs'))
             x)
      | Alpha ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x
         | Alpha ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Alpha (x :: acc) xs'
                  else if b1
                       then tokenize_helper Alpha (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Alpha (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Alpha
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Alpha
                                                       (x :: acc) xs'
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Alpha (x :: acc)
                                             xs'
                            else tokenize_helper Alpha (x :: acc) xs'
             else if b0
                  then tokenize_helper Alpha (x :: acc) xs'
                  else if b1
                       then tokenize_helper Alpha (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Alpha (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Alpha
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Alpha
                                                       (x :: acc) xs'
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Alpha (x :: acc)
                                             xs'
                            else tokenize_helper Alpha (x :: acc) xs')
             x
         | Digit ->
           let tp = Digit in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x)
      | Digit ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x
         | Alpha ->
           let tp = Alpha in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x
         | Digit ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Digit (x :: acc) xs'
                  else if b1
                       then tokenize_helper Digit (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Digit (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Digit
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Digit
                                                       (x :: acc) xs'
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Digit (x :: acc)
                                             xs'
                            else tokenize_helper Digit (x :: acc) xs'
             else if b0
                  then tokenize_helper Digit (x :: acc) xs'
                  else if b1
                       then tokenize_helper Digit (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Digit (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Digit
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Digit
                                                       (x :: acc) xs'
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Digit (x :: acc)
                                             xs'
                            else tokenize_helper Digit (x :: acc) xs')
             x
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper tp (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper tp (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper tp (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x :: []) xs'))
             x)
      | Other ->
        (match classifyChar x with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b0
                  then app tk (tokenize_helper White [] xs')
                  else if b1
                       then app tk (tokenize_helper White [] xs')
                       else if b2
                            then if b3
                                 then app tk (tokenize_helper White [] xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x
         | Other ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then tokenize_helper Other (x :: acc) xs'
                  else if b1
                       then tokenize_helper Other (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Other (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Other
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Other
                                                       (x :: acc) xs'
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Other (x :: acc)
                                             xs'
                            else tokenize_helper Other (x :: acc) xs'
             else if b0
                  then tokenize_helper Other (x :: acc) xs'
                  else if b1
                       then tokenize_helper Other (x :: acc) xs'
                       else if b2
                            then if b3
                                 then tokenize_helper Other (x :: acc) xs'
                                 else if b4
                                      then if b5
                                           then tokenize_helper Other
                                                  (x :: acc) xs'
                                           else if b6
                                                then tokenize_helper Other
                                                       (x :: acc) xs'
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Other (x :: acc)
                                             xs'
                            else tokenize_helper Other (x :: acc) xs')
             x
         | x0 ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then if b0
                  then app tk (tokenize_helper x0 (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (x :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x0 (x :: [])
                                               xs')
                            else app tk (tokenize_helper x0 (x :: []) xs')
             else if b0
                  then app tk (tokenize_helper x0 (x :: []) xs')
                  else if b1
                       then app tk (tokenize_helper x0 (x :: []) xs')
                       else if b2
                            then if b3
                                 then app tk
                                        (tokenize_helper x0 (x :: []) xs')
                                 else if b4
                                      then if b5
                                           then app tk
                                                  (tokenize_helper x0
                                                    (x :: []) xs')
                                           else if b6
                                                then app tk
                                                       (tokenize_helper x0
                                                         (x :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x0 (x :: [])
                                               xs')
                            else app tk (tokenize_helper x0 (x :: []) xs'))
             x)))

(** val tokenize : char list -> char list list **)

let tokenize s =
  map string_of_list (tokenize_helper White [] (list_of_string s))

type 'x optionE =
| SomeE of 'x
| NoneE of char list

type 't parser0 = token list -> ('t * token list) optionE

(** val many_helper :
    'a1 parser0 -> 'a1 list -> int -> token list -> ('a1 list * token list)
    optionE **)

let rec many_helper p acc steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match p xs with
    | SomeE x -> let (t, xs') = x in many_helper p (t :: acc) steps' xs'
    | NoneE _ -> SomeE ((rev acc), xs))
    steps

(** val many : 'a1 parser0 -> int -> 'a1 list parser0 **)

let many p steps =
  many_helper p [] steps

(** val firstExpect : token -> 'a1 parser0 -> 'a1 parser0 **)

let firstExpect t p = function
| [] ->
  NoneE
    (append
      ('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('\''::[]))))))))))
      (append t ('\''::('.'::[]))))
| x :: xs' ->
  if string_dec x t
  then p xs'
  else NoneE
         (append
           ('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('\''::[]))))))))))
           (append t ('\''::('.'::[]))))

(** val expect : token -> unit parser0 **)

let expect t =
  firstExpect t (fun xs -> SomeE ((), xs))

(** val parseIdentifier : token list -> (char list * token list) optionE **)

let parseIdentifier = function
| [] ->
  NoneE
    ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('i'::('d'::('e'::('n'::('t'::('i'::('f'::('i'::('e'::('r'::[])))))))))))))))))))
| x :: xs' ->
  if forallb isLowerAlpha (list_of_string x)
  then SomeE (x, xs')
  else NoneE
         (append
           ('I'::('l'::('l'::('e'::('g'::('a'::('l'::(' '::('i'::('d'::('e'::('n'::('t'::('i'::('f'::('i'::('e'::('r'::(':'::('\''::[]))))))))))))))))))))
           (append x ('\''::[])))

(** val parseNumber : token list -> (int * token list) optionE **)

let parseNumber = function
| [] ->
  NoneE
    ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::[])))))))))))))))
| x :: xs' ->
  if forallb isDigit (list_of_string x)
  then SomeE
         ((fold_left (fun n0 d ->
            add
              (mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) 0)))))))))) n0)
              (sub (nat_of_ascii d) (nat_of_ascii '0')))
            (list_of_string x) 0),
         xs')
  else NoneE
         ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::[])))))))))))))))

(** val parsePrimaryExp : int -> token list -> (aexp * token list) optionE **)

let rec parsePrimaryExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    let result =
      match parseIdentifier xs with
      | SomeE x -> let (i, rest) = x in SomeE ((AId i), rest)
      | NoneE err -> NoneE err
    in
    (match result with
     | SomeE _ -> result
     | NoneE _ ->
       let result0 =
         match parseNumber xs with
         | SomeE x -> let (n0, rest) = x in SomeE ((ANum n0), rest)
         | NoneE err -> NoneE err
       in
       (match result0 with
        | SomeE _ -> result0
        | NoneE _ ->
          (match firstExpect ('('::[]) (parseSumExp steps') xs with
           | SomeE x ->
             let (e, rest) = x in
             (match expect (')'::[]) rest with
              | SomeE x0 -> let (_, rest') = x0 in SomeE (e, rest')
              | NoneE err -> NoneE err)
           | NoneE err -> NoneE err))))
    steps

(** val parseProductExp : int -> token list -> (aexp * token list) optionE **)

and parseProductExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parsePrimaryExp steps' xs with
    | SomeE x ->
      let (e, rest) = x in
      (match many (firstExpect ('*'::[]) (parsePrimaryExp steps')) steps' rest with
       | SomeE x0 ->
         let (es, rest') = x0 in
         SomeE ((fold_left (fun x1 x2 -> AMult (x1, x2)) es e), rest')
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseSumExp : int -> token list -> (aexp * token list) optionE **)

and parseSumExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parseProductExp steps' xs with
    | SomeE x ->
      let (e, rest) = x in
      (match many (fun xs0 ->
               let result =
                 match firstExpect ('+'::[]) (parseProductExp steps') xs0 with
                 | SomeE x0 ->
                   let (e0, rest') = x0 in SomeE ((true, e0), rest')
                 | NoneE err -> NoneE err
               in
               (match result with
                | SomeE _ -> result
                | NoneE _ ->
                  (match firstExpect ('-'::[]) (parseProductExp steps') xs0 with
                   | SomeE x0 ->
                     let (e0, rest') = x0 in SomeE ((false, e0), rest')
                   | NoneE err -> NoneE err)))
               steps' rest with
       | SomeE x0 ->
         let (es, rest') = x0 in
         SomeE
         ((fold_left (fun e0 term ->
            let (y, e1) = term in
            if y then APlus (e0, e1) else AMinus (e0, e1)) es e),
         rest')
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseAExp : int -> token list -> (aexp * token list) optionE **)

let parseAExp =
  parseSumExp

(** val parseAtomicExp : int -> token list -> (bexp * token list) optionE **)

let rec parseAtomicExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    let result =
      match expect ('t'::('r'::('u'::('e'::[])))) xs with
      | SomeE x -> let (_, rest) = x in SomeE (BTrue, rest)
      | NoneE err -> NoneE err
    in
    (match result with
     | SomeE _ -> result
     | NoneE _ ->
       let result0 =
         match expect ('f'::('a'::('l'::('s'::('e'::[]))))) xs with
         | SomeE x -> let (_, rest) = x in SomeE (BFalse, rest)
         | NoneE err -> NoneE err
       in
       (match result0 with
        | SomeE _ -> result0
        | NoneE _ ->
          let result1 =
            match firstExpect ('~'::[]) (parseAtomicExp steps') xs with
            | SomeE x -> let (e, rest) = x in SomeE ((BNot e), rest)
            | NoneE err -> NoneE err
          in
          (match result1 with
           | SomeE _ -> result1
           | NoneE _ ->
             let result2 =
               match firstExpect ('('::[]) (parseConjunctionExp steps') xs with
               | SomeE x ->
                 let (e, rest) = x in
                 (match expect (')'::[]) rest with
                  | SomeE x0 -> let (_, rest') = x0 in SomeE (e, rest')
                  | NoneE err -> NoneE err)
               | NoneE err -> NoneE err
             in
             (match result2 with
              | SomeE _ -> result2
              | NoneE _ ->
                (match parseProductExp steps' xs with
                 | SomeE x ->
                   let (e, rest) = x in
                   let result3 =
                     match firstExpect ('='::[]) (parseAExp steps') rest with
                     | SomeE x0 ->
                       let (e', rest') = x0 in SomeE ((BEq (e, e')), rest')
                     | NoneE err -> NoneE err
                   in
                   (match result3 with
                    | SomeE _ -> result3
                    | NoneE _ ->
                      let result4 =
                        match firstExpect ('<'::('='::[])) (parseAExp steps')
                                rest with
                        | SomeE x0 ->
                          let (e', rest') = x0 in SomeE ((BLe (e, e')), rest')
                        | NoneE err -> NoneE err
                      in
                      (match result4 with
                       | SomeE _ -> result4
                       | NoneE _ ->
                         NoneE
                           ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('\''::('='::('\''::(' '::('o'::('r'::(' '::('\''::('<'::('='::('\''::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('a'::('r'::('i'::('t'::('h'::('m'::('e'::('t'::('i'::('c'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))))))))
                 | NoneE err -> NoneE err))))))
    steps

(** val parseConjunctionExp :
    int -> token list -> (bexp * token list) optionE **)

and parseConjunctionExp steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parseAtomicExp steps' xs with
    | SomeE x ->
      let (e, rest) = x in
      (match many (firstExpect ('&'::('&'::[])) (parseAtomicExp steps'))
               steps' rest with
       | SomeE x0 ->
         let (es, rest') = x0 in
         SomeE ((fold_left (fun x1 x2 -> BAnd (x1, x2)) es e), rest')
       | NoneE err -> NoneE err)
    | NoneE err -> NoneE err)
    steps

(** val parseBExp : int -> token list -> (bexp * token list) optionE **)

let parseBExp =
  parseConjunctionExp

(** val parseSimpleCommand :
    int -> token list -> (com * token list) optionE **)

let rec parseSimpleCommand steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    let result =
      match expect ('s'::('k'::('i'::('p'::[])))) xs with
      | SomeE x -> let (_, rest) = x in SomeE (CSkip, rest)
      | NoneE err -> NoneE err
    in
    (match result with
     | SomeE _ -> result
     | NoneE _ ->
       let result0 =
         match firstExpect ('i'::('f'::[])) (parseBExp steps') xs with
         | SomeE x ->
           let (e, rest) = x in
           (match firstExpect ('t'::('h'::('e'::('n'::[]))))
                    (parseSequencedCommand steps') rest with
            | SomeE x0 ->
              let (c, rest') = x0 in
              (match firstExpect ('e'::('l'::('s'::('e'::[]))))
                       (parseSequencedCommand steps') rest' with
               | SomeE x1 ->
                 let (c', rest'') = x1 in
                 (match expect ('e'::('n'::('d'::[]))) rest'' with
                  | SomeE x2 ->
                    let (_, rest''') = x2 in SomeE ((CIf (e, c, c')), rest''')
                  | NoneE err -> NoneE err)
               | NoneE err -> NoneE err)
            | NoneE err -> NoneE err)
         | NoneE err -> NoneE err
       in
       (match result0 with
        | SomeE _ -> result0
        | NoneE _ ->
          let result1 =
            match firstExpect ('w'::('h'::('i'::('l'::('e'::[])))))
                    (parseBExp steps') xs with
            | SomeE x ->
              let (e, rest) = x in
              (match firstExpect ('d'::('o'::[]))
                       (parseSequencedCommand steps') rest with
               | SomeE x0 ->
                 let (c, rest') = x0 in
                 (match expect ('e'::('n'::('d'::[]))) rest' with
                  | SomeE x1 ->
                    let (_, rest'') = x1 in SomeE ((CWhile (e, c)), rest'')
                  | NoneE err -> NoneE err)
               | NoneE err -> NoneE err)
            | NoneE err -> NoneE err
          in
          (match result1 with
           | SomeE _ -> result1
           | NoneE _ ->
             let result2 =
               match parseIdentifier xs with
               | SomeE x ->
                 let (i, rest) = x in
                 (match firstExpect (':'::('='::[])) (parseAExp steps') rest with
                  | SomeE x0 ->
                    let (e, rest') = x0 in SomeE ((CAsgn (i, e)), rest')
                  | NoneE err -> NoneE err)
               | NoneE err -> NoneE err
             in
             (match result2 with
              | SomeE _ -> result2
              | NoneE _ ->
                NoneE
                  ('E'::('x'::('p'::('e'::('c'::('t'::('i'::('n'::('g'::(' '::('a'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::[]))))))))))))))))))))))))
    steps

(** val parseSequencedCommand :
    int -> token list -> (com * token list) optionE **)

and parseSequencedCommand steps xs =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> NoneE
    ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('v'::('e'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))))))))))))))))))
    (fun steps' ->
    match parseSimpleCommand steps' xs with
    | SomeE x ->
      let (c, rest) = x in
      let result =
        match firstExpect (';'::[]) (parseSequencedCommand steps') rest with
        | SomeE x0 -> let (c', rest') = x0 in SomeE ((CSeq (c, c')), rest')
        | NoneE err -> NoneE err
      in
      (match result with
       | SomeE _ -> result
       | NoneE _ -> SomeE (c, rest))
    | NoneE err -> NoneE err)
    steps

(** val bignumber : int **)

let bignumber =
  (fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val parse : char list -> com optionE **)

let parse str =
  let tokens = tokenize str in
  (match parseSequencedCommand bignumber tokens with
   | SomeE x ->
     let (c, l) = x in
     (match l with
      | [] -> SomeE c
      | t :: _ ->
        NoneE
          (append
            ('T'::('r'::('a'::('i'::('l'::('i'::('n'::('g'::(' '::('t'::('o'::('k'::('e'::('n'::('s'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::('i'::('n'::('g'::(':'::(' '::[])))))))))))))))))))))))))))
            t))
   | NoneE err -> NoneE err)
