
type key = int

type 'v tree =
| E
| T of 'v tree * key * 'v * 'v tree

(** val empty_tree : 'a1 tree **)

let empty_tree =
  E

(** val lookup : 'a1 -> key -> 'a1 tree -> 'a1 **)

let rec lookup default x = function
| E -> default
| T (l, k, v, r) ->
  if ( < ) x k
  then lookup default x l
  else if ( < ) k x then lookup default x r else v

(** val insert : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let rec insert x v = function
| E -> T (E, x, v, E)
| T (l, y, v', r) ->
  if ( < ) x y
  then T ((insert x v l), y, v', r)
  else if ( < ) y x then T (l, y, v', (insert x v r)) else T (l, x, v, r)

(** val elements_aux : 'a1 tree -> (key * 'a1) list -> (key * 'a1) list **)

let rec elements_aux t acc =
  match t with
  | E -> acc
  | T (l, k, v, r) -> elements_aux l ((k , v)::(elements_aux r acc))

(** val elements : 'a1 tree -> (key * 'a1) list **)

let elements t =
  elements_aux t []
