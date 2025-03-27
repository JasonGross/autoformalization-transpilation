
type key = int

type color =
| Red
| Black

type 'v tree =
| E
| T of color * 'v tree * key * 'v * 'v tree

val empty_tree : 'a1 tree

val lookup : 'a1 -> key -> 'a1 tree -> 'a1

val balance : color -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

val ins : key -> 'a1 -> 'a1 tree -> 'a1 tree

val make_black : 'a1 tree -> 'a1 tree

val insert : key -> 'a1 -> 'a1 tree -> 'a1 tree

val elements_aux : 'a1 tree -> (key * 'a1) list -> (key * 'a1) list

val elements : 'a1 tree -> (key * 'a1) list
