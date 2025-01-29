From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require Import Arith.

From Coq Require Import Init.Nat.

From Coq Require Import EqNat.

From LF Require Import ImpCEvalFun.

Extraction "imp1.ml" ceval_step.

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".

Extraction "imp2.ml" ceval_step.

Require Import ExtrOcamlBasic.

Require Import ExtrOcamlString.

Extract Inductive sumbool => "bool" ["true" "false"].

From LF Require Import Imp.

From LF Require Import ImpParser.

From LF Require Import Maps.
Extraction "imp.ml" empty_st ceval_step parse.

