(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-R" "src" "Flocq" "-top" "Everything") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 40 lines to 48 lines, then from 52 lines to 1298 lines, then from 1251 lines to 1222 lines, then from 1226 lines to 5796 lines, then from 5800 lines to 6609 lines, then from 6613 lines to 7513 lines, then from 7517 lines to 7559 lines, then from 7563 lines to 10125 lines, then from 10098 lines to 10024 lines, then from 10028 lines to 10883 lines, then from 10865 lines to 10827 lines, then from 10831 lines to 11025 lines, then from 11030 lines to 10998 lines, then from 11002 lines to 11387 lines, then from 11392 lines to 11365 lines, then from 11369 lines to 11998 lines, then from 12003 lines to 11981 lines, then from 11985 lines to 12572 lines, then from 12577 lines to 12544 lines, then from 12549 lines to 13327 lines, then from 13333 lines to 13312 lines, then from 13317 lines to 14797 lines, then from 14803 lines to 14764 lines, then from 14769 lines to 18629 lines, then from 18635 lines to 19124 lines, then from 19129 lines to 20136 lines, then from 20141 lines to 20214 lines, then from 20219 lines to 20582 lines, then from 20587 lines to 20571 lines, then from 20576 lines to 20796 lines, then from 20802 lines to 20770 lines, then from 20775 lines to 20972 lines, then from 20978 lines to 20959 lines, then from 20964 lines to 22175 lines, then from 22181 lines to 22160 lines, then from 22165 lines to 22206 lines, then from 22212 lines to 22190 lines, then from 22195 lines to 22749 lines, then from 22755 lines to 22763 lines, then from 22768 lines to 23154 lines, then from 23159 lines to 23144 lines, then from 23149 lines to 23272 lines, then from 23278 lines to 23261 lines, then from 23266 lines to 23825 lines, then from 23831 lines to 23826 lines, then from 23831 lines to 26501 lines, then from 26493 lines to 26518 lines, then from 26523 lines to 26703 lines, then from 26709 lines to 26691 lines, then from 26696 lines to 26874 lines, then from 26880 lines to 26857 lines, then from 26862 lines to 29288 lines, then from 29290 lines to 29317 lines, then from 29322 lines to 31014 lines, then from 31017 lines to 30999 lines, then from 31004 lines to 31708 lines, then from 31714 lines to 31687 lines, then from 31692 lines to 32251 lines, then from 32256 lines to 32246 lines, then from 32251 lines to 33414 lines, then from 33420 lines to 33390 lines, then from 33395 lines to 33479 lines, then from 33485 lines to 33457 lines, then from 33462 lines to 35900 lines, then from 35901 lines to 35992 lines, then from 35997 lines to 37012 lines, then from 37018 lines to 37017 lines, then from 37023 lines to 37019 lines *)
(* coqc version 9.1+alpha compiled with OCaml 4.14.2
   coqtop version 9.1+alpha
   Modules that could not be inlined: Flocq.Pff.Pff
   Expected coqc runtime on this file: 11.995 sec *)

Require Stdlib.ZArith.ZArith.
Require Stdlib.Reals.Reals.
Require Stdlib.micromega.Lia.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.ZArith.Zquot.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.

Module Export Flocq_DOT_Core_DOT_Zaux.
Module Export Flocq.
Module Export Core.
Module Export Zaux.

Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.ZArith.Zquot.

Notation cond_Zopp := SpecFloat.cond_Zopp (only parsing).
Notation iter_pos := SpecFloat.iter_pos (only parsing).

Section Zmissing.

Theorem Zopp_le_cancel :
  forall x y : Z,
  (-y <= -x)%Z -> Z.le x y.
Proof.
intros x y Hxy.
apply Zplus_le_reg_r with (-x - y)%Z.
now ring_simplify.
Qed.

Theorem Zgt_not_eq :
  forall x y : Z,
  (y < x)%Z -> (x <> y)%Z.
Proof.
intros x y H Hn.
apply Z.lt_irrefl with x.
now rewrite Hn at 1.
Qed.

End Zmissing.

Section Proof_Irrelevance.

Scheme eq_dep_elim := Induction for eq Sort Type.

Definition eqbool_dep P (h1 : P true) b :=
  match b return P b -> Prop with
  | true => fun (h2 : P true) => h1 = h2
  | false => fun (h2 : P false) => False
  end.

Lemma eqbool_irrelevance : forall (b : bool) (h1 h2 : b = true), h1 = h2.
Proof.
assert (forall (h : true = true), refl_equal true = h).
apply (eq_dep_elim bool true (eqbool_dep _ _) (refl_equal _)).
intros b.
case b.
intros h1 h2.
now rewrite <- (H h1).
intros h.
discriminate h.
Qed.

End Proof_Irrelevance.

Section Even_Odd.

Theorem Zeven_ex :
  forall x, exists p, x = (2 * p + if Z.even x then 0 else 1)%Z.
Proof.
intros [|[n|n|]|[n|n|]].
now exists Z0.
now exists (Zpos n).
now exists (Zpos n).
now exists Z0.
exists (Zneg n - 1)%Z.
change (2 * Zneg n - 1 = 2 * (Zneg n - 1) + 1)%Z.
ring.
now exists (Zneg n).
now exists (-1)%Z.
Qed.

End Even_Odd.

Section Zpower.

Theorem Zpower_plus :
  forall n k1 k2, (0 <= k1)%Z -> (0 <= k2)%Z ->
  Zpower n (k1 + k2) = (Zpower n k1 * Zpower n k2)%Z.
Proof.
intros n k1 k2 H1 H2.
now apply Zpower_exp ; apply Z.le_ge.
Qed.

Theorem Zpower_Zpower_nat :
  forall b e, (0 <= e)%Z ->
  Zpower b e = Zpower_nat b (Z.abs_nat e).
Proof.
intros b [|e|e] He.
apply refl_equal.
apply Zpower_pos_nat.
elim He.
apply refl_equal.
Qed.

Theorem Zpower_nat_S :
  forall b e,
  Zpower_nat b (S e) = (b * Zpower_nat b e)%Z.
Proof.
intros b e.
rewrite (Zpower_nat_is_exp 1 e).
apply (f_equal (fun x => x * _)%Z).
apply Zmult_1_r.
Qed.

Theorem Zpower_pos_gt_0 :
  forall b p, (0 < b)%Z ->
  (0 < Zpower_pos b p)%Z.
Proof.
intros b p Hb.
rewrite Zpower_pos_nat.
induction (nat_of_P p).
easy.
rewrite Zpower_nat_S.
now apply Zmult_lt_0_compat.
Qed.

Theorem Zeven_Zpower_odd :
  forall b e, (0 <= e)%Z -> Z.even b = false ->
  Z.even (Zpower b e) = false.
Proof.
intros b e He Hb.
destruct (Z_le_lt_eq_dec _ _ He) as [He'|He'].
rewrite <- Hb.
now apply Z.even_pow.
now rewrite <- He'.
Qed.

Record radix := { radix_val :> Z ; radix_prop : Zle_bool 2 radix_val = true }.

Theorem radix_val_inj :
  forall r1 r2, radix_val r1 = radix_val r2 -> r1 = r2.
Proof.
intros (r1, H1) (r2, H2) H.
simpl in H.
revert H1.
rewrite H.
intros H1.
apply f_equal.
apply eqbool_irrelevance.
Qed.

Definition radix2 := Build_radix 2 (refl_equal _).

Variable r : radix.

Theorem radix_gt_0 : (0 < r)%Z.
Proof using .
apply Z.lt_le_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply r.
Qed.

Theorem radix_gt_1 : (1 < r)%Z.
Proof using .
destruct r as (v, Hr).
simpl.
apply Z.lt_le_trans with 2%Z.
easy.
now apply Zle_bool_imp_le.
Qed.

Theorem Zpower_gt_1 :
  forall p,
  (0 < p)%Z ->
  (1 < Zpower r p)%Z.
Proof using .
intros [|p|p] Hp ; try easy.
simpl.
rewrite Zpower_pos_nat.
generalize (lt_O_nat_of_P p).
induction (nat_of_P p).
easy.
intros _.
rewrite Zpower_nat_S.
assert (0 < Zpower_nat r n)%Z.
clear.
induction n.
easy.
rewrite Zpower_nat_S.
apply Zmult_lt_0_compat with (2 := IHn).
apply radix_gt_0.
apply Z.le_lt_trans with (1 * Zpower_nat r n)%Z.
rewrite Zmult_1_l.
now apply (Zlt_le_succ 0).
apply Zmult_lt_compat_r with (1 := H).
apply radix_gt_1.
Qed.

Theorem Zpower_gt_0 :
  forall p,
  (0 <= p)%Z ->
  (0 < Zpower r p)%Z.
Proof using .
intros p Hp.
rewrite Zpower_Zpower_nat with (1 := Hp).
induction (Z.abs_nat p).
easy.
rewrite Zpower_nat_S.
apply Zmult_lt_0_compat with (2 := IHn).
apply radix_gt_0.
Qed.

Theorem Zpower_ge_0 :
  forall e,
  (0 <= Zpower r e)%Z.
Proof using .
intros [|e|e] ; try easy.
apply Zlt_le_weak.
now apply Zpower_gt_0.
Qed.

Theorem Zpower_le :
  forall e1 e2, (e1 <= e2)%Z ->
  (Zpower r e1 <= Zpower r e2)%Z.
Proof using .
intros e1 e2 He.
destruct (Zle_or_lt 0 e1)%Z as [H1|H1].
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite Zpower_plus with (2 := H1).
rewrite <- (Zmult_1_l (r ^ e1)) at 1.
apply Zmult_le_compat_r.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zpower_ge_0.
now apply Zle_minus_le_0.
clear He.
destruct e1 as [|e1|e1] ; try easy.
apply Zpower_ge_0.
Qed.

Theorem Zpower_lt :
  forall e1 e2, (0 <= e2)%Z -> (e1 < e2)%Z ->
  (Zpower r e1 < Zpower r e2)%Z.
Proof using .
intros e1 e2 He2 He.
destruct (Zle_or_lt 0 e1)%Z as [H1|H1].
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite Zpower_plus with (2 := H1).
rewrite Zmult_comm.
rewrite <- (Zmult_1_r (r ^ e1)) at 1.
apply Zmult_lt_compat2.
split.
now apply Zpower_gt_0.
apply Z.le_refl.
split.
easy.
apply Zpower_gt_1.
clear -He ; lia.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
revert H1.
clear -He2.
destruct e1 ; try easy.
intros _.
now apply Zpower_gt_0.
Qed.

Theorem Zpower_lt_Zpower :
  forall e1 e2,
  (Zpower r (e1 - 1) < Zpower r e2)%Z ->
  (e1 <= e2)%Z.
Proof using .
intros e1 e2 He.
apply Znot_gt_le.
intros H.
apply Zlt_not_le with (1 := He).
apply Zpower_le.
clear -H ; lia.
Qed.

Theorem Zpower_gt_id :
  forall n, (n < Zpower r n)%Z.
Proof using .
intros [|n|n] ; try easy.
simpl.
rewrite Zpower_pos_nat.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
induction (nat_of_P n).
easy.
rewrite inj_S.
change (Zpower_nat r (S n0)) with (r * Zpower_nat r n0)%Z.
unfold Z.succ.
apply Z.lt_le_trans with (r * (Z_of_nat n0 + 1))%Z.
clear.
apply Zlt_0_minus_lt.
replace (r * (Z_of_nat n0 + 1) - (Z_of_nat n0 + 1))%Z with ((r - 1) * (Z_of_nat n0 + 1))%Z by ring.
apply Zmult_lt_0_compat.
cut (2 <= r)%Z.
lia.
apply Zle_bool_imp_le.
apply r.
apply (Zle_lt_succ 0).
apply Zle_0_nat.
apply Zmult_le_compat_l.
now apply Zlt_le_succ.
apply Z.le_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply r.
Qed.

End Zpower.

Section Div_Mod.

Theorem Zmod_mod_mult :
  forall n a b, (0 < a)%Z -> (0 <= b)%Z ->
  Zmod (Zmod n (a * b)) b = Zmod n b.
Proof.
  intros n a b Ha Hb.
destruct (Zle_lt_or_eq _ _ Hb) as [H'b|H'b].
  -
 rewrite (Z.mul_comm a b), Z.rem_mul_r, Z.add_mod, Z.mul_mod, Z.mod_same,
      Z.mul_0_l, Z.mod_0_l, Z.add_0_r, !Z.mod_mod; lia.
  -
 subst.
now rewrite Z.mul_0_r, !Zmod_0_r.
Qed.

Theorem ZOmod_eq :
  forall a b,
  Z.rem a b = (a - Z.quot a b * b)%Z.
Proof.
intros a b.
rewrite (Z.quot_rem' a b) at 2.
ring.
Qed.

Theorem ZOmod_mod_mult :
  forall n a b,
  Z.rem (Z.rem n (a * b)) b = Z.rem n b.
Proof.
intros n a b.
assert (Z.rem n (a * b) = n + - (Z.quot n (a * b) * a) * b)%Z.
rewrite <- Zopp_mult_distr_l.
rewrite <- Zmult_assoc.
apply ZOmod_eq.
rewrite H.
apply Z_rem_plus.
rewrite <- H.
apply Zrem_sgn2.
Qed.

Theorem Zdiv_mod_mult :
  forall n a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Z.div (Zmod n (a * b)) a) = Zmod (Z.div n a) b.
Proof.
intros n a b Ha Hb.
destruct (Zle_lt_or_eq _ _ Ha) as [Ha'|<-].
-
 destruct (Zle_lt_or_eq _ _ Hb) as [Hb'|<-].
  +
 rewrite Z.rem_mul_r, Z.add_comm, Z.mul_comm, Z.div_add_l by lia.
    rewrite (Zdiv_small (Zmod n a)).
    apply Z.add_0_r.
    now apply Z.mod_pos_bound.
  +
 now rewrite Z.mul_0_r, !Zmod_0_r, ?Zdiv_0_l.
-
 now rewrite Z.mul_0_l, !Zdiv_0_r, Zmod_0_l.
Qed.

Theorem ZOdiv_mod_mult :
  forall n a b,
  (Z.quot (Z.rem n (a * b)) a) = Z.rem (Z.quot n a) b.
Proof.
intros n a b.
destruct (Z.eq_dec a 0) as [Za|Za].
rewrite Za.
now rewrite 2!Zquot_0_r, Zrem_0_l.
assert (Z.rem n (a * b) = n + - (Z.quot (Z.quot n a) b * b) * a)%Z.
rewrite (ZOmod_eq n (a * b)) at 1.
rewrite Zquot_Zquot.
ring.
rewrite H.
rewrite Z_quot_plus with (2 := Za).
apply sym_eq.
apply ZOmod_eq.
rewrite <- H.
apply Zrem_sgn2.
Qed.

Theorem ZOdiv_small_abs :
  forall a b,
  (Z.abs a < b)%Z -> Z.quot a b = Z0.
Proof.
intros a b Ha.
destruct (Zle_or_lt 0 a) as [H|H].
apply Z.quot_small.
split.
exact H.
now rewrite Z.abs_eq in Ha.
apply Z.opp_inj.
rewrite <- Zquot_opp_l, Z.opp_0.
apply Z.quot_small.
generalize (Zabs_non_eq a).
lia.
Qed.

Theorem ZOmod_small_abs :
  forall a b,
  (Z.abs a < b)%Z -> Z.rem a b = a.
Proof.
intros a b Ha.
destruct (Zle_or_lt 0 a) as [H|H].
apply Z.rem_small.
split.
exact H.
now rewrite Z.abs_eq in Ha.
apply Z.opp_inj.
rewrite <- Zrem_opp_l.
apply Z.rem_small.
generalize (Zabs_non_eq a).
lia.
Qed.

Theorem ZOdiv_plus :
  forall a b c, (0 <= a * b)%Z ->
  (Z.quot (a + b) c = Z.quot a c + Z.quot b c + Z.quot (Z.rem a c + Z.rem b c) c)%Z.
Proof.
intros a b c Hab.
destruct (Z.eq_dec c 0) as [Zc|Zc].
now rewrite Zc, 4!Zquot_0_r.
apply Zmult_reg_r with (1 := Zc).
rewrite 2!Zmult_plus_distr_l.
assert (forall d, Z.quot d c * c = d - Z.rem d c)%Z.
intros d.
rewrite ZOmod_eq.
ring.
rewrite 4!H.
rewrite <- Zplus_rem with (1 := Hab).
ring.
Qed.

End Div_Mod.

Section Same_sign.

Theorem Zsame_sign_trans :
  forall v u w, v <> Z0 ->
  (0 <= u * v)%Z -> (0 <= v * w)%Z -> (0 <= u * w)%Z.
Proof.
intros [|v|v] [|u|u] [|w|w] Zv Huv Hvw ; try easy ; now elim Zv.
Qed.

Theorem Zsame_sign_trans_weak :
  forall v u w, (v = Z0 -> w = Z0) ->
  (0 <= u * v)%Z -> (0 <= v * w)%Z -> (0 <= u * w)%Z.
Proof.
intros [|v|v] [|u|u] [|w|w] Zv Huv Hvw ; try easy ; now discriminate Zv.
Qed.

Theorem Zsame_sign_imp :
  forall u v,
  (0 < u -> 0 <= v)%Z ->
  (0 < -u -> 0 <= -v)%Z ->
  (0 <= u * v)%Z.
Proof.
intros [|u|u] v Hp Hn.
easy.
apply Zmult_le_0_compat.
easy.
now apply Hp.
replace (Zneg u * v)%Z with (Zpos u * (-v))%Z.
apply Zmult_le_0_compat.
easy.
now apply Hn.
rewrite <- Zopp_mult_distr_r.
apply Zopp_mult_distr_l.
Qed.

Theorem Zsame_sign_odiv :
  forall u v, (0 <= v)%Z ->
  (0 <= u * Z.quot u v)%Z.
Proof.
intros u v Hv.
apply Zsame_sign_imp ; intros Hu.
apply Z_quot_pos with (2 := Hv).
now apply Zlt_le_weak.
rewrite <- Zquot_opp_l.
apply Z_quot_pos with (2 := Hv).
now apply Zlt_le_weak.
Qed.

End Same_sign.

Section Zeq_bool.

Inductive Zeq_bool_prop (x y : Z) : bool -> Prop :=
  | Zeq_bool_true_ : x = y -> Zeq_bool_prop x y true
  | Zeq_bool_false_ : x <> y -> Zeq_bool_prop x y false.

Theorem Zeq_bool_spec :
  forall x y, Zeq_bool_prop x y (Zeq_bool x y).
Proof.
intros x y.
generalize (Zeq_is_eq_bool x y).
case (Zeq_bool x y) ; intros (H1, H2) ; constructor.
now apply H2.
intros H.
specialize (H1 H).
discriminate H1.
Qed.

Theorem Zeq_bool_true :
  forall x y, x = y -> Zeq_bool x y = true.
Proof.
intros x y.
apply -> Zeq_is_eq_bool.
Qed.

Theorem Zeq_bool_false :
  forall x y, x <> y -> Zeq_bool x y = false.
Proof.
intros x y.
generalize (proj2 (Zeq_is_eq_bool x y)).
case Zeq_bool.
intros He Hn.
elim Hn.
now apply He.
now intros _ _.
Qed.

Theorem Zeq_bool_diag :
  forall x, Zeq_bool x x = true.
Proof.
intros x.
now apply Zeq_bool_true.
Qed.

Theorem Zeq_bool_opp :
  forall x y,
  Zeq_bool (Z.opp x) y = Zeq_bool x (Z.opp y).
Proof.
intros x y.
case Zeq_bool_spec.
-
 intros <-.
  apply eq_sym, Zeq_bool_true.
  apply eq_sym, Z.opp_involutive.
-
 intros H.
  case Zeq_bool_spec.
  2: easy.
  intros ->.
  contradict H.
  apply Z.opp_involutive.
Qed.

Theorem Zeq_bool_opp' :
  forall x y,
  Zeq_bool (Z.opp x) (Z.opp y) = Zeq_bool x y.
Proof.
intros x y.
rewrite Zeq_bool_opp.
apply f_equal, Z.opp_involutive.
Qed.

End Zeq_bool.

Section Zle_bool.

Inductive Zle_bool_prop (x y : Z) : bool -> Prop :=
  | Zle_bool_true_ : (x <= y)%Z -> Zle_bool_prop x y true
  | Zle_bool_false_ : (y < x)%Z -> Zle_bool_prop x y false.

Theorem Zle_bool_spec :
  forall x y, Zle_bool_prop x y (Zle_bool x y).
Proof.
intros x y.
generalize (Zle_is_le_bool x y).
case Zle_bool ; intros (H1, H2) ; constructor.
now apply H2.
destruct (Zle_or_lt x y) as [H|H].
now specialize (H1 H).
exact H.
Qed.

Theorem Zle_bool_true :
  forall x y : Z,
  (x <= y)%Z -> Zle_bool x y = true.
Proof.
intros x y.
apply (proj1 (Zle_is_le_bool x y)).
Qed.

Theorem Zle_bool_false :
  forall x y : Z,
  (y < x)%Z -> Zle_bool x y = false.
Proof.
intros x y Hxy.
generalize (Zle_cases x y).
case Zle_bool ; intros H.
elim (Z.lt_irrefl x).
now apply Z.le_lt_trans with y.
apply refl_equal.
Qed.

Theorem Zle_bool_opp_l :
  forall x y,
  Zle_bool (Z.opp x) y = Zle_bool (Z.opp y) x.
Proof.
intros x y.
case Zle_bool_spec ; intros Hxy ;
  case Zle_bool_spec ; intros Hyx ; try easy ; lia.
Qed.

Theorem Zle_bool_opp :
  forall x y,
  Zle_bool (Z.opp x) (Z.opp y) = Zle_bool y x.
Proof.
intros x y.
now rewrite Zle_bool_opp_l, Z.opp_involutive.
Qed.

Theorem Zle_bool_opp_r :
  forall x y,
  Zle_bool x (Z.opp y) = Zle_bool y (Z.opp x).
Proof.
intros x y.
rewrite <- (Z.opp_involutive x) at 1.
apply Zle_bool_opp.
Qed.

End Zle_bool.

Section Zlt_bool.

Inductive Zlt_bool_prop (x y : Z) : bool -> Prop :=
  | Zlt_bool_true_ : (x < y)%Z -> Zlt_bool_prop x y true
  | Zlt_bool_false_ : (y <= x)%Z -> Zlt_bool_prop x y false.

Theorem Zlt_bool_spec :
  forall x y, Zlt_bool_prop x y (Zlt_bool x y).
Proof.
intros x y.
generalize (Zlt_is_lt_bool x y).
case Zlt_bool ; intros (H1, H2) ; constructor.
now apply H2.
destruct (Zle_or_lt y x) as [H|H].
exact H.
now specialize (H1 H).
Qed.

Theorem Zlt_bool_true :
  forall x y : Z,
  (x < y)%Z -> Zlt_bool x y = true.
Proof.
intros x y.
apply (proj1 (Zlt_is_lt_bool x y)).
Qed.

Theorem Zlt_bool_false :
  forall x y : Z,
  (y <= x)%Z -> Zlt_bool x y = false.
Proof.
intros x y Hxy.
generalize (Zlt_cases x y).
case Zlt_bool ; intros H.
elim (Z.lt_irrefl x).
now apply Z.lt_le_trans with y.
apply refl_equal.
Qed.

Theorem negb_Zle_bool :
  forall x y : Z,
  negb (Zle_bool x y) = Zlt_bool y x.
Proof.
intros x y.
case Zle_bool_spec ; intros H.
now rewrite Zlt_bool_false.
now rewrite Zlt_bool_true.
Qed.

Theorem negb_Zlt_bool :
  forall x y : Z,
  negb (Zlt_bool x y) = Zle_bool y x.
Proof.
intros x y.
case Zlt_bool_spec ; intros H.
now rewrite Zle_bool_false.
now rewrite Zle_bool_true.
Qed.

Theorem Zlt_bool_opp_l :
  forall x y,
  Zlt_bool (Z.opp x) y = Zlt_bool (Z.opp y) x.
Proof.
intros x y.
rewrite <- 2! negb_Zle_bool.
apply f_equal, Zle_bool_opp_r.
Qed.

Theorem Zlt_bool_opp_r :
  forall x y,
  Zlt_bool x (Z.opp y) = Zlt_bool y (Z.opp x).
Proof.
intros x y.
rewrite <- 2! negb_Zle_bool.
apply f_equal, Zle_bool_opp_l.
Qed.

Theorem Zlt_bool_opp :
  forall x y,
  Zlt_bool (Z.opp x) (Z.opp y) = Zlt_bool y x.
Proof.
intros x y.
rewrite <- 2! negb_Zle_bool.
apply f_equal, Zle_bool_opp.
Qed.

End Zlt_bool.

Section Zcompare.

Inductive Zcompare_prop (x y : Z) : comparison -> Prop :=
  | Zcompare_Lt_ : (x < y)%Z -> Zcompare_prop x y Lt
  | Zcompare_Eq_ : x = y -> Zcompare_prop x y Eq
  | Zcompare_Gt_ : (y < x)%Z -> Zcompare_prop x y Gt.

Theorem Zcompare_spec :
  forall x y, Zcompare_prop x y (Z.compare x y).
Proof.
intros x y.
destruct (Z_dec x y) as [[H|H]|H].
generalize (Zlt_compare _ _ H).
case (Z.compare x y) ; try easy.
now constructor.
generalize (Zgt_compare _ _ H).
case (Z.compare x y) ; try easy.
constructor.
now apply Z.gt_lt.
generalize (proj2 (Zcompare_Eq_iff_eq _ _) H).
case (Z.compare x y) ; try easy.
now constructor.
Qed.

Theorem Zcompare_Lt :
  forall x y,
  (x < y)%Z -> Z.compare x y = Lt.
Proof.
easy.
Qed.

Theorem Zcompare_Eq :
  forall x y,
  (x = y)%Z -> Z.compare x y = Eq.
Proof.
intros x y.
apply <- Zcompare_Eq_iff_eq.
Qed.

Theorem Zcompare_Gt :
  forall x y,
  (y < x)%Z -> Z.compare x y = Gt.
Proof.
intros x y.
apply Z.lt_gt.
Qed.

End Zcompare.

Section cond_Zopp.

Theorem cond_Zopp_0 :
  forall sx, cond_Zopp sx 0 = 0%Z.
Proof.
now intros [|].
Qed.

Theorem cond_Zopp_negb :
  forall x y, cond_Zopp (negb x) y = Z.opp (cond_Zopp x y).
Proof.
intros [|] y.
apply sym_eq, Z.opp_involutive.
easy.
Qed.

Theorem abs_cond_Zopp :
  forall b m,
  Z.abs (cond_Zopp b m) = Z.abs m.
Proof.
intros [|] m.
apply Zabs_Zopp.
apply refl_equal.
Qed.

Theorem cond_Zopp_Zlt_bool :
  forall m,
  cond_Zopp (Zlt_bool m 0) m = Z.abs m.
Proof.
intros m.
apply sym_eq.
case Zlt_bool_spec ; intros Hm.
apply Zabs_non_eq.
now apply Zlt_le_weak.
now apply Z.abs_eq.
Qed.

Theorem Zeq_bool_cond_Zopp :
  forall s m n,
  Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n).
Proof.
intros [|] m n ; simpl.
apply Zeq_bool_opp.
easy.
Qed.

End cond_Zopp.

Section fast_pow_pos.

Fixpoint Zfast_pow_pos (v : Z) (e : positive) : Z :=
  match e with
  | xH => v
  | xO e' => Z.square (Zfast_pow_pos v e')
  | xI e' => Zmult v (Z.square (Zfast_pow_pos v e'))
  end.

Theorem Zfast_pow_pos_correct :
  forall v e, Zfast_pow_pos v e = Zpower_pos v e.
Proof.
intros v e.
rewrite <- (Zmult_1_r (Zfast_pow_pos v e)).
unfold Z.pow_pos.
generalize 1%Z.
revert v.
induction e ; intros v f ; simpl.
-
 rewrite <- 2!IHe.
  rewrite Z.square_spec.
  ring.
-
 rewrite <- 2!IHe.
  rewrite Z.square_spec.
  apply eq_sym, Zmult_assoc.
-
 apply eq_refl.
Qed.

End fast_pow_pos.

Section faster_div.

Lemma Zdiv_eucl_unique :
  forall a b,
  Z.div_eucl a b = (Z.div a b, Zmod a b).
Proof.
intros a b.
unfold Z.div, Zmod.
now case Z.div_eucl.
Qed.

Fixpoint Zpos_div_eucl_aux1 (a b : positive) {struct b} :=
  match b with
  | xO b' =>
    match a with
    | xO a' => let (q, r) := Zpos_div_eucl_aux1 a' b' in (q, 2 * r)%Z
    | xI a' => let (q, r) := Zpos_div_eucl_aux1 a' b' in (q, 2 * r + 1)%Z
    | xH => (Z0, Zpos a)
    end
  | xH => (Zpos a, Z0)
  | xI _ => Z.pos_div_eucl a (Zpos b)
  end.

Lemma Zpos_div_eucl_aux1_correct :
  forall a b,
  Zpos_div_eucl_aux1 a b = Z.pos_div_eucl a (Zpos b).
Proof.
intros a b.
revert a.
induction b ; intros a.
-
 easy.
-
 change (Z.pos_div_eucl a (Zpos b~0)) with (Z.div_eucl (Zpos a) (Zpos b~0)).
  rewrite Zdiv_eucl_unique.
  change (Zpos b~0) with (2 * Zpos b)%Z.
  rewrite Z.rem_mul_r by easy.
  rewrite <- Zdiv_Zdiv by easy.
  destruct a as [a|a|].
  +
 change (Zpos_div_eucl_aux1 a~1 b~0) with (let (q, r) := Zpos_div_eucl_aux1 a b in (q, 2 * r + 1)%Z).
    rewrite IHb.
clear IHb.
    change (Z.pos_div_eucl a (Zpos b)) with (Z.div_eucl (Zpos a) (Zpos b)).
    rewrite Zdiv_eucl_unique.
    change (Zpos a~1) with (1 + 2 * Zpos a)%Z.
    rewrite (Zmult_comm 2 (Zpos a)).
    rewrite Z_div_plus_full by easy.
    apply f_equal.
    rewrite Z_mod_plus_full.
    apply Zplus_comm.
  +
 change (Zpos_div_eucl_aux1 a~0 b~0) with (let (q, r) := Zpos_div_eucl_aux1 a b in (q, 2 * r)%Z).
    rewrite IHb.
clear IHb.
    change (Z.pos_div_eucl a (Zpos b)) with (Z.div_eucl (Zpos a) (Zpos b)).
    rewrite Zdiv_eucl_unique.
    change (Zpos a~0) with (2 * Zpos a)%Z.
    rewrite (Zmult_comm 2 (Zpos a)).
    rewrite Z_div_mult_full by easy.
    apply f_equal.
    now rewrite Z_mod_mult.
  +
 easy.
-
 change (Z.pos_div_eucl a 1) with (Z.div_eucl (Zpos a) 1).
  rewrite Zdiv_eucl_unique.
  now rewrite Zdiv_1_r, Zmod_1_r.
Qed.

Definition Zpos_div_eucl_aux (a b : positive) :=
  match Pos.compare a b with
  | Lt => (Z0, Zpos a)
  | Eq => (1%Z, Z0)
  | Gt => Zpos_div_eucl_aux1 a b
  end.

Lemma Zpos_div_eucl_aux_correct :
  forall a b,
  Zpos_div_eucl_aux a b = Z.pos_div_eucl a (Zpos b).
Proof.
intros a b.
unfold Zpos_div_eucl_aux.
change (Z.pos_div_eucl a (Zpos b)) with (Z.div_eucl (Zpos a) (Zpos b)).
rewrite Zdiv_eucl_unique.
case Pos.compare_spec ; intros H.
now rewrite H, Z_div_same, Z_mod_same.
now rewrite Zdiv_small, Zmod_small by (split ; easy).
rewrite Zpos_div_eucl_aux1_correct.
change (Z.pos_div_eucl a (Zpos b)) with (Z.div_eucl (Zpos a) (Zpos b)).
apply Zdiv_eucl_unique.
Qed.

Definition Zfast_div_eucl (a b : Z) :=
  match a with
  | Z0 => (0, 0)%Z
  | Zpos a' =>
    match b with
    | Z0 => (0, (match (1 mod 0) with | 0 => 0 | _ => a end))%Z
    | Zpos b' => Zpos_div_eucl_aux a' b'
    | Zneg b' =>
      let (q, r) := Zpos_div_eucl_aux a' b' in
      match r with
      | Z0 => (-q, 0)%Z
      | Zpos _ => (-(q + 1), (b + r))%Z
      | Zneg _ => (-(q + 1), (b + r))%Z
      end
    end
  | Zneg a' =>
    match b with
    | Z0 => (0, (match (1 mod 0) with | 0 => 0 | _ => a end))%Z
    | Zpos b' =>
      let (q, r) := Zpos_div_eucl_aux a' b' in
      match r with
      | Z0 => (-q, 0)%Z
      | Zpos _ => (-(q + 1), (b - r))%Z
      | Zneg _ => (-(q + 1), (b - r))%Z
      end
    | Zneg b' => let (q, r) := Zpos_div_eucl_aux a' b' in (q, (-r)%Z)
    end
  end.

Theorem Zfast_div_eucl_correct :
  forall a b : Z,
  Zfast_div_eucl a b = Z.div_eucl a b.
Proof.
unfold Zfast_div_eucl.
intros [|a|a] [|b|b] ; try rewrite Zpos_div_eucl_aux_correct ; easy.
Qed.

End faster_div.

Section Iter.

Context {A : Type}.
Variable (f : A -> A).

Fixpoint iter_nat (n : nat) (x : A) {struct n} : A :=
  match n with
  | S n' => iter_nat n' (f x)
  | O => x
  end.

Lemma iter_nat_plus :
  forall (p q : nat) (x : A),
  iter_nat (p + q) x = iter_nat p (iter_nat q x).
Proof using .
induction q.
now rewrite Nat.add_0_r.
intros x.
rewrite <- plus_n_Sm.
apply IHq.
Qed.

Lemma iter_nat_S :
  forall (p : nat) (x : A),
  iter_nat (S p) x = f (iter_nat p x).
Proof using .
induction p.
easy.
simpl.
intros x.
apply IHp.
Qed.

Lemma iter_pos_nat :
  forall (p : positive) (x : A),
  iter_pos f p x = iter_nat (Pos.to_nat p) x.
Proof using .
induction p ; intros x.
rewrite Pos2Nat.inj_xI.
simpl.
rewrite Nat.add_0_r.
rewrite iter_nat_plus.
rewrite (IHp (f x)).
apply IHp.
rewrite Pos2Nat.inj_xO.
simpl.
rewrite Nat.add_0_r.
rewrite iter_nat_plus.
rewrite (IHp x).
apply IHp.
easy.
Qed.

End Iter.

End Zaux.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Zaux.
Require Stdlib.micromega.Psatz.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_Raux.
Module Export Flocq.
Module Export Core.
Module Export Raux.

Import Stdlib.micromega.Psatz Stdlib.Reals.Reals Stdlib.ZArith.ZArith.
Import Flocq.Core.Zaux.

Section Rmissing.

Theorem Rle_0_minus :
  forall x y, (x <= y)%R -> (0 <= y - x)%R.
Proof.
intros.
apply Rge_le.
apply Rge_minus.
now apply Rle_ge.
Qed.

Theorem Rabs_eq_Rabs :
  forall x y : R,
  Rabs x = Rabs y -> x = y \/ x = Ropp y.
Proof.
intros x y H.
unfold Rabs in H.
destruct (Rcase_abs x) as [_|_].
assert (H' := f_equal Ropp H).
rewrite Ropp_involutive in H'.
rewrite H'.
destruct (Rcase_abs y) as [_|_].
left.
apply Ropp_involutive.
now right.
rewrite H.
now destruct (Rcase_abs y) as [_|_] ; [right|left].
Qed.

Theorem Rabs_minus_le:
  forall x y : R,
  (0 <= y)%R -> (y <= 2*x)%R ->
  (Rabs (x-y) <= x)%R.
Proof.
intros x y Hx Hy.
apply Rabs_le.
lra.
Qed.

Theorem Rabs_eq_R0 x : (Rabs x = 0 -> x = 0)%R.
Proof.
split_Rabs; lra.
Qed.

Theorem Rmult_lt_compat :
  forall r1 r2 r3 r4,
  (0 <= r1)%R -> (0 <= r3)%R -> (r1 < r2)%R -> (r3 < r4)%R ->
  (r1 * r3 < r2 * r4)%R.
Proof.
intros r1 r2 r3 r4 Pr1 Pr3 H12 H34.
apply Rle_lt_trans with (r1 * r4)%R.
-
 apply Rmult_le_compat_l.
  +
 exact Pr1.
  +
 now apply Rlt_le.
-
 apply Rmult_lt_compat_r.
  +
 now apply Rle_lt_trans with r3.
  +
 exact H12.
Qed.

Lemma Rmult_neq_reg_r :
  forall r1 r2 r3 : R, (r2 * r1 <> r3 * r1)%R -> r2 <> r3.
Proof.
intros r1 r2 r3 H1 H2.
apply H1; rewrite H2; ring.
Qed.

Lemma Rmult_neq_compat_r :
  forall r1 r2 r3 : R,
  (r1 <> 0)%R -> (r2 <> r3)%R ->
  (r2 * r1 <> r3 * r1)%R.
Proof.
intros r1 r2 r3 H H1 H2.
now apply H1, Rmult_eq_reg_r with r1.
Qed.

Theorem Rmult_min_distr_r :
  forall r r1 r2 : R,
  (0 <= r)%R ->
  (Rmin r1 r2 * r)%R = Rmin (r1 * r) (r2 * r).
Proof.
intros r r1 r2 [Hr|Hr].
unfold Rmin.
destruct (Rle_dec r1 r2) as [H1|H1] ;
  destruct (Rle_dec (r1 * r) (r2 * r)) as [H2|H2] ;
  try easy.
apply (f_equal (fun x => Rmult x r)).
apply Rle_antisym.
exact H1.
apply Rmult_le_reg_r with (1 := Hr).
apply Rlt_le.
now apply Rnot_le_lt.
apply Rle_antisym.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rlt_le.
now apply Rnot_le_lt.
exact H2.
rewrite <- Hr.
rewrite 3!Rmult_0_r.
unfold Rmin.
destruct (Rle_dec 0 0) as [H0|H0].
easy.
elim H0.
apply Rle_refl.
Qed.

Theorem Rmult_min_distr_l :
  forall r r1 r2 : R,
  (0 <= r)%R ->
  (r * Rmin r1 r2)%R = Rmin (r * r1) (r * r2).
Proof.
intros r r1 r2 Hr.
rewrite 3!(Rmult_comm r).
now apply Rmult_min_distr_r.
Qed.

Lemma Rmin_opp: forall x y, (Rmin (-x) (-y) = - Rmax x y)%R.
Proof.
intros x y.
apply Rmax_case_strong; intros H.
rewrite Rmin_left; trivial.
now apply Ropp_le_contravar.
rewrite Rmin_right; trivial.
now apply Ropp_le_contravar.
Qed.

Lemma Rmax_opp: forall x y, (Rmax (-x) (-y) = - Rmin x y)%R.
Proof.
intros x y.
apply Rmin_case_strong; intros H.
rewrite Rmax_left; trivial.
now apply Ropp_le_contravar.
rewrite Rmax_right; trivial.
now apply Ropp_le_contravar.
Qed.

Theorem exp_le :
  forall x y : R,
  (x <= y)%R -> (exp x <= exp y)%R.
Proof.
intros x y [H|H].
apply Rlt_le.
now apply exp_increasing.
rewrite H.
apply Rle_refl.
Qed.

Theorem Rinv_lt :
  forall x y,
  (0 < x)%R -> (x < y)%R -> (/y < /x)%R.
Proof.
intros x y Hx Hxy.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
exact Hx.
now apply Rlt_trans with x.
exact Hxy.
Qed.

Theorem Rinv_le :
  forall x y,
  (0 < x)%R -> (x <= y)%R -> (/y <= /x)%R.
Proof.
intros x y Hx Hxy.
apply Rle_Rinv.
exact Hx.
now apply Rlt_le_trans with x.
exact Hxy.
Qed.

Theorem sqrt_ge_0 :
  forall x : R,
  (0 <= sqrt x)%R.
Proof.
intros x.
unfold sqrt.
destruct (Rcase_abs x) as [_|H].
apply Rle_refl.
apply Rsqrt_positivity.
Qed.

Lemma sqrt_neg : forall x, (x <= 0)%R -> (sqrt x = 0)%R.
Proof.
intros x Npx.
destruct (Req_dec x 0) as [Zx|Nzx].
-

  rewrite Zx.
  exact sqrt_0.
-

  unfold sqrt.
  destruct Rcase_abs.
  +
 reflexivity.
  +
 exfalso.
    now apply Nzx, Rle_antisym; [|apply Rge_le].
Qed.

Lemma Rsqr_le_abs_0_alt :
  forall x y,
  (x² <= y² -> x <= Rabs y)%R.
Proof.
intros x y H.
apply (Rle_trans _ (Rabs x)); [apply Rle_abs|apply (Rsqr_le_abs_0 _ _ H)].
Qed.

Theorem Rabs_le_inv :
  forall x y,
  (Rabs x <= y)%R -> (-y <= x <= y)%R.
Proof.
intros x y Hxy.
split.
apply Rle_trans with (- Rabs x)%R.
now apply Ropp_le_contravar.
apply Ropp_le_cancel.
rewrite Ropp_involutive, <- Rabs_Ropp.
apply RRle_abs.
apply Rle_trans with (2 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_ge :
  forall x y,
  (y <= -x \/ x <= y)%R -> (x <= Rabs y)%R.
Proof.
intros x y [Hyx|Hxy].
apply Rle_trans with (-y)%R.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
rewrite <- Rabs_Ropp.
apply RRle_abs.
apply Rle_trans with (1 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_ge_inv :
  forall x y,
  (x <= Rabs y)%R -> (y <= -x \/ x <= y)%R.
Proof.
intros x y.
unfold Rabs.
case Rcase_abs ; intros Hy Hxy.
left.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
now right.
Qed.

Theorem Rabs_lt :
  forall x y,
  (-y < x < y)%R -> (Rabs x < y)%R.
Proof.
intros x y (Hyx,Hxy).
now apply Rabs_def1.
Qed.

Theorem Rabs_lt_inv :
  forall x y,
  (Rabs x < y)%R -> (-y < x < y)%R.
Proof.
intros x y H.
now split ; eapply Rabs_def2.
Qed.

Theorem Rabs_gt :
  forall x y,
  (y < -x \/ x < y)%R -> (x < Rabs y)%R.
Proof.
intros x y [Hyx|Hxy].
rewrite <- Rabs_Ropp.
apply Rlt_le_trans with (Ropp y).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
apply RRle_abs.
apply Rlt_le_trans with (1 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_gt_inv :
  forall x y,
  (x < Rabs y)%R -> (y < -x \/ x < y)%R.
Proof.
intros x y.
unfold Rabs.
case Rcase_abs ; intros Hy Hxy.
left.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
now right.
Qed.

End Rmissing.

Section IZR.

Theorem IZR_le_lt :
  forall m n p, (m <= n < p)%Z -> (IZR m <= IZR n < IZR p)%R.
Proof.
intros m n p (H1, H2).
split.
now apply IZR_le.
now apply IZR_lt.
Qed.

Theorem le_lt_IZR :
  forall m n p, (IZR m <= IZR n < IZR p)%R -> (m <= n < p)%Z.
Proof.
intros m n p (H1, H2).
split.
now apply le_IZR.
now apply lt_IZR.
Qed.

Theorem neq_IZR :
  forall m n, (IZR m <> IZR n)%R -> (m <> n)%Z.
Proof.
intros m n H H'.
apply H.
now apply f_equal.
Qed.

End IZR.

Section Rcompare.

Definition Rcompare x y :=
  match total_order_T x y with
  | inleft (left _) => Lt
  | inleft (right _) => Eq
  | inright _ => Gt
  end.

Inductive Rcompare_prop (x y : R) : comparison -> Prop :=
  | Rcompare_Lt_ : (x < y)%R -> Rcompare_prop x y Lt
  | Rcompare_Eq_ : x = y -> Rcompare_prop x y Eq
  | Rcompare_Gt_ : (y < x)%R -> Rcompare_prop x y Gt.

Theorem Rcompare_spec :
  forall x y, Rcompare_prop x y (Rcompare x y).
Proof.
intros x y.
unfold Rcompare.
now destruct (total_order_T x y) as [[H|H]|H] ; constructor.
Qed.

Global Opaque Rcompare.

Theorem Rcompare_Lt :
  forall x y,
  (x < y)%R -> Rcompare x y = Lt.
Proof.
intros x y H.
case Rcompare_spec ; intro H'.
easy.
rewrite H' in H.
elim (Rlt_irrefl _ H).
elim (Rlt_irrefl x).
now apply Rlt_trans with y.
Qed.

Theorem Rcompare_Lt_inv :
  forall x y,
  Rcompare x y = Lt -> (x < y)%R.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_not_Lt :
  forall x y,
  (y <= x)%R -> Rcompare x y <> Lt.
Proof.
intros x y H1 H2.
apply Rle_not_lt with (1 := H1).
now apply Rcompare_Lt_inv.
Qed.

Theorem Rcompare_not_Lt_inv :
  forall x y,
  Rcompare x y <> Lt -> (y <= x)%R.
Proof.
intros x y H.
apply Rnot_lt_le.
contradict H.
now apply Rcompare_Lt.
Qed.

Theorem Rcompare_Eq :
  forall x y,
  x = y -> Rcompare x y = Eq.
Proof.
intros x y H.
rewrite H.
now case Rcompare_spec ; intro H' ; try elim (Rlt_irrefl _ H').
Qed.

Theorem Rcompare_Eq_inv :
  forall x y,
  Rcompare x y = Eq -> x = y.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_Gt :
  forall x y,
  (y < x)%R -> Rcompare x y = Gt.
Proof.
intros x y H.
case Rcompare_spec ; intro H'.
elim (Rlt_irrefl x).
now apply Rlt_trans with y.
rewrite H' in H.
elim (Rlt_irrefl _ H).
easy.
Qed.

Theorem Rcompare_Gt_inv :
  forall x y,
  Rcompare x y = Gt -> (y < x)%R.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_not_Gt :
  forall x y,
  (x <= y)%R -> Rcompare x y <> Gt.
Proof.
intros x y H1 H2.
apply Rle_not_lt with (1 := H1).
now apply Rcompare_Gt_inv.
Qed.

Theorem Rcompare_not_Gt_inv :
  forall x y,
  Rcompare x y <> Gt -> (x <= y)%R.
Proof.
intros x y H.
apply Rnot_lt_le.
contradict H.
now apply Rcompare_Gt.
Qed.

Theorem Rcompare_IZR :
  forall x y, Rcompare (IZR x) (IZR y) = Z.compare x y.
Proof.
intros x y.
case Rcompare_spec ; intros H ; apply sym_eq.
apply Zcompare_Lt.
now apply lt_IZR.
apply Zcompare_Eq.
now apply eq_IZR.
apply Zcompare_Gt.
now apply lt_IZR.
Qed.

Theorem Rcompare_sym :
  forall x y,
  Rcompare x y = CompOpp (Rcompare y x).
Proof.
intros x y.
destruct (Rcompare_spec y x) as [H|H|H].
now apply Rcompare_Gt.
now apply Rcompare_Eq.
now apply Rcompare_Lt.
Qed.

Lemma Rcompare_opp :
  forall x y,
  Rcompare (- x) (- y) = Rcompare y x.
Proof.
intros x y.
destruct (Rcompare_spec y x);
  destruct (Rcompare_spec (- x) (- y));
  try reflexivity; exfalso; lra.
Qed.

Theorem Rcompare_plus_r :
  forall z x y,
  Rcompare (x + z) (y + z) = Rcompare x y.
Proof.
intros z x y.
destruct (Rcompare_spec x y) as [H|H|H].
apply Rcompare_Lt.
now apply Rplus_lt_compat_r.
apply Rcompare_Eq.
now rewrite H.
apply Rcompare_Gt.
now apply Rplus_lt_compat_r.
Qed.

Theorem Rcompare_plus_l :
  forall z x y,
  Rcompare (z + x) (z + y) = Rcompare x y.
Proof.
intros z x y.
rewrite 2!(Rplus_comm z).
apply Rcompare_plus_r.
Qed.

Theorem Rcompare_mult_r :
  forall z x y,
  (0 < z)%R ->
  Rcompare (x * z) (y * z) = Rcompare x y.
Proof.
intros z x y Hz.
destruct (Rcompare_spec x y) as [H|H|H].
apply Rcompare_Lt.
now apply Rmult_lt_compat_r.
apply Rcompare_Eq.
now rewrite H.
apply Rcompare_Gt.
now apply Rmult_lt_compat_r.
Qed.

Theorem Rcompare_mult_l :
  forall z x y,
  (0 < z)%R ->
  Rcompare (z * x) (z * y) = Rcompare x y.
Proof.
intros z x y.
rewrite 2!(Rmult_comm z).
apply Rcompare_mult_r.
Qed.

Theorem Rcompare_middle :
  forall x d u,
  Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2).
Proof.
intros x d u.
rewrite <- (Rcompare_plus_r (- x / 2 - d / 2) x).
rewrite <- (Rcompare_mult_r (/2) (x - d)).
field_simplify (x + (- x / 2 - d / 2))%R.
now field_simplify ((d + u) / 2 + (- x / 2 - d / 2))%R.
apply Rinv_0_lt_compat.
now apply IZR_lt.
Qed.

Theorem Rcompare_half_l :
  forall x y, Rcompare (x / 2) y = Rcompare x (2 * y).
Proof.
intros x y.
rewrite <- (Rcompare_mult_r 2%R).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now rewrite Rmult_comm.
now apply IZR_neq.
now apply IZR_lt.
Qed.

Theorem Rcompare_half_r :
  forall x y, Rcompare x (y / 2) = Rcompare (2 * x) y.
Proof.
intros x y.
rewrite <- (Rcompare_mult_r 2%R).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now rewrite Rmult_comm.
now apply IZR_neq.
now apply IZR_lt.
Qed.

Theorem Rcompare_sqr :
  forall x y,
  Rcompare (x * x) (y * y) = Rcompare (Rabs x) (Rabs y).
Proof.
intros x y.
destruct (Rcompare_spec (Rabs x) (Rabs y)) as [H|H|H].
apply Rcompare_Lt.
now apply Rsqr_lt_abs_1.
change (Rcompare (Rsqr x) (Rsqr y) = Eq).
rewrite Rsqr_abs, H, (Rsqr_abs y).
now apply Rcompare_Eq.
apply Rcompare_Gt.
now apply Rsqr_lt_abs_1.
Qed.

Theorem Rmin_compare :
  forall x y,
  Rmin x y = match Rcompare x y with Lt => x | Eq => x | Gt => y end.
Proof.
intros x y.
unfold Rmin.
destruct (Rle_dec x y) as [[Hx|Hx]|Hx].
now rewrite Rcompare_Lt.
now rewrite Rcompare_Eq.
rewrite Rcompare_Gt.
easy.
now apply Rnot_le_lt.
Qed.

End Rcompare.

Section Rle_bool.

Definition Rle_bool x y :=
  match Rcompare x y with
  | Gt => false
  | _ => true
  end.

Inductive Rle_bool_prop (x y : R) : bool -> Prop :=
  | Rle_bool_true_ : (x <= y)%R -> Rle_bool_prop x y true
  | Rle_bool_false_ : (y < x)%R -> Rle_bool_prop x y false.

Theorem Rle_bool_spec :
  forall x y, Rle_bool_prop x y (Rle_bool x y).
Proof.
intros x y.
unfold Rle_bool.
case Rcompare_spec ; constructor.
now apply Rlt_le.
rewrite H.
apply Rle_refl.
exact H.
Qed.

Theorem Rle_bool_true :
  forall x y,
  (x <= y)%R -> Rle_bool x y = true.
Proof.
intros x y Hxy.
case Rle_bool_spec ; intros H.
apply refl_equal.
elim (Rlt_irrefl x).
now apply Rle_lt_trans with y.
Qed.

Theorem Rle_bool_false :
  forall x y,
  (y < x)%R -> Rle_bool x y = false.
Proof.
intros x y Hxy.
case Rle_bool_spec ; intros H.
elim (Rlt_irrefl x).
now apply Rle_lt_trans with y.
apply refl_equal.
Qed.

End Rle_bool.

Section Rlt_bool.

Definition Rlt_bool x y :=
  match Rcompare x y with
  | Lt => true
  | _ => false
  end.

Inductive Rlt_bool_prop (x y : R) : bool -> Prop :=
  | Rlt_bool_true_ : (x < y)%R -> Rlt_bool_prop x y true
  | Rlt_bool_false_ : (y <= x)%R -> Rlt_bool_prop x y false.

Theorem Rlt_bool_spec :
  forall x y, Rlt_bool_prop x y (Rlt_bool x y).
Proof.
intros x y.
unfold Rlt_bool.
case Rcompare_spec ; constructor.
exact H.
rewrite H.
apply Rle_refl.
now apply Rlt_le.
Qed.

Theorem negb_Rlt_bool :
  forall x y,
  negb (Rle_bool x y) = Rlt_bool y x.
Proof.
intros x y.
unfold Rlt_bool, Rle_bool.
rewrite Rcompare_sym.
now case Rcompare.
Qed.

Theorem negb_Rle_bool :
  forall x y,
  negb (Rlt_bool x y) = Rle_bool y x.
Proof.
intros x y.
unfold Rlt_bool, Rle_bool.
rewrite Rcompare_sym.
now case Rcompare.
Qed.

Theorem Rlt_bool_true :
  forall x y,
  (x < y)%R -> Rlt_bool x y = true.
Proof.
intros x y Hxy.
rewrite <- negb_Rlt_bool.
now rewrite Rle_bool_false.
Qed.

Theorem Rlt_bool_false :
  forall x y,
  (y <= x)%R -> Rlt_bool x y = false.
Proof.
intros x y Hxy.
rewrite <- negb_Rlt_bool.
now rewrite Rle_bool_true.
Qed.

Lemma Rlt_bool_opp :
  forall x y,
  Rlt_bool (- x) (- y) = Rlt_bool y x.
Proof.
intros x y.
now unfold Rlt_bool; rewrite Rcompare_opp.
Qed.

End Rlt_bool.

Section Req_bool.

Definition Req_bool x y :=
  match Rcompare x y with
  | Eq => true
  | _ => false
  end.

Inductive Req_bool_prop (x y : R) : bool -> Prop :=
  | Req_bool_true_ : (x = y)%R -> Req_bool_prop x y true
  | Req_bool_false_ : (x <> y)%R -> Req_bool_prop x y false.

Theorem Req_bool_spec :
  forall x y, Req_bool_prop x y (Req_bool x y).
Proof.
intros x y.
unfold Req_bool.
case Rcompare_spec ; constructor.
now apply Rlt_not_eq.
easy.
now apply Rgt_not_eq.
Qed.

Theorem Req_bool_true :
  forall x y,
  (x = y)%R -> Req_bool x y = true.
Proof.
intros x y Hxy.
case Req_bool_spec ; intros H.
apply refl_equal.
contradict H.
exact Hxy.
Qed.

Theorem Req_bool_false :
  forall x y,
  (x <> y)%R -> Req_bool x y = false.
Proof.
intros x y Hxy.
case Req_bool_spec ; intros H.
contradict Hxy.
exact H.
apply refl_equal.
Qed.

End Req_bool.

Section Floor_Ceil.

Definition Zfloor (x : R) := (up x - 1)%Z.

Theorem Zfloor_lb :
  forall x : R,
  (IZR (Zfloor x) <= x)%R.
Proof.
intros x.
unfold Zfloor.
rewrite minus_IZR.
simpl.
apply Rplus_le_reg_r with (1 - x)%R.
ring_simplify.
exact (proj2 (archimed x)).
Qed.

Theorem Zfloor_ub :
  forall x : R,
  (x < IZR (Zfloor x) + 1)%R.
Proof.
intros x.
unfold Zfloor.
rewrite minus_IZR.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
exact (proj1 (archimed x)).
Qed.

Theorem Zfloor_lub :
  forall n x,
  (IZR n <= x)%R ->
  (n <= Zfloor x)%Z.
Proof.
intros n x Hnx.
apply Zlt_succ_le.
apply lt_IZR.
apply Rle_lt_trans with (1 := Hnx).
unfold Z.succ.
rewrite plus_IZR.
apply Zfloor_ub.
Qed.

Theorem Zfloor_imp :
  forall n x,
  (IZR n <= x < IZR (n + 1))%R ->
  Zfloor x = n.
Proof.
intros n x Hnx.
apply Zle_antisym.
apply Zlt_succ_le.
apply lt_IZR.
apply Rle_lt_trans with (2 := proj2 Hnx).
apply Zfloor_lb.
now apply Zfloor_lub.
Qed.

Theorem Zfloor_IZR :
  forall n,
  Zfloor (IZR n) = n.
Proof.
intros n.
apply Zfloor_imp.
split.
apply Rle_refl.
apply IZR_lt.
apply Zlt_succ.
Qed.

Theorem Zfloor_le :
  forall x y, (x <= y)%R ->
  (Zfloor x <= Zfloor y)%Z.
Proof.
intros x y Hxy.
apply Zfloor_lub.
apply Rle_trans with (2 := Hxy).
apply Zfloor_lb.
Qed.

Definition Zceil (x : R) := (- Zfloor (- x))%Z.

Theorem Zceil_ub :
  forall x : R,
  (x <= IZR (Zceil x))%R.
Proof.
intros x.
unfold Zceil.
rewrite opp_IZR.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Zfloor_lb.
Qed.

Theorem Zceil_lb :
  forall x : R,
  (IZR (Zceil x) < x + 1)%R.
Proof.
intros x.
unfold Zceil.
rewrite opp_IZR.
rewrite <-(Ropp_involutive (x + 1)), Ropp_plus_distr.
apply Ropp_lt_contravar, (Rplus_lt_reg_r 1); ring_simplify.
apply Zfloor_ub.
Qed.

Theorem Zceil_glb :
  forall n x,
  (x <= IZR n)%R ->
  (Zceil x <= n)%Z.
Proof.
intros n x Hnx.
unfold Zceil.
apply Zopp_le_cancel.
rewrite Z.opp_involutive.
apply Zfloor_lub.
rewrite opp_IZR.
now apply Ropp_le_contravar.
Qed.

Theorem Zceil_imp :
  forall n x,
  (IZR (n - 1) < x <= IZR n)%R ->
  Zceil x = n.
Proof.
intros n x Hnx.
unfold Zceil.
rewrite <- (Z.opp_involutive n).
apply f_equal.
apply Zfloor_imp.
split.
rewrite opp_IZR.
now apply Ropp_le_contravar.
rewrite <- (Z.opp_involutive 1).
rewrite <- Zopp_plus_distr.
rewrite opp_IZR.
now apply Ropp_lt_contravar.
Qed.

Theorem Zceil_IZR :
  forall n,
  Zceil (IZR n) = n.
Proof.
intros n.
unfold Zceil.
rewrite <- opp_IZR, Zfloor_IZR.
apply Z.opp_involutive.
Qed.

Theorem Zceil_le :
  forall x y, (x <= y)%R ->
  (Zceil x <= Zceil y)%Z.
Proof.
intros x y Hxy.
apply Zceil_glb.
apply Rle_trans with (1 := Hxy).
apply Zceil_ub.
Qed.

Theorem Zceil_floor_neq :
  forall x : R,
  (IZR (Zfloor x) <> x)%R ->
  (Zceil x = Zfloor x + 1)%Z.
Proof.
intros x Hx.
apply Zceil_imp.
split.
ring_simplify (Zfloor x + 1 - 1)%Z.
apply Rnot_le_lt.
intros H.
apply Hx.
apply Rle_antisym.
apply Zfloor_lb.
exact H.
apply Rlt_le.
rewrite plus_IZR.
apply Zfloor_ub.
Qed.

Definition Ztrunc x := if Rlt_bool x 0 then Zceil x else Zfloor x.

Theorem Ztrunc_IZR :
  forall n,
  Ztrunc (IZR n) = n.
Proof.
intros n.
unfold Ztrunc.
case Rlt_bool_spec ; intro H.
apply Zceil_IZR.
apply Zfloor_IZR.
Qed.

Theorem Ztrunc_floor :
  forall x,
  (0 <= x)%R ->
  Ztrunc x = Zfloor x.
Proof.
intros x Hx.
unfold Ztrunc.
case Rlt_bool_spec ; intro H.
elim Rlt_irrefl with x.
now apply Rlt_le_trans with R0.
apply refl_equal.
Qed.

Theorem Ztrunc_ceil :
  forall x,
  (x <= 0)%R ->
  Ztrunc x = Zceil x.
Proof.
intros x Hx.
unfold Ztrunc.
case Rlt_bool_spec ; intro H.
apply refl_equal.
rewrite (Rle_antisym _ _ Hx H).
rewrite Zceil_IZR.
apply Zfloor_IZR.
Qed.

Theorem Ztrunc_le :
  forall x y, (x <= y)%R ->
  (Ztrunc x <= Ztrunc y)%Z.
Proof.
intros x y Hxy.
unfold Ztrunc at 1.
case Rlt_bool_spec ; intro Hx.
unfold Ztrunc.
case Rlt_bool_spec ; intro Hy.
now apply Zceil_le.
apply Z.le_trans with 0%Z.
apply Zceil_glb.
now apply Rlt_le.
now apply Zfloor_lub.
rewrite Ztrunc_floor.
now apply Zfloor_le.
now apply Rle_trans with x.
Qed.

Theorem Ztrunc_opp :
  forall x,
  Ztrunc (- x) = Z.opp (Ztrunc x).
Proof.
intros x.
unfold Ztrunc at 2.
case Rlt_bool_spec ; intros Hx.
rewrite Ztrunc_floor.
apply sym_eq.
apply Z.opp_involutive.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite Ztrunc_ceil.
unfold Zceil.
now rewrite Ropp_involutive.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
Qed.

Theorem Ztrunc_abs :
  forall x,
  Ztrunc (Rabs x) = Z.abs (Ztrunc x).
Proof.
intros x.
rewrite Ztrunc_floor.
2: apply Rabs_pos.
unfold Ztrunc.
case Rlt_bool_spec ; intro H.
rewrite Rabs_left with (1 := H).
rewrite Zabs_non_eq.
apply sym_eq.
apply Z.opp_involutive.
apply Zceil_glb.
now apply Rlt_le.
rewrite Rabs_pos_eq with (1 := H).
apply sym_eq.
apply Z.abs_eq.
now apply Zfloor_lub.
Qed.

Theorem Ztrunc_lub :
  forall n x,
  (IZR n <= Rabs x)%R ->
  (n <= Z.abs (Ztrunc x))%Z.
Proof.
intros n x H.
rewrite <- Ztrunc_abs.
rewrite Ztrunc_floor.
2: apply Rabs_pos.
now apply Zfloor_lub.
Qed.

Definition Zaway x := if Rlt_bool x 0 then Zfloor x else Zceil x.

Theorem Zaway_IZR :
  forall n,
  Zaway (IZR n) = n.
Proof.
intros n.
unfold Zaway.
case Rlt_bool_spec ; intro H.
apply Zfloor_IZR.
apply Zceil_IZR.
Qed.

Theorem Zaway_ceil :
  forall x,
  (0 <= x)%R ->
  Zaway x = Zceil x.
Proof.
intros x Hx.
unfold Zaway.
case Rlt_bool_spec ; intro H.
elim Rlt_irrefl with x.
now apply Rlt_le_trans with R0.
apply refl_equal.
Qed.

Theorem Zaway_floor :
  forall x,
  (x <= 0)%R ->
  Zaway x = Zfloor x.
Proof.
intros x Hx.
unfold Zaway.
case Rlt_bool_spec ; intro H.
apply refl_equal.
rewrite (Rle_antisym _ _ Hx H).
rewrite Zfloor_IZR.
apply Zceil_IZR.
Qed.

Theorem Zaway_le :
  forall x y, (x <= y)%R ->
  (Zaway x <= Zaway y)%Z.
Proof.
intros x y Hxy.
unfold Zaway at 1.
case Rlt_bool_spec ; intro Hx.
unfold Zaway.
case Rlt_bool_spec ; intro Hy.
now apply Zfloor_le.
apply le_IZR.
apply Rle_trans with 0%R.
apply Rlt_le.
apply Rle_lt_trans with (2 := Hx).
apply Zfloor_lb.
apply Rle_trans with (1 := Hy).
apply Zceil_ub.
rewrite Zaway_ceil.
now apply Zceil_le.
now apply Rle_trans with x.
Qed.

Theorem Zaway_opp :
  forall x,
  Zaway (- x) = Z.opp (Zaway x).
Proof.
intros x.
unfold Zaway at 2.
case Rlt_bool_spec ; intro H.
rewrite Zaway_ceil.
unfold Zceil.
now rewrite Ropp_involutive.
apply Rlt_le.
now apply Ropp_0_gt_lt_contravar.
rewrite Zaway_floor.
apply sym_eq.
apply Z.opp_involutive.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
Qed.

Theorem Zaway_abs :
  forall x,
  Zaway (Rabs x) = Z.abs (Zaway x).
Proof.
intros x.
rewrite Zaway_ceil.
2: apply Rabs_pos.
unfold Zaway.
case Rlt_bool_spec ; intro H.
rewrite Rabs_left with (1 := H).
rewrite Zabs_non_eq.
apply (f_equal (fun v => - Zfloor v)%Z).
apply Ropp_involutive.
apply le_IZR.
apply Rlt_le.
apply Rle_lt_trans with (2 := H).
apply Zfloor_lb.
rewrite Rabs_pos_eq with (1 := H).
apply sym_eq.
apply Z.abs_eq.
apply le_IZR.
apply Rle_trans with (1 := H).
apply Zceil_ub.
Qed.

End Floor_Ceil.

Theorem Rcompare_floor_ceil_middle :
  forall x,
  IZR (Zfloor x) <> x ->
  Rcompare (x - IZR (Zfloor x)) (/ 2) = Rcompare (x - IZR (Zfloor x)) (IZR (Zceil x) - x).
Proof.
intros x Hx.
rewrite Zceil_floor_neq with (1 := Hx).
rewrite plus_IZR.
destruct (Rcompare_spec (x - IZR (Zfloor x)) (/ 2)) as [H1|H1|H1] ; apply sym_eq.

apply Rcompare_Lt.
apply Rplus_lt_reg_l with (x - IZR (Zfloor x))%R.
replace (x - IZR (Zfloor x) + (x - IZR (Zfloor x)))%R with ((x - IZR (Zfloor x)) * 2)%R by ring.
replace (x - IZR (Zfloor x) + (IZR (Zfloor x) + 1 - x))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply IZR_lt.

apply Rcompare_Eq.
replace (IZR (Zfloor x) + 1 - x)%R with (1 - (x - IZR (Zfloor x)))%R by ring.
rewrite H1.
field.

apply Rcompare_Gt.
apply Rplus_lt_reg_l with (x - IZR (Zfloor x))%R.
replace (x - IZR (Zfloor x) + (x - IZR (Zfloor x)))%R with ((x - IZR (Zfloor x)) * 2)%R by ring.
replace (x - IZR (Zfloor x) + (IZR (Zfloor x) + 1 - x))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply IZR_lt.
Qed.

Theorem Rcompare_ceil_floor_middle :
  forall x,
  IZR (Zfloor x) <> x ->
  Rcompare (IZR (Zceil x) - x) (/ 2) = Rcompare (IZR (Zceil x) - x) (x - IZR (Zfloor x)).
Proof.
intros x Hx.
rewrite Zceil_floor_neq with (1 := Hx).
rewrite plus_IZR.
destruct (Rcompare_spec (IZR (Zfloor x) + 1 - x) (/ 2)) as [H1|H1|H1] ; apply sym_eq.

apply Rcompare_Lt.
apply Rplus_lt_reg_l with (IZR (Zfloor x) + 1 - x)%R.
replace (IZR (Zfloor x) + 1 - x + (IZR (Zfloor x) + 1 - x))%R with ((IZR (Zfloor x) + 1 - x) * 2)%R by ring.
replace (IZR (Zfloor x) + 1 - x + (x - IZR (Zfloor x)))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply IZR_lt.

apply Rcompare_Eq.
replace (x - IZR (Zfloor x))%R with (1 - (IZR (Zfloor x) + 1 - x))%R by ring.
rewrite H1.
field.

apply Rcompare_Gt.
apply Rplus_lt_reg_l with (IZR (Zfloor x) + 1 - x)%R.
replace (IZR (Zfloor x) + 1 - x + (IZR (Zfloor x) + 1 - x))%R with ((IZR (Zfloor x) + 1 - x) * 2)%R by ring.
replace (IZR (Zfloor x) + 1 - x + (x - IZR (Zfloor x)))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply IZR_lt.
Qed.

Theorem Zfloor_div :
  forall x y,
  y <> Z0 ->
  Zfloor (IZR x / IZR y) = (x / y)%Z.
Proof.
intros x y Zy.
generalize (Z.div_mod x y Zy).
intros Hx.
rewrite Hx at 1.
assert (Zy': IZR y <> 0%R).
contradict Zy.
now apply eq_IZR.
unfold Rdiv.
rewrite plus_IZR, Rmult_plus_distr_r, mult_IZR.
replace (IZR y * IZR (x / y) * / IZR y)%R with (IZR (x / y)) by now field.
apply Zfloor_imp.
rewrite plus_IZR.
assert (0 <= IZR (x mod y) * / IZR y < 1)%R.

assert (forall x' y', (0 < y')%Z -> 0 <= IZR (x' mod y') * / IZR y' < 1)%R.

clear.
intros x y Hy.
split.
apply Rmult_le_pos.
apply IZR_le.
refine (proj1 (Z_mod_lt _ _ _)).
now apply Z.lt_gt.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply Rmult_lt_reg_r with (IZR y).
now apply IZR_lt.
rewrite Rmult_1_l, Rmult_assoc, Rinv_l, Rmult_1_r.
apply IZR_lt.
eapply Z_mod_lt.
now apply Z.lt_gt.
apply Rgt_not_eq.
now apply IZR_lt.

destruct (Z_lt_le_dec y 0) as [Hy|Hy].
rewrite <- Rmult_opp_opp.
rewrite Ropp_inv_permute with (1 := Zy').
rewrite <- 2!opp_IZR.
rewrite <- Zmod_opp_opp.
apply H.
clear -Hy ; lia.
apply H.
clear -Zy Hy ; lia.

split.
pattern (IZR (x / y)) at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
apply H.
apply Rplus_lt_compat_l.
apply H.
Qed.

Theorem Ztrunc_div :
  forall x y, y <> 0%Z ->
  Ztrunc (IZR x / IZR y) = Z.quot x y.
Proof.
  destruct y; [easy | |]; destruct x; intros _.
  -
 rewrite Z.quot_0_l; [| easy].
unfold Rdiv.
rewrite Rmult_0_l.
    rewrite Ztrunc_floor; [| apply Rle_refl].
now rewrite Zfloor_IZR.
  -
 rewrite Z.quot_div_nonneg; [| easy | easy].
rewrite <-Zfloor_div; [| easy].
    unfold Ztrunc.
rewrite Rlt_bool_false; [reflexivity |].
    apply Rle_mult_inv_pos; [now apply IZR_le | now apply IZR_lt].
  -
 rewrite <-Pos2Z.opp_pos.
rewrite Z.quot_opp_l; [| easy].
    rewrite Z.quot_div_nonneg; [| easy | easy].
rewrite <-Zfloor_div; [| easy].
    rewrite Ropp_Ropp_IZR.
rewrite Ropp_div.
unfold Ztrunc.
rewrite Rlt_bool_true.
    +
 unfold Zceil.
now rewrite Ropp_involutive.
    +
 apply Ropp_lt_gt_0_contravar.
apply Rdiv_lt_0_compat; now apply IZR_lt.
  -
 rewrite Z.quot_0_l; [| easy].
unfold Rdiv.
rewrite Rmult_0_l.
    rewrite Ztrunc_floor; [| apply Rle_refl].
now rewrite Zfloor_IZR.
  -
 rewrite <-Pos2Z.opp_pos.
rewrite Z.quot_opp_r; [| easy].
    rewrite Z.quot_div_nonneg; [| easy | easy].
rewrite <-Zfloor_div; [| easy].
    rewrite Ropp_Ropp_IZR.
rewrite Ropp_div_den; [| easy].
unfold Ztrunc.
    rewrite Rlt_bool_true.
    +
 unfold Zceil.
now rewrite Ropp_involutive.
    +
 apply Ropp_lt_gt_0_contravar.
apply Rdiv_lt_0_compat; now apply IZR_lt.
  -
 rewrite <-2Pos2Z.opp_pos.
rewrite Z.quot_opp_l; [| easy].
rewrite Z.quot_opp_r; [| easy].
    rewrite Z.quot_div_nonneg; [| easy | easy].
rewrite <-Zfloor_div; [| easy].
    rewrite 2Ropp_Ropp_IZR.
rewrite Ropp_div.
rewrite Ropp_div_den; [| easy].
    rewrite Z.opp_involutive.
rewrite Ropp_involutive.
    unfold Ztrunc.
rewrite Rlt_bool_false; [reflexivity |].
    apply Rle_mult_inv_pos; [now apply IZR_le | now apply IZR_lt].
Qed.

Section pow.

Variable r : radix.

Theorem radix_pos : (0 < IZR r)%R.
Proof using .
destruct r as (v, Hr).
simpl.
apply IZR_lt.
apply Z.lt_le_trans with 2%Z.
easy.
now apply Zle_bool_imp_le.
Qed.

Definition bpow e :=
  match e with
  | Zpos p => IZR (Zpower_pos r p)
  | Zneg p => Rinv (IZR (Zpower_pos r p))
  | Z0 => 1%R
  end.

Theorem IZR_Zpower_pos :
  forall n m,
  IZR (Zpower_pos n m) = powerRZ (IZR n) (Zpos m).
Proof using .
intros.
rewrite Zpower_pos_nat.
simpl.
induction (nat_of_P m).
apply refl_equal.
unfold Zpower_nat.
simpl.
rewrite mult_IZR.
apply Rmult_eq_compat_l.
exact IHn0.
Qed.

Theorem bpow_powerRZ :
  forall e,
  bpow e = powerRZ (IZR r) e.
Proof using .
destruct e ; unfold bpow.
reflexivity.
now rewrite IZR_Zpower_pos.
now rewrite IZR_Zpower_pos.
Qed.

Theorem  bpow_ge_0 :
  forall e : Z, (0 <= bpow e)%R.
Proof using .
intros.
rewrite bpow_powerRZ.
apply powerRZ_le.
apply radix_pos.
Qed.

Theorem bpow_gt_0 :
  forall e : Z, (0 < bpow e)%R.
Proof using .
intros.
rewrite bpow_powerRZ.
apply powerRZ_lt.
apply radix_pos.
Qed.

Theorem bpow_plus :
  forall e1 e2 : Z, (bpow (e1 + e2) = bpow e1 * bpow e2)%R.
Proof using .
intros.
repeat rewrite bpow_powerRZ.
apply powerRZ_add.
apply Rgt_not_eq.
apply radix_pos.
Qed.

Theorem bpow_1 :
  bpow 1 = IZR r.
Proof using .
unfold bpow, Zpower_pos.
simpl.
now rewrite Zmult_1_r.
Qed.

Theorem bpow_plus_1 :
  forall e : Z, (bpow (e + 1) = IZR r * bpow e)%R.
Proof using .
intros.
rewrite <- bpow_1.
rewrite <- bpow_plus.
now rewrite Zplus_comm.
Qed.

Theorem bpow_opp :
  forall e : Z, (bpow (-e) = /bpow e)%R.
Proof using .
intros [|p|p].
apply eq_sym, Rinv_1.
now change (-Zpos p)%Z with (Zneg p).
change (-Zneg p)%Z with (Zpos p).
simpl; rewrite Rinv_involutive; trivial.
apply Rgt_not_eq.
apply (bpow_gt_0 (Zpos p)).
Qed.

Theorem IZR_Zpower_nat :
  forall e : nat,
  IZR (Zpower_nat r e) = bpow (Z_of_nat e).
Proof using .
intros [|e].
split.
rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ.
rewrite <- Zpower_pos_nat.
now rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Theorem IZR_Zpower :
  forall e : Z,
  (0 <= e)%Z ->
  IZR (Zpower r e) = bpow e.
Proof using .
intros [|e|e] H.
split.
split.
now elim H.
Qed.

Theorem bpow_lt :
  forall e1 e2 : Z,
  (e1 < e2)%Z -> (bpow e1 < bpow e2)%R.
Proof using .
intros e1 e2 H.
replace e2 with (e1 + (e2 - e1))%Z by ring.
rewrite <- (Rmult_1_r (bpow e1)).
rewrite bpow_plus.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
assert (0 < e2 - e1)%Z by lia.
destruct (e2 - e1)%Z ; try discriminate H0.
clear.
rewrite <- IZR_Zpower by easy.
apply IZR_lt.
now apply Zpower_gt_1.
Qed.

Theorem lt_bpow :
  forall e1 e2 : Z,
  (bpow e1 < bpow e2)%R -> (e1 < e2)%Z.
Proof using .
intros e1 e2 H.
apply Z.gt_lt.
apply Znot_le_gt.
intros H'.
apply Rlt_not_le with (1 := H).
destruct (Zle_lt_or_eq _ _ H').
apply Rlt_le.
now apply bpow_lt.
rewrite H0.
apply Rle_refl.
Qed.

Theorem bpow_le :
  forall e1 e2 : Z,
  (e1 <= e2)%Z -> (bpow e1 <= bpow e2)%R.
Proof using .
intros e1 e2 H.
apply Rnot_lt_le.
intros H'.
apply Zle_not_gt with (1 := H).
apply Z.lt_gt.
now apply lt_bpow.
Qed.

Theorem le_bpow :
  forall e1 e2 : Z,
  (bpow e1 <= bpow e2)%R -> (e1 <= e2)%Z.
Proof using .
intros e1 e2 H.
apply Znot_gt_le.
intros H'.
apply Rle_not_lt with (1 := H).
apply bpow_lt.
now apply Z.gt_lt.
Qed.

Theorem bpow_inj :
  forall e1 e2 : Z,
  bpow e1 = bpow e2 -> e1 = e2.
Proof using .
intros.
apply Zle_antisym.
apply le_bpow.
now apply Req_le.
apply le_bpow.
now apply Req_le.
Qed.

Theorem bpow_exp :
  forall e : Z,
  bpow e = exp (IZR e * ln (IZR r)).
Proof using .

assert (forall e, bpow (Zpos e) = exp (IZR (Zpos e) * ln (IZR r))).
intros e.
unfold bpow.
rewrite Zpower_pos_nat.
rewrite <- positive_nat_Z.
rewrite <- INR_IZR_INZ.
induction (nat_of_P e).
rewrite Rmult_0_l.
now rewrite exp_0.
rewrite Zpower_nat_S.
rewrite S_INR.
rewrite Rmult_plus_distr_r.
rewrite exp_plus.
rewrite Rmult_1_l.
rewrite exp_ln.
rewrite <- IHn.
rewrite <- mult_IZR.
now rewrite Zmult_comm.
apply radix_pos.

intros [|e|e].
rewrite Rmult_0_l.
now rewrite exp_0.
apply H.
unfold bpow.
change (IZR (Zpower_pos r e)) with (bpow (Zpos e)).
rewrite H.
rewrite <- exp_Ropp.
rewrite <- Ropp_mult_distr_l_reverse.
now rewrite <- opp_IZR.
Qed.

Lemma sqrt_bpow :
  forall e,
  sqrt (bpow (2 * e)) = bpow e.
Proof using .
intro e.
change 2%Z with (1 + 1)%Z; rewrite Z.mul_add_distr_r, Z.mul_1_l, bpow_plus.
apply sqrt_square, bpow_ge_0.
Qed.

Lemma sqrt_bpow_ge :
  forall e,
  (bpow (e / 2) <= sqrt (bpow e))%R.
Proof using .
intro e.
rewrite <- (sqrt_square (bpow _)); [|now apply bpow_ge_0].
apply sqrt_le_1_alt; rewrite <- bpow_plus; apply bpow_le.
now replace (_ + _)%Z with (2 * (e / 2))%Z by ring; apply Z_mult_div_ge.
Qed.

Record mag_prop x := {
  mag_val :> Z ;
  _ : (x <> 0)%R -> (bpow (mag_val - 1)%Z <= Rabs x < bpow mag_val)%R
}.

Definition mag :
  forall x : R, mag_prop x.
Proof using .
intros x.
set (fact := ln (IZR r)).

assert (0 < fact)%R.
apply exp_lt_inv.
rewrite exp_0.
unfold fact.
rewrite exp_ln.
apply IZR_lt.
apply radix_gt_1.
apply radix_pos.

exists (Zfloor (ln (Rabs x) / fact) + 1)%Z.
intros Hx'.
generalize (Rabs_pos_lt _ Hx').
clear Hx'.
generalize (Rabs x).
clear x.
intros x Hx.
rewrite 2!bpow_exp.
fold fact.
pattern x at 2 3 ; replace x with (exp (ln x * / fact * fact)).
split.
rewrite minus_IZR.
apply exp_le.
apply Rmult_le_compat_r.
now apply Rlt_le.
unfold Rminus.
rewrite plus_IZR.
rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
apply Zfloor_lb.
apply exp_increasing.
apply Rmult_lt_compat_r.
exact H.
rewrite plus_IZR.
apply Zfloor_ub.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
now apply exp_ln.
now apply Rgt_not_eq.
Qed.

Theorem bpow_lt_bpow :
  forall e1 e2,
  (bpow (e1 - 1) < bpow e2)%R ->
  (e1 <= e2)%Z.
Proof using .
intros e1 e2 He.
rewrite (Zsucc_pred e1).
apply Zlt_le_succ.
now apply lt_bpow.
Qed.

Theorem bpow_unique :
  forall x e1 e2,
  (bpow (e1 - 1) <= x < bpow e1)%R ->
  (bpow (e2 - 1) <= x < bpow e2)%R ->
  e1 = e2.
Proof using .
intros x e1 e2 (H1a,H1b) (H2a,H2b).
apply Zle_antisym ;
  apply bpow_lt_bpow ;
  apply Rle_lt_trans with x ;
  assumption.
Qed.

Theorem mag_unique :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= Rabs x < bpow e)%R ->
  mag x = e :> Z.
Proof using .
intros x e1 He.
destruct (Req_dec x 0) as [Hx|Hx].
elim Rle_not_lt with (1 := proj1 He).
rewrite Hx, Rabs_R0.
apply bpow_gt_0.
destruct (mag x) as (e2, Hx2).
simpl.
apply bpow_unique with (2 := He).
now apply Hx2.
Qed.

Theorem mag_opp :
  forall x,
  mag (-x) = mag x :> Z.
Proof using .
intros x.
destruct (Req_dec x 0) as [Hx|Hx].
now rewrite Hx, Ropp_0.
destruct (mag x) as (e, He).
simpl.
specialize (He Hx).
apply mag_unique.
now rewrite Rabs_Ropp.
Qed.

Theorem mag_abs :
  forall x,
  mag (Rabs x) = mag x :> Z.
Proof using .
intros x.
unfold Rabs.
case Rcase_abs ; intros _.
apply mag_opp.
apply refl_equal.
Qed.

Theorem mag_unique_pos :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= x < bpow e)%R ->
  mag x = e :> Z.
Proof using .
intros x e1 He1.
rewrite <- mag_abs.
apply mag_unique.
rewrite 2!Rabs_pos_eq.
exact He1.
apply Rle_trans with (2 := proj1 He1).
apply bpow_ge_0.
apply Rabs_pos.
Qed.

Theorem mag_le_abs :
  forall x y,
  (x <> 0)%R -> (Rabs x <= Rabs y)%R ->
  (mag x <= mag y)%Z.
Proof using .
intros x y H0x Hxy.
destruct (mag x) as (ex, Hx).
destruct (mag y) as (ey, Hy).
simpl.
apply bpow_lt_bpow.
specialize (Hx H0x).
apply Rle_lt_trans with (1 := proj1 Hx).
apply Rle_lt_trans with (1 := Hxy).
apply Hy.
intros Hy'.
apply Rlt_not_le with (1 := Rabs_pos_lt _ H0x).
apply Rle_trans with (1 := Hxy).
rewrite Hy', Rabs_R0.
apply Rle_refl.
Qed.

Theorem mag_le :
  forall x y,
  (0 < x)%R -> (x <= y)%R ->
  (mag x <= mag y)%Z.
Proof using .
intros x y H0x Hxy.
apply mag_le_abs.
now apply Rgt_not_eq.
rewrite 2!Rabs_pos_eq.
exact Hxy.
apply Rle_trans with (2 := Hxy).
now apply Rlt_le.
now apply Rlt_le.
Qed.

Lemma lt_mag :
  forall x y,
  (0 < y)%R ->
  (mag x < mag y)%Z -> (x < y)%R.
Proof using .
intros x y Py.
case (Rle_or_lt x 0); intros Px.
intros H.
now apply Rle_lt_trans with 0%R.
destruct (mag x) as (ex, Hex).
destruct (mag y) as (ey, Hey).
simpl.
intro H.
destruct Hex as (_,Hex); [now apply Rgt_not_eq|].
destruct Hey as (Hey,_); [now apply Rgt_not_eq|].
rewrite Rabs_right in Hex; [|now apply Rle_ge; apply Rlt_le].
rewrite Rabs_right in Hey; [|now apply Rle_ge; apply Rlt_le].
apply (Rlt_le_trans _ _ _ Hex).
apply Rle_trans with (bpow (ey - 1)); [|exact Hey].
now apply bpow_le; lia.
Qed.

Theorem mag_bpow :
  forall e, (mag (bpow e) = e + 1 :> Z)%Z.
Proof using .
intros e.
apply mag_unique.
rewrite Rabs_right.
replace (e + 1 - 1)%Z with e by ring.
split.
apply Rle_refl.
apply bpow_lt.
apply Zlt_succ.
apply Rle_ge.
apply bpow_ge_0.
Qed.

Theorem mag_mult_bpow :
  forall x e, x <> 0%R ->
  (mag (x * bpow e) = mag x + e :>Z)%Z.
Proof using .
intros x e Zx.
destruct (mag x) as (ex, Ex) ; simpl.
specialize (Ex Zx).
apply mag_unique.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow e)) by apply bpow_ge_0.
split.
replace (ex + e - 1)%Z with (ex - 1 + e)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Ex.
rewrite bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Ex.
Qed.

Theorem mag_le_bpow :
  forall x e,
  x <> 0%R ->
  (Rabs x < bpow e)%R ->
  (mag x <= e)%Z.
Proof using .
intros x e Zx Hx.
destruct (mag x) as (ex, Ex) ; simpl.
specialize (Ex Zx).
apply bpow_lt_bpow.
now apply Rle_lt_trans with (Rabs x).
Qed.

Theorem mag_gt_bpow :
  forall x e,
  (bpow e <= Rabs x)%R ->
  (e < mag x)%Z.
Proof using .
intros x e Hx.
destruct (mag x) as (ex, Ex) ; simpl.
apply lt_bpow.
apply Rle_lt_trans with (1 := Hx).
apply Ex.
intros Zx.
apply Rle_not_lt with (1 := Hx).
rewrite Zx, Rabs_R0.
apply bpow_gt_0.
Qed.

Theorem mag_ge_bpow :
  forall x e,
  (bpow (e - 1) <= Rabs x)%R ->
  (e <= mag x)%Z.
Proof using .
intros x e H.
destruct (Rlt_or_le (Rabs x) (bpow e)) as [Hxe|Hxe].
-

  assert (mag x = e :> Z) as Hln.
  now apply mag_unique; split.
  rewrite Hln.
  now apply Z.le_refl.
-

  apply Zlt_le_weak.
  now apply mag_gt_bpow.
Qed.

Theorem bpow_mag_gt :
  forall x,
  (Rabs x < bpow (mag x))%R.
Proof using .
intros x.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, Rabs_R0.
apply bpow_gt_0.
destruct (mag x) as (ex, Ex) ; simpl.
now apply Ex.
Qed.

Theorem bpow_mag_le :
  forall x, (x <> 0)%R ->
    (bpow (mag x-1) <= Rabs x)%R.
Proof using .
intros x Hx.
destruct (mag x) as (ex, Ex) ; simpl.
now apply Ex.
Qed.

Theorem mag_le_Zpower :
  forall m e,
  m <> Z0 ->
  (Z.abs m < Zpower r e)%Z->
  (mag (IZR m) <= e)%Z.
Proof using .
intros m e Zm Hm.
apply mag_le_bpow.
now apply IZR_neq.
destruct (Zle_or_lt 0 e).
rewrite <- abs_IZR, <- IZR_Zpower with (1 := H).
now apply IZR_lt.
elim Zm.
cut (Z.abs m < 0)%Z.
now case m.
clear -Hm H.
now destruct e.
Qed.

Theorem mag_gt_Zpower :
  forall m e,
  m <> Z0 ->
  (Zpower r e <= Z.abs m)%Z ->
  (e < mag (IZR m))%Z.
Proof using .
intros m e Zm Hm.
apply mag_gt_bpow.
rewrite <- abs_IZR.
destruct (Zle_or_lt 0 e).
rewrite <- IZR_Zpower with (1 := H).
now apply IZR_le.
apply Rle_trans with (bpow 0).
apply bpow_le.
now apply Zlt_le_weak.
apply IZR_le.
clear -Zm.
lia.
Qed.

Lemma mag_mult :
  forall x y,
  (x <> 0)%R -> (y <> 0)%R ->
  (mag x + mag y - 1 <= mag (x * y) <= mag x + mag y)%Z.
Proof using .
intros x y Hx Hy.
destruct (mag x) as (ex, Hx2).
destruct (mag y) as (ey, Hy2).
simpl.
destruct (Hx2 Hx) as (Hx21,Hx22); clear Hx2.
destruct (Hy2 Hy) as (Hy21,Hy22); clear Hy2.
assert (Hxy : (bpow (ex + ey - 1 - 1) <= Rabs (x * y))%R).
{
 replace (ex + ey -1 -1)%Z with (ex - 1 + (ey - 1))%Z; [|ring].
  rewrite bpow_plus.
  rewrite Rabs_mult.
  now apply Rmult_le_compat; try apply bpow_ge_0.
}
assert (Hxy2 : (Rabs (x * y) < bpow (ex + ey))%R).
{
 rewrite Rabs_mult.
  rewrite bpow_plus.
  apply Rmult_le_0_lt_compat; try assumption.
  now apply Rle_trans with (bpow (ex - 1)); try apply bpow_ge_0.
  now apply Rle_trans with (bpow (ey - 1)); try apply bpow_ge_0.
}
split.
-
 now apply mag_ge_bpow.
-
 apply mag_le_bpow.
  +
 now apply Rmult_integral_contrapositive_currified.
  +
 assumption.
Qed.

Lemma mag_plus :
  forall x y,
  (0 < y)%R -> (y <= x)%R ->
  (mag x <= mag (x + y) <= mag x + 1)%Z.
Proof using .
assert (Hr : (2 <= r)%Z).
{
 destruct r as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
}
intros x y Hy Hxy.
assert (Hx : (0 < x)%R) by apply (Rlt_le_trans _ _ _ Hy Hxy).
destruct (mag x) as (ex,Hex); simpl.
destruct Hex as (Hex0,Hex1); [now apply Rgt_not_eq|].
assert (Haxy : (Rabs (x + y) < bpow (ex + 1))%R).
{
 rewrite bpow_plus_1.
  apply Rlt_le_trans with (2 * bpow ex)%R.
  -
 rewrite Rabs_pos_eq.
    apply Rle_lt_trans with (2 * Rabs x)%R.
    +
 rewrite Rabs_pos_eq.
      replace (2 * x)%R with (x + x)%R by ring.
      now apply Rplus_le_compat_l.
      now apply Rlt_le.
    +
 apply Rmult_lt_compat_l with (2 := Hex1).
      exact Rlt_0_2.
    +
 rewrite <- (Rplus_0_l 0).
      now apply Rlt_le, Rplus_lt_compat.
  -
 apply Rmult_le_compat_r.
    now apply bpow_ge_0.
    now apply IZR_le.
}
assert (Haxy2 : (bpow (ex - 1) <= Rabs (x + y))%R).
{
 apply (Rle_trans _ _ _ Hex0).
  rewrite Rabs_right; [|now apply Rgt_ge].
  apply Rabs_ge; right.
  rewrite <- (Rplus_0_r x) at 1.
  apply Rplus_le_compat_l.
  now apply Rlt_le.
}
split.
-
 now apply mag_ge_bpow.
-
 apply mag_le_bpow.
  +
 now apply tech_Rplus; [apply Rlt_le|].
  +
 exact Haxy.
Qed.

Lemma mag_minus :
  forall x y,
  (0 < y)%R -> (y < x)%R ->
  (mag (x - y) <= mag x)%Z.
Proof using .
intros x y Py Hxy.
assert (Px : (0 < x)%R) by apply (Rlt_trans _ _ _ Py Hxy).
apply mag_le.
-
 now apply Rlt_Rminus.
-
 rewrite <- (Rplus_0_r x) at 2.
  apply Rplus_le_compat_l.
  rewrite <- Ropp_0.
  now apply Ropp_le_contravar; apply Rlt_le.
Qed.

Lemma mag_minus_lb :
  forall x y,
  (0 < x)%R -> (0 < y)%R ->
  (mag y <= mag x - 2)%Z ->
  (mag x - 1 <= mag (x - y))%Z.
Proof using .
assert (Hbeta : (2 <= r)%Z).
{
 destruct r as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
}
intros x y Px Py Hln.
assert (Oxy : (y < x)%R); [apply lt_mag;[assumption|lia]|].
destruct (mag x) as (ex,Hex).
destruct (mag y) as (ey,Hey).
simpl in Hln |- *.
destruct Hex as (Hex,_); [now apply Rgt_not_eq|].
destruct Hey as (_,Hey); [now apply Rgt_not_eq|].
assert (Hbx : (bpow (ex - 2) + bpow (ex - 2) <= x)%R).
{
 ring_simplify.
  apply Rle_trans with (bpow (ex - 1)).
  -
 replace (ex - 1)%Z with (ex - 2 + 1)%Z by ring.
    rewrite bpow_plus_1.
    apply Rmult_le_compat_r; [now apply bpow_ge_0|].
    now apply IZR_le.
  -
 now rewrite Rabs_right in Hex; [|apply Rle_ge; apply Rlt_le].
}
assert (Hby : (y < bpow (ex - 2))%R).
{
 apply Rlt_le_trans with (bpow ey).
  now rewrite Rabs_right in Hey; [|apply Rle_ge; apply Rlt_le].
  now apply bpow_le.
}
assert (Hbxy : (bpow (ex - 2) <= x - y)%R).
{
 apply Ropp_lt_contravar in Hby.
  apply Rlt_le in Hby.
  replace (bpow (ex - 2))%R with (bpow (ex - 2) + bpow (ex - 2)
                                                  - bpow (ex - 2))%R by ring.
  now apply Rplus_le_compat.
}
apply mag_ge_bpow.
replace (ex - 1 - 1)%Z with (ex - 2)%Z by ring.
now apply Rabs_ge; right.
Qed.

Theorem mag_plus_ge :
  forall x y,
  (x <> 0)%R ->
  (mag y <= mag x - 2)%Z ->
  (mag x - 1 <= mag (x + y))%Z.
Proof using .
intros x y Zx.
destruct (Req_dec y 0) as [Zy|Zy].
{
 intros _.
  rewrite Zy, Rplus_0_r.
  lia.
}
rewrite <- (mag_abs x), <- (mag_abs y).
intros Hm.
assert (H: Rabs x <> Rabs y).
{
 intros H.
  apply Zlt_not_le with (2 := Hm).
  rewrite H.
  lia.
}
apply mag_minus_lb in Hm ; try now apply Rabs_pos_lt.
apply Z.le_trans with (1 := Hm).
apply mag_le_abs.
now apply Rminus_eq_contra.
rewrite <- (Ropp_involutive y).
rewrite Rabs_Ropp.
apply Rabs_triang_inv2.
Qed.

Lemma mag_div :
  forall x y : R,
  x <> 0%R -> y <> 0%R ->
  (mag x - mag y <= mag (x / y) <= mag x - mag y + 1)%Z.
Proof using .
intros x y Px Py.
destruct (mag x) as (ex,Hex).
destruct (mag y) as (ey,Hey).
simpl.
unfold Rdiv.
assert (Heiy : (bpow (- ey) < Rabs (/ y) <= bpow (- ey + 1))%R).
{
 rewrite Rabs_Rinv by easy.
  split.
  -
 rewrite bpow_opp.
    apply Rinv_lt_contravar.
    +
 apply Rmult_lt_0_compat.
      now apply Rabs_pos_lt.
      now apply bpow_gt_0.
    +
 now apply Hey.
  -
 replace (_ + _)%Z with (- (ey - 1))%Z by ring.
    rewrite bpow_opp.
    apply Rinv_le; [now apply bpow_gt_0|].
    now apply Hey.
}
split.
-
 apply mag_ge_bpow.
  replace (_ - _)%Z with (ex - 1 - ey)%Z by ring.
  unfold Zminus at 1; rewrite bpow_plus.
  rewrite Rabs_mult.
  apply Rmult_le_compat.
  +
 now apply bpow_ge_0.
  +
 now apply bpow_ge_0.
  +
 now apply Hex.
  +
 now apply Rlt_le; apply Heiy.
-
 apply mag_le_bpow.
  +
 apply Rmult_integral_contrapositive_currified.
    exact Px.
    now apply Rinv_neq_0_compat.
  +
 replace (_ + 1)%Z with (ex + (- ey + 1))%Z by ring.
    rewrite bpow_plus.
    apply Rlt_le_trans with (bpow ex * Rabs (/ y))%R.
    *
 rewrite Rabs_mult.
      apply Rmult_lt_compat_r.
      apply Rabs_pos_lt.
      now apply Rinv_neq_0_compat.
      now apply Hex.
    *
 apply Rmult_le_compat_l; [now apply bpow_ge_0|].
      apply Heiy.
Qed.

Lemma mag_sqrt :
  forall x,
  (0 < x)%R ->
  mag (sqrt x) = Z.div2 (mag x + 1) :> Z.
Proof using .
intros x Px.
apply mag_unique.
destruct mag as [e He].
simpl.
specialize (He (Rgt_not_eq _ _ Px)).
rewrite Rabs_pos_eq in He by now apply Rlt_le.
split.
-
 rewrite <- (Rabs_pos_eq (bpow _)) by apply bpow_ge_0.
  apply Rsqr_le_abs_0.
  rewrite Rsqr_sqrt by now apply Rlt_le.
  apply Rle_trans with (2 := proj1 He).
  unfold Rsqr ; rewrite <- bpow_plus.
  apply bpow_le.
  generalize (Zdiv2_odd_eqn (e + 1)).
  destruct Z.odd ; intros ; lia.
-
 rewrite <- (Rabs_pos_eq (bpow _)) by apply bpow_ge_0.
  apply Rsqr_lt_abs_0.
  rewrite Rsqr_sqrt by now apply Rlt_le.
  apply Rlt_le_trans with (1 := proj2 He).
  unfold Rsqr ; rewrite <- bpow_plus.
  apply bpow_le.
  generalize (Zdiv2_odd_eqn (e + 1)).
  destruct Z.odd ; intros ; lia.
Qed.

Lemma mag_1 : mag 1 = 1%Z :> Z.
Proof using .
apply mag_unique_pos; rewrite bpow_1; simpl; split; [now right|apply IZR_lt].
assert (H := Zle_bool_imp_le _ _ (radix_prop r)); revert H.
now apply Z.lt_le_trans.
Qed.

End pow.

Section Bool.

Theorem eqb_sym :
  forall x y, Bool.eqb x y = Bool.eqb y x.
Proof.
now intros [|] [|].
Qed.

Theorem eqb_false :
  forall x y, x = negb y -> Bool.eqb x y = false.
Proof.
now intros [|] [|].
Qed.

Theorem eqb_true :
  forall x y, x = y -> Bool.eqb x y = true.
Proof.
now intros [|] [|].
Qed.

End Bool.

Section cond_Ropp.

Definition cond_Ropp (b : bool) m := if b then Ropp m else m.

Theorem IZR_cond_Zopp :
  forall b m,
  IZR (cond_Zopp b m) = cond_Ropp b (IZR m).
Proof.
intros [|] m.
apply opp_IZR.
apply refl_equal.
Qed.

Theorem abs_cond_Ropp :
  forall b m,
  Rabs (cond_Ropp b m) = Rabs m.
Proof.
intros [|] m.
apply Rabs_Ropp.
apply refl_equal.
Qed.

Theorem cond_Ropp_Rlt_bool :
  forall m,
  cond_Ropp (Rlt_bool m 0) m = Rabs m.
Proof.
intros m.
apply sym_eq.
case Rlt_bool_spec ; intros Hm.
now apply Rabs_left.
now apply Rabs_pos_eq.
Qed.

Theorem Rlt_bool_cond_Ropp :
  forall x sx, (0 < x)%R ->
  Rlt_bool (cond_Ropp sx x) 0 = sx.
Proof.
  intros x sx Hx.
destruct sx; simpl.
  -
 apply Rlt_bool_true.
now apply Ropp_lt_gt_0_contravar.
  -
 apply Rlt_bool_false.
now left.
Qed.

Theorem cond_Ropp_involutive :
  forall b x,
  cond_Ropp b (cond_Ropp b x) = x.
Proof.
intros [|] x.
apply Ropp_involutive.
apply refl_equal.
Qed.

Theorem cond_Ropp_inj :
  forall b x y,
  cond_Ropp b x = cond_Ropp b y -> x = y.
Proof.
intros b x y H.
rewrite <- (cond_Ropp_involutive b x), H.
apply cond_Ropp_involutive.
Qed.

Theorem cond_Ropp_mult_l :
  forall b x y,
  cond_Ropp b (x * y) = (cond_Ropp b x * y)%R.
Proof.
intros [|] x y.
apply sym_eq.
apply Ropp_mult_distr_l_reverse.
apply refl_equal.
Qed.

Theorem cond_Ropp_mult_r :
  forall b x y,
  cond_Ropp b (x * y) = (x * cond_Ropp b y)%R.
Proof.
intros [|] x y.
apply sym_eq.
apply Ropp_mult_distr_r_reverse.
apply refl_equal.
Qed.

Theorem cond_Ropp_plus :
  forall b x y,
  cond_Ropp b (x + y) = (cond_Ropp b x + cond_Ropp b y)%R.
Proof.
intros [|] x y.
apply Ropp_plus_distr.
apply refl_equal.
Qed.

End cond_Ropp.

Theorem LPO_min :
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
  {n : nat | P n /\ forall i, (i < n)%nat -> ~ P i} + {forall n, ~ P n}.
Proof.
assert (Hi: forall n, (0 < INR n + 1)%R).
  intros N.
  rewrite <- S_INR.
  apply lt_0_INR.
  apply Nat.lt_0_succ.
intros P HP.
set (E y := exists n, (P n /\ y = / (INR n + 1))%R \/ (~ P n /\ y = 0)%R).
assert (HE: forall n, P n -> E (/ (INR n + 1))%R).
  intros n Pn.
  exists n.
  left.
  now split.
assert (BE: is_upper_bound E 1).
  intros x [y [[_ ->]|[_ ->]]].
  rewrite <- Rinv_1 at 2.
  apply Rinv_le.
  exact Rlt_0_1.
  rewrite <- S_INR.
  apply (le_INR 1), le_n_S, le_0_n.
  exact Rle_0_1.
destruct (completeness E) as [l [ub lub]].
  now exists 1%R.
  destruct (HP O) as [H0|H0].
  exists 1%R.
  exists O.
  left.
  apply (conj H0).
  rewrite Rplus_0_l.
  apply sym_eq, Rinv_1.
  exists 0%R.
  exists O.
  right.
  now split.
destruct (Rle_lt_dec l 0) as [Hl|Hl].
  right.
  intros n Pn.
  apply Rle_not_lt with (1 := Hl).
  apply Rlt_le_trans with (/ (INR n + 1))%R.
  now apply Rinv_0_lt_compat.
  apply ub.
  now apply HE.
left.
set (N := Z.abs_nat (up (/l) - 2)).
exists N.
assert (HN: (INR N + 1 = IZR (up (/ l)) - 1)%R).
  unfold N.
  rewrite INR_IZR_INZ.
  rewrite inj_Zabs_nat.
  replace (IZR (up (/ l)) - 1)%R with (IZR (up (/ l) - 2) + 1)%R.
  apply (f_equal (fun v => IZR v + 1)%R).
  apply Z.abs_eq.
  apply Zle_minus_le_0.
  apply (Zlt_le_succ 1).
  apply lt_IZR.
  apply Rle_lt_trans with (/l)%R.
  apply Rmult_le_reg_r with (1 := Hl).
  rewrite Rmult_1_l, Rinv_l by now apply Rgt_not_eq.
  apply lub.
  exact BE.
  apply archimed.
  rewrite minus_IZR.
  simpl.
  ring.
assert (H: forall i, (i < N)%nat -> ~ P i).
  intros i HiN Pi.
  unfold is_upper_bound in ub.
  refine (Rle_not_lt _ _ (ub (/ (INR i + 1))%R _) _).
  now apply HE.
  rewrite <- (Rinv_involutive l) by now apply Rgt_not_eq.
  apply Rinv_1_lt_contravar.
  rewrite <- S_INR.
  apply (le_INR 1).
  apply le_n_S.
  apply le_0_n.
  apply Rlt_le_trans with (INR N + 1)%R.
  apply Rplus_lt_compat_r.
  now apply lt_INR.
  rewrite HN.
  apply Rplus_le_reg_r with (-/l + 1)%R.
  ring_simplify.
  apply archimed.
destruct (HP N) as [PN|PN].
  now split.
exfalso.
refine (Rle_not_lt _ _ (lub (/ (INR (S N) + 1))%R _) _).
  intros x [y [[Py ->]|[_ ->]]].
  destruct (eq_nat_dec y N) as [HyN|HyN].
  elim PN.
  now rewrite <- HyN.
  apply Rinv_le.
  apply Hi.
  apply Rplus_le_compat_r.
  apply Rnot_lt_le.
  intros Hy.
  refine (H _ _ Py).
  apply INR_lt in Hy.
  clear -Hy HyN ; lia.
  now apply Rlt_le, Rinv_0_lt_compat.
rewrite S_INR, HN.
ring_simplify (IZR (up (/ l)) - 1 + 1)%R.
rewrite <- (Rinv_involutive l) at 2 by now apply Rgt_not_eq.
apply Rinv_1_lt_contravar.
rewrite <- Rinv_1.
apply Rinv_le.
exact Hl.
now apply lub.
apply archimed.
Qed.

Theorem LPO :
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
  {n : nat | P n} + {forall n, ~ P n}.
Proof.
intros P HP.
destruct (LPO_min P HP) as [[n [Pn _]]|Pn].
left.
now exists n.
now right.
Qed.

Lemma LPO_Z : forall P : Z -> Prop, (forall n, P n \/ ~P n) ->
  {n : Z| P n} + {forall n, ~ P n}.
Proof.
intros P H.
destruct (LPO (fun n => P (Z.of_nat n))) as [J|J].
intros n; apply H.
destruct J as (n, Hn).
left; now exists (Z.of_nat n).
destruct (LPO (fun n => P (-Z.of_nat n)%Z)) as [K|K].
intros n; apply H.
destruct K as (n, Hn).
left; now exists (-Z.of_nat n)%Z.
right; intros n; case (Zle_or_lt 0 n); intros M.
rewrite <- (Z.abs_eq n); trivial.
rewrite <- Zabs2Nat.id_abs.
apply J.
rewrite <- (Z.opp_involutive n).
rewrite <- (Z.abs_neq n).
rewrite <- Zabs2Nat.id_abs.
apply K.
lia.
Qed.

Ltac bpow_simplify :=

  repeat
    match goal with
      | |- context [(bpow _ _ * bpow _ _)] =>
        rewrite <- bpow_plus
      | |- context [(?X1 * bpow _ _ * bpow _ _)] =>
        rewrite (Rmult_assoc X1); rewrite <- bpow_plus
      | |- context [(?X1 * (?X2 * bpow _ _) * bpow _ _)] =>
        rewrite <- (Rmult_assoc X1 X2); rewrite (Rmult_assoc (X1 * X2));
        rewrite <- bpow_plus
    end;

  repeat
    match goal with
      | |- context [(bpow _ ?X)] =>
        progress ring_simplify X
    end;

  change (bpow _ 0) with 1;
  repeat
    match goal with
      | |- context [(_ * 1)] =>
        rewrite Rmult_1_r
    end.

End Raux.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Raux.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_Defs.
Module Export Flocq.
Module Export Core.
Module Export Defs.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals.
Import Flocq.Core.Raux Flocq.Core.Zaux.

Section Def.

Record float (beta : radix) := Float { Fnum : Z ; Fexp : Z }.

Arguments Fnum {beta}.
Arguments Fexp {beta}.

Variable beta : radix.

Definition F2R (f : float beta) :=
  (IZR (Fnum f) * bpow beta (Fexp f))%R.

Definition round_pred_total (P : R -> R -> Prop) :=
  forall x, exists f, P x f.

Definition round_pred_monotone (P : R -> R -> Prop) :=
  forall x y f g, P x f -> P y g -> (x <= y)%R -> (f <= g)%R.

Definition round_pred (P : R -> R -> Prop) :=
  round_pred_total P /\
  round_pred_monotone P.

End Def.

Arguments Fnum {beta}.
Arguments Fexp {beta}.
Arguments F2R {beta}.

Section RND.

Definition Rnd_DN_pt (F : R -> Prop) (x f : R) :=
  F f /\ (f <= x)%R /\
  forall g : R, F g -> (g <= x)%R -> (g <= f)%R.

Definition Rnd_UP_pt (F : R -> Prop) (x f : R) :=
  F f /\ (x <= f)%R /\
  forall g : R, F g -> (x <= g)%R -> (f <= g)%R.

Definition Rnd_ZR_pt (F : R -> Prop) (x f : R) :=
  ( (0 <= x)%R -> Rnd_DN_pt F x f ) /\
  ( (x <= 0)%R -> Rnd_UP_pt F x f ).

Definition Rnd_N_pt (F : R -> Prop) (x f : R) :=
  F f /\
  forall g : R, F g -> (Rabs (f - x) <= Rabs (g - x))%R.

Definition Rnd_NG_pt (F : R -> Prop) (P : R -> R -> Prop) (x f : R) :=
  Rnd_N_pt F x f /\
  ( P x f \/ forall f2 : R, Rnd_N_pt F x f2 -> f2 = f ).

Definition Rnd_NA_pt (F : R -> Prop) (x f : R) :=
  Rnd_N_pt F x f /\
  forall f2 : R, Rnd_N_pt F x f2 -> (Rabs f2 <= Rabs f)%R.

Definition Rnd_N0_pt (F : R -> Prop) (x f : R) :=
  Rnd_N_pt F x f /\
  forall f2 : R, Rnd_N_pt F x f2 -> (Rabs f <= Rabs f2)%R.

End RND.

End Defs.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Defs.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.

Module Export Flocq_DOT_Core_DOT_Digits.
Module Export Flocq.
Module Export Core.
Module Export Digits.

Import Stdlib.micromega.Lia Stdlib.ZArith.ZArith Stdlib.ZArith.Zquot.
Import Flocq.Core.Zaux.

Notation digits2_pos := SpecFloat.digits2_pos (only parsing).
Notation Zdigits2 := SpecFloat.Zdigits2 (only parsing).

Fixpoint digits2_Pnat (n : positive) : nat :=
  match n with
  | xH => O
  | xO p => S (digits2_Pnat p)
  | xI p => S (digits2_Pnat p)
  end.

Theorem digits2_Pnat_correct :
  forall n,
  let d := digits2_Pnat n in
  (Zpower_nat 2 d <= Zpos n < Zpower_nat 2 (S d))%Z.
Proof.
intros n d.
unfold d.
clear.
assert (Hp: forall m, (Zpower_nat 2 (S m) = 2 * Zpower_nat 2 m)%Z) by easy.
induction n ; simpl digits2_Pnat.
rewrite Zpos_xI, 2!Hp.
lia.
rewrite (Zpos_xO n), 2!Hp.
lia.
now split.
Qed.

Section Fcore_digits.

Variable beta : radix.

Definition Zdigit n k := Z.rem (Z.quot n (Zpower beta k)) beta.

Theorem Zdigit_lt :
  forall n k,
  (k < 0)%Z ->
  Zdigit n k = Z0.
Proof using .
intros n [|k|k] Hk ; try easy.
now case n.
Qed.

Theorem Zdigit_0 :
  forall k, Zdigit 0 k = Z0.
Proof using .
intros k.
unfold Zdigit.
rewrite Zquot_0_l.
apply Zrem_0_l.
Qed.

Theorem Zdigit_opp :
  forall n k,
  Zdigit (-n) k = Z.opp (Zdigit n k).
Proof using .
intros n k.
unfold Zdigit.
rewrite Zquot_opp_l.
apply Zrem_opp_l.
Qed.

Theorem Zdigit_ge_Zpower_pos :
  forall e n,
  (0 <= n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof using .
intros e n Hn k Hk.
unfold Zdigit.
rewrite Z.quot_small.
apply Zrem_0_l.
split.
apply Hn.
apply Z.lt_le_trans with (1 := proj2 Hn).
replace k with (e + (k - e))%Z by ring.
rewrite Zpower_plus.
rewrite <- (Zmult_1_r (beta ^ e)) at 1.
apply Zmult_le_compat_l.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zlt_le_weak.
now apply Z.le_lt_trans with n.
generalize (Z.le_lt_trans _ _ _ (proj1 Hn) (proj2 Hn)).
clear.
now destruct e as [|e|e].
now apply Zle_minus_le_0.
Qed.

Theorem Zdigit_ge_Zpower :
  forall e n,
  (Z.abs n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof using .
intros e [|n|n] Hn k.
easy.
apply Zdigit_ge_Zpower_pos.
now split.
intros He.
change (Zneg n) with (Z.opp (Zpos n)).
rewrite Zdigit_opp.
rewrite Zdigit_ge_Zpower_pos with (2 := He).
apply Z.opp_0.
now split.
Qed.

Theorem Zdigit_not_0_pos :
  forall e n, (0 <= e)%Z ->
  (Zpower beta e <= n < Zpower beta (e + 1))%Z ->
  Zdigit n e <> Z0.
Proof using .
intros e n He (Hn1,Hn2).
unfold Zdigit.
rewrite <- ZOdiv_mod_mult.
rewrite Z.rem_small.
intros H.
apply Zle_not_lt with (1 := Hn1).
rewrite (Z.quot_rem' n (beta ^ e)).
rewrite H, Zmult_0_r, Zplus_0_l.
apply Zrem_lt_pos_pos.
apply Z.le_trans with (2 := Hn1).
apply Zpower_ge_0.
now apply Zpower_gt_0.
split.
apply Z.le_trans with (2 := Hn1).
apply Zpower_ge_0.
replace (beta ^ e * beta)%Z with (beta ^ (e + 1))%Z.
exact Hn2.
rewrite <- (Zmult_1_r beta) at 3.
now apply (Zpower_plus beta e 1).
Qed.

Theorem Zdigit_not_0 :
  forall e n, (0 <= e)%Z ->
  (Zpower beta e <= Z.abs n < Zpower beta (e + 1))%Z ->
  Zdigit n e <> Z0.
Proof using .
intros e n He Hn.
destruct (Zle_or_lt 0 n) as [Hn'|Hn'].
rewrite (Z.abs_eq _ Hn') in Hn.
now apply Zdigit_not_0_pos.
intros H.
rewrite (Zabs_non_eq n) in Hn by now apply Zlt_le_weak.
apply (Zdigit_not_0_pos _ _ He Hn).
now rewrite Zdigit_opp, H.
Qed.

Theorem Zdigit_mul_pow :
  forall n k k', (0 <= k')%Z ->
  Zdigit (n * Zpower beta k') k = Zdigit n (k - k').
Proof using .
intros n k k' Hk'.
destruct (Zle_or_lt k' k) as [H|H].
revert k H.
pattern k' ; apply Zlt_0_ind with (2 := Hk').
clear k' Hk'.
intros k' IHk' Hk' k H.
unfold Zdigit.
apply (f_equal (fun x => Z.rem x beta)).
pattern k at 1 ; replace k with (k - k' + k')%Z by ring.
rewrite Zpower_plus with (2 := Hk').
apply Zquot_mult_cancel_r.
apply Zgt_not_eq.
now apply Zpower_gt_0.
now apply Zle_minus_le_0.
destruct (Zle_or_lt 0 k) as [H0|H0].
rewrite (Zdigit_lt n) by lia.
unfold Zdigit.
replace k' with (k' - k + k)%Z by ring.
rewrite Zpower_plus with (2 := H0).
rewrite Zmult_assoc, Z_quot_mult.
replace (k' - k)%Z with (k' - k - 1 + 1)%Z by ring.
rewrite Zpower_exp by lia.
rewrite Zmult_assoc.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply Z_rem_mult.
apply Zgt_not_eq.
now apply Zpower_gt_0.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
rewrite Zdigit_lt with (1 := H0).
apply sym_eq.
apply Zdigit_lt.
lia.
Qed.

Theorem Zdigit_div_pow :
  forall n k k', (0 <= k)%Z -> (0 <= k')%Z ->
  Zdigit (Z.quot n (Zpower beta k')) k = Zdigit n (k + k').
Proof using .
intros n k k' Hk Hk'.
unfold Zdigit.
rewrite Zquot_Zquot.
rewrite Zplus_comm.
now rewrite Zpower_plus.
Qed.

Theorem Zdigit_mod_pow :
  forall n k k', (k < k')%Z ->
  Zdigit (Z.rem n (Zpower beta k')) k = Zdigit n k.
Proof using .
intros n k k' Hk.
destruct (Zle_or_lt 0 k) as [H|H].
unfold Zdigit.
rewrite <- 2!ZOdiv_mod_mult.
apply (f_equal (fun x => Z.quot x (beta ^ k))).
replace k' with (k + 1 + (k' - (k + 1)))%Z by ring.
rewrite Zpower_exp by lia.
rewrite Zmult_comm.
rewrite Zpower_plus by easy.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply ZOmod_mod_mult.
now rewrite 2!Zdigit_lt.
Qed.

Theorem Zdigit_mod_pow_out :
  forall n k k', (0 <= k' <= k)%Z ->
  Zdigit (Z.rem n (Zpower beta k')) k = Z0.
Proof using .
intros n k k' Hk.
unfold Zdigit.
rewrite ZOdiv_small_abs.
apply Zrem_0_l.
apply Z.lt_le_trans with (Zpower beta k').
rewrite <- (Z.abs_eq (beta ^ k')) at 2 by apply Zpower_ge_0.
apply Zrem_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
now apply Zpower_le.
Qed.

Fixpoint Zsum_digit f k :=
  match k with
  | O => Z0
  | S k => (Zsum_digit f k + f (Z_of_nat k) * Zpower beta (Z_of_nat k))%Z
  end.

Theorem Zsum_digit_digit :
  forall n k,
  Zsum_digit (Zdigit n) k = Z.rem n (Zpower beta (Z_of_nat k)).
Proof using .
intros n.
induction k.
apply sym_eq.
apply Z.rem_1_r.
simpl Zsum_digit.
rewrite IHk.
unfold Zdigit.
rewrite <- ZOdiv_mod_mult.
rewrite <- (ZOmod_mod_mult n beta).
rewrite Zmult_comm.
replace (beta ^ Z_of_nat k * beta)%Z with (Zpower beta (Z_of_nat (S k))).
rewrite Zplus_comm, Zmult_comm.
apply sym_eq.
apply Z.quot_rem'.
rewrite inj_S.
rewrite <- (Zmult_1_r beta) at 3.
apply Zpower_plus.
apply Zle_0_nat.
easy.
Qed.

Theorem Zdigit_ext :
  forall n1 n2,
  (forall k, (0 <= k)%Z -> Zdigit n1 k = Zdigit n2 k) ->
  n1 = n2.
Proof using .
intros n1 n2 H.
rewrite <- (ZOmod_small_abs n1 (Zpower beta (Z.max (Z.abs n1) (Z.abs n2)))).
rewrite <- (ZOmod_small_abs n2 (Zpower beta (Z.max (Z.abs n1) (Z.abs n2)))) at 2.
replace (Z.max (Z.abs n1) (Z.abs n2)) with (Z_of_nat (Z.abs_nat (Z.max (Z.abs n1) (Z.abs n2)))).
rewrite <- 2!Zsum_digit_digit.
induction (Z.abs_nat (Z.max (Z.abs n1) (Z.abs n2))).
easy.
simpl.
rewrite H, IHn.
apply refl_equal.
apply Zle_0_nat.
rewrite inj_Zabs_nat.
apply Z.abs_eq.
apply Z.le_trans with (Z.abs n1).
apply Zabs_pos.
apply Z.le_max_l.
apply Z.lt_le_trans with (Zpower beta (Z.abs n2)).
apply Zpower_gt_id.
apply Zpower_le.
apply Z.le_max_r.
apply Z.lt_le_trans with (Zpower beta (Z.abs n1)).
apply Zpower_gt_id.
apply Zpower_le.
apply Z.le_max_l.
Qed.

Theorem ZOmod_plus_pow_digit :
  forall u v n, (0 <= u * v)%Z ->
  (forall k, (0 <= k < n)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  Z.rem (u + v) (Zpower beta n) = (Z.rem u (Zpower beta n) + Z.rem v (Zpower beta n))%Z.
Proof using .
intros u v n Huv Hd.
destruct (Zle_or_lt 0 n) as [Hn|Hn].
rewrite Zplus_rem with (1 := Huv).
apply ZOmod_small_abs.
generalize (Z.le_refl n).
pattern n at -2 ; rewrite <- Z.abs_eq with (1 := Hn).
rewrite <- (inj_Zabs_nat n).
induction (Z.abs_nat n) as [|p IHp].
now rewrite 2!Z.rem_1_r.
rewrite <- 2!Zsum_digit_digit.
simpl Zsum_digit.
rewrite inj_S.
intros Hn'.
replace (Zsum_digit (Zdigit u) p + Zdigit u (Z_of_nat p) * beta ^ Z_of_nat p +
  (Zsum_digit (Zdigit v) p + Zdigit v (Z_of_nat p) * beta ^ Z_of_nat p))%Z with
  (Zsum_digit (Zdigit u) p + Zsum_digit (Zdigit v) p +
  (Zdigit u (Z_of_nat p) + Zdigit v (Z_of_nat p)) * beta ^ Z_of_nat p)%Z by ring.
apply (Z.le_lt_trans _ _ _ (Z.abs_triangle _ _)).
replace (beta ^ Z.succ (Z_of_nat p))%Z with (beta ^ Z_of_nat p + (beta - 1) * beta ^ Z_of_nat p)%Z.
apply Zplus_lt_le_compat.
rewrite 2!Zsum_digit_digit.
apply IHp.
now apply Zle_succ_le.
rewrite Zabs_Zmult.
rewrite (Z.abs_eq (beta ^ Z_of_nat p)) by apply Zpower_ge_0.
apply Zmult_le_compat_r.
2: apply Zpower_ge_0.
apply Zlt_succ_le.
assert (forall u v, Z.abs (Zdigit u v) < Z.succ (beta -  1))%Z.
clear ; intros n k.
assert (0 < beta)%Z.
apply Z.lt_le_trans with 2%Z.
apply refl_equal.
apply Zle_bool_imp_le.
apply beta.
replace (Z.succ (beta - 1)) with (Z.abs beta).
apply Zrem_lt.
now apply Zgt_not_eq.
rewrite Z.abs_eq.
apply Zsucc_pred.
now apply Zlt_le_weak.
assert (0 <= Z_of_nat p < n)%Z.
split.
apply Zle_0_nat.
apply Z.gt_lt.
now apply Zle_succ_gt.
destruct (Hd (Z_of_nat p) H0) as [K|K] ; rewrite K.
apply H.
rewrite Zplus_0_r.
apply H.
unfold Z.succ.
ring_simplify.
rewrite Zpower_plus.
change (beta ^1)%Z with (beta * 1)%Z.
now rewrite Zmult_1_r.
apply Zle_0_nat.
easy.
destruct n as [|n|n] ; try easy.
now rewrite 3!Zrem_0_r.
Qed.

Theorem ZOdiv_plus_pow_digit :
  forall u v n, (0 <= u * v)%Z ->
  (forall k, (0 <= k < n)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  Z.quot (u + v) (Zpower beta n) = (Z.quot u (Zpower beta n) + Z.quot v (Zpower beta n))%Z.
Proof using .
intros u v n Huv Hd.
rewrite <- (Zplus_0_r (Z.quot u (Zpower beta n) + Z.quot v (Zpower beta n))).
rewrite ZOdiv_plus with (1 := Huv).
rewrite <- ZOmod_plus_pow_digit by assumption.
apply f_equal.
destruct (Zle_or_lt 0 n) as [Hn|Hn].
apply ZOdiv_small_abs.
rewrite <- Z.abs_eq.
apply Zrem_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
apply Zpower_ge_0.
clear -Hn.
destruct n as [|n|n] ; try easy.
apply Zquot_0_r.
Qed.

Theorem Zdigit_plus :
  forall u v, (0 <= u * v)%Z ->
  (forall k, (0 <= k)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  forall k,
  Zdigit (u + v) k = (Zdigit u k + Zdigit v k)%Z.
Proof using .
intros u v Huv Hd k.
destruct (Zle_or_lt 0 k) as [Hk|Hk].
unfold Zdigit.
rewrite ZOdiv_plus_pow_digit with (1 := Huv).
rewrite <- (Zmult_1_r beta) at 3 5 7.
change (beta * 1)%Z with (beta ^1)%Z.
apply ZOmod_plus_pow_digit.
apply Zsame_sign_trans_weak with v.
intros Zv ; rewrite Zv.
apply Zquot_0_l.
rewrite Zmult_comm.
apply Zsame_sign_trans_weak with u.
intros Zu ; rewrite Zu.
apply Zquot_0_l.
now rewrite Zmult_comm.
apply Zsame_sign_odiv.
apply Zpower_ge_0.
apply Zsame_sign_odiv.
apply Zpower_ge_0.
intros k' (Hk1,Hk2).
rewrite 2!Zdigit_div_pow by assumption.
apply Hd.
now apply Zplus_le_0_compat.
intros k' (Hk1,Hk2).
now apply Hd.
now rewrite 3!Zdigit_lt.
Qed.

Definition Zscale n k :=
  if Zle_bool 0 k then (n * Zpower beta k)%Z else Z.quot n (Zpower beta (-k)).

Theorem Zdigit_scale :
  forall n k k', (0 <= k')%Z ->
  Zdigit (Zscale n k) k' = Zdigit n (k' - k).
Proof using .
intros n k k' Hk'.
unfold Zscale.
case Zle_bool_spec ; intros Hk.
now apply Zdigit_mul_pow.
apply Zdigit_div_pow with (1 := Hk').
lia.
Qed.

Theorem Zscale_0 :
  forall k,
  Zscale 0 k = Z0.
Proof using .
intros k.
unfold Zscale.
case Zle_bool.
apply Zmult_0_l.
apply Zquot_0_l.
Qed.

Theorem Zsame_sign_scale :
  forall n k,
  (0 <= n * Zscale n k)%Z.
Proof using .
intros n k.
unfold Zscale.
case Zle_bool_spec ; intros Hk.
rewrite Zmult_assoc.
apply Zmult_le_0_compat.
apply Zsame_sign_imp ; apply Zlt_le_weak.
apply Zpower_ge_0.
apply Zsame_sign_odiv.
apply Zpower_ge_0.
Qed.

Theorem Zscale_mul_pow :
  forall n k k', (0 <= k)%Z ->
  Zscale (n * Zpower beta k) k' = Zscale n (k + k').
Proof using .
intros n k k' Hk.
unfold Zscale.
case Zle_bool_spec ; intros Hk'.
rewrite Zle_bool_true.
rewrite <- Zmult_assoc.
apply f_equal.
now rewrite Zpower_plus.
now apply Zplus_le_0_compat.
case Zle_bool_spec ; intros Hk''.
pattern k at 1 ; replace k with (k + k' + -k')%Z by ring.
assert (0 <= -k')%Z by lia.
rewrite Zpower_plus by easy.
rewrite Zmult_assoc, Z_quot_mult.
apply refl_equal.
apply Zgt_not_eq.
now apply Zpower_gt_0.
replace (-k')%Z with (-(k+k') + k)%Z by ring.
rewrite Zpower_plus with (2 := Hk).
apply Zquot_mult_cancel_r.
apply Zgt_not_eq.
now apply Zpower_gt_0.
lia.
Qed.

Theorem Zscale_scale :
  forall n k k', (0 <= k)%Z ->
  Zscale (Zscale n k) k' = Zscale n (k + k').
Proof using .
intros n k k' Hk.
unfold Zscale at 2.
rewrite Zle_bool_true with (1 := Hk).
now apply Zscale_mul_pow.
Qed.

Definition Zslice n k1 k2 :=
  if Zle_bool 0 k2 then Z.rem (Zscale n (-k1)) (Zpower beta k2) else Z0.

Theorem Zdigit_slice :
  forall n k1 k2 k, (0 <= k < k2)%Z ->
  Zdigit (Zslice n k1 k2) k = Zdigit n (k1 + k).
Proof using .
intros n k1 k2 k Hk.
unfold Zslice.
rewrite Zle_bool_true.
rewrite Zdigit_mod_pow by apply Hk.
rewrite Zdigit_scale by apply Hk.
unfold Zminus.
now rewrite Z.opp_involutive, Zplus_comm.
lia.
Qed.

Theorem Zdigit_slice_out :
  forall n k1 k2 k, (k2 <= k)%Z ->
  Zdigit (Zslice n k1 k2) k = Z0.
Proof using .
intros n k1 k2 k Hk.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
apply Zdigit_mod_pow_out.
now split.
apply Zdigit_0.
Qed.

Theorem Zslice_0 :
  forall k k',
  Zslice 0 k k' = Z0.
Proof using .
intros k k'.
unfold Zslice.
case Zle_bool.
rewrite Zscale_0.
apply Zrem_0_l.
apply refl_equal.
Qed.

Theorem Zsame_sign_slice :
  forall n k k',
  (0 <= n * Zslice n k k')%Z.
Proof using .
intros n k k'.
unfold Zslice.
case Zle_bool.
apply Zsame_sign_trans_weak with (Zscale n (-k)).
intros H ; rewrite H.
apply Zrem_0_l.
apply Zsame_sign_scale.
rewrite Zmult_comm.
apply Zrem_sgn2.
now rewrite Zmult_0_r.
Qed.

Theorem Zslice_slice :
  forall n k1 k2 k1' k2', (0 <= k1' <= k2)%Z ->
  Zslice (Zslice n k1 k2) k1' k2' = Zslice n (k1 + k1') (Z.min (k2 - k1') k2').
Proof using .
intros n k1 k2 k1' k2' Hk1'.
destruct (Zle_or_lt 0 k2') as [Hk2'|Hk2'].
apply Zdigit_ext.
intros k Hk.
destruct (Zle_or_lt (Z.min (k2 - k1') k2') k) as [Hk'|Hk'].
rewrite (Zdigit_slice_out n (k1 + k1')) with (1 := Hk').
destruct (Zle_or_lt k2' k) as [Hk''|Hk''].
now apply Zdigit_slice_out.
rewrite Zdigit_slice by now split.
apply Zdigit_slice_out.
lia.
rewrite Zdigit_slice by lia.
rewrite (Zdigit_slice n (k1 + k1')) by now split.
rewrite Zdigit_slice.
now rewrite Zplus_assoc.
lia.
unfold Zslice.
rewrite Z.min_r.
now rewrite Zle_bool_false.
lia.
Qed.

Theorem Zslice_mul_pow :
  forall n k k1 k2, (0 <= k)%Z ->
  Zslice (n * Zpower beta k) k1 k2 = Zslice n (k1 - k) k2.
Proof using .
intros n k k1 k2 Hk.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
2: apply refl_equal.
rewrite Zscale_mul_pow with (1 := Hk).
now replace (- (k1 - k))%Z with (k + -k1)%Z by ring.
Qed.

Theorem Zslice_div_pow :
  forall n k k1 k2, (0 <= k)%Z -> (0 <= k1)%Z ->
  Zslice (Z.quot n (Zpower beta k)) k1 k2 = Zslice n (k1 + k) k2.
Proof using .
intros n k k1 k2 Hk Hk1.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
2: apply refl_equal.
apply (f_equal (fun x => Z.rem x (beta ^ k2))).
unfold Zscale.
case Zle_bool_spec ; intros Hk1'.
replace k1 with Z0 by lia.
case Zle_bool_spec ; intros Hk'.
replace k with Z0 by lia.
simpl.
now rewrite Z.quot_1_r.
rewrite Z.opp_involutive.
apply Zmult_1_r.
rewrite Zle_bool_false by lia.
rewrite 2!Z.opp_involutive, Zplus_comm.
rewrite Zpower_plus by assumption.
apply Zquot_Zquot.
Qed.

Theorem Zslice_scale :
  forall n k k1 k2, (0 <= k1)%Z ->
  Zslice (Zscale n k) k1 k2 = Zslice n (k1 - k) k2.
Proof using .
intros n k k1 k2 Hk1.
unfold Zscale.
case Zle_bool_spec; intros Hk.
now apply Zslice_mul_pow.
apply Zslice_div_pow with (2 := Hk1).
lia.
Qed.

Theorem Zslice_div_pow_scale :
  forall n k k1 k2, (0 <= k)%Z ->
  Zslice (Z.quot n (Zpower beta k)) k1 k2 = Zscale (Zslice n k (k1 + k2)) (-k1).
Proof using .
intros n k k1 k2 Hk.
apply Zdigit_ext.
intros k' Hk'.
rewrite Zdigit_scale with (1 := Hk').
unfold Zminus.
rewrite (Zplus_comm k'), Z.opp_involutive.
destruct (Zle_or_lt k2 k') as [Hk2|Hk2].
rewrite Zdigit_slice_out with (1 := Hk2).
apply sym_eq.
apply Zdigit_slice_out.
now apply Zplus_le_compat_l.
rewrite Zdigit_slice by now split.
destruct (Zle_or_lt 0 (k1 + k')) as [Hk1'|Hk1'].
rewrite Zdigit_slice by lia.
rewrite Zdigit_div_pow by assumption.
apply f_equal.
ring.
now rewrite 2!Zdigit_lt.
Qed.

Theorem Zplus_slice :
  forall n k l1 l2, (0 <= l1)%Z -> (0 <= l2)%Z ->
  (Zslice n k l1 + Zscale (Zslice n (k + l1) l2) l1)%Z = Zslice n k (l1 + l2).
Proof using .
intros n k1 l1 l2 Hl1 Hl2.
clear Hl1.
apply Zdigit_ext.
intros k Hk.
rewrite Zdigit_plus.
rewrite Zdigit_scale with (1 := Hk).
destruct (Zle_or_lt (l1 + l2) k) as [Hk2|Hk2].
rewrite Zdigit_slice_out with (1 := Hk2).
now rewrite 2!Zdigit_slice_out by lia.
rewrite Zdigit_slice with (1 := conj Hk Hk2).
destruct (Zle_or_lt l1 k) as [Hk1|Hk1].
rewrite Zdigit_slice_out with (1 := Hk1).
rewrite Zdigit_slice by lia.
simpl ; apply f_equal.
ring.
rewrite Zdigit_slice with (1 := conj Hk Hk1).
rewrite (Zdigit_lt _ (k - l1)) by lia.
apply Zplus_0_r.
rewrite Zmult_comm.
apply Zsame_sign_trans_weak with n.
intros H ; rewrite H.
apply Zslice_0.
rewrite Zmult_comm.
apply Zsame_sign_trans_weak with (Zslice n (k1 + l1) l2).
intros H ; rewrite H.
apply Zscale_0.
apply Zsame_sign_slice.
apply Zsame_sign_scale.
apply Zsame_sign_slice.
clear k Hk ; intros k Hk.
rewrite Zdigit_scale with (1 := Hk).
destruct (Zle_or_lt l1 k) as [Hk1|Hk1].
left.
now apply Zdigit_slice_out.
right.
apply Zdigit_lt.
lia.
Qed.

Section digits_aux.

Variable p : Z.

Fixpoint Zdigits_aux (nb pow : Z) (n : nat) { struct n } : Z :=
  match n with
  | O => nb
  | S n => if Zlt_bool p pow then nb else Zdigits_aux (nb + 1) (Zmult beta pow) n
  end.

End digits_aux.

Definition Zdigits n :=
  match n with
  | Z0 => Z0
  | Zneg p => Zdigits_aux (Zpos p) 1 beta (digits2_Pnat p)
  | Zpos p => Zdigits_aux n 1 beta (digits2_Pnat p)
  end.

Theorem Zdigits_correct :
  forall n,
  (Zpower beta (Zdigits n - 1) <= Z.abs n < Zpower beta (Zdigits n))%Z.
Proof using .
cut (forall p, Zpower beta (Zdigits (Zpos p) - 1) <= Zpos p < Zpower beta (Zdigits (Zpos p)))%Z.
intros H [|n|n] ; try exact (H n).
now split.
intros n.
simpl.

assert (U: (Zpos n < Zpower beta (Z_of_nat (S (digits2_Pnat n))))%Z).
apply Z.lt_le_trans with (1 := proj2 (digits2_Pnat_correct n)).
rewrite Zpower_Zpower_nat.
rewrite Zabs_nat_Z_of_nat.
induction (S (digits2_Pnat n)).
easy.
rewrite 2!(Zpower_nat_S).
apply Zmult_le_compat with (2 := IHn0).
apply Zle_bool_imp_le.
apply beta.
easy.
rewrite <- (Zabs_nat_Z_of_nat n0).
rewrite <- Zpower_Zpower_nat.
apply (Zpower_ge_0 (Build_radix 2 (refl_equal true))).
apply Zle_0_nat.
apply Zle_0_nat.

revert U.
rewrite inj_S.
unfold Z.succ.
generalize (digits2_Pnat n).
intros u U.
pattern (radix_val beta) at 2 4 ; replace (radix_val beta) with (Zpower beta 1) by apply Zmult_1_r.
assert (V: (Zpower beta (1 - 1) <= Zpos n)%Z).
now apply (Zlt_le_succ 0).
generalize (conj V U).
clear.
generalize (Z.le_refl 1).
generalize 1%Z at 2 3 5 6 7 9 10.

induction u.
easy.
rewrite inj_S; unfold Z.succ.
simpl Zdigits_aux.
intros v Hv U.
case Zlt_bool_spec ; intros K.
now split.
pattern (radix_val beta) at 2 5 ; replace (radix_val beta) with (Zpower beta 1) by apply Zmult_1_r.
rewrite <- Zpower_plus.
rewrite Zplus_comm.
apply IHu.
clear -Hv ; lia.
split.
now ring_simplify (1 + v - 1)%Z.
now rewrite Zplus_assoc.
easy.
apply Zle_succ_le with (1 := Hv).
Qed.

Theorem Zdigits_unique :
  forall n d,
  (Zpower beta (d - 1) <= Z.abs n < Zpower beta d)%Z ->
  Zdigits n = d.
Proof using .
intros n d Hd.
assert (Hd' := Zdigits_correct n).
apply Zle_antisym.
apply (Zpower_lt_Zpower beta).
now apply Z.le_lt_trans with (Z.abs n).
apply (Zpower_lt_Zpower beta).
now apply Z.le_lt_trans with (Z.abs n).
Qed.

Theorem Zdigits_abs :
  forall n, Zdigits (Z.abs n) = Zdigits n.
Proof using .
now intros [|n|n].
Qed.

Theorem Zdigits_opp :
  forall n, Zdigits (Z.opp n) = Zdigits n.
Proof using .
now intros [|n|n].
Qed.

Theorem Zdigits_cond_Zopp :
  forall s n, Zdigits (cond_Zopp s n) = Zdigits n.
Proof using .
now intros [|] [|n|n].
Qed.

Theorem Zdigits_gt_0 :
  forall n, n <> Z0 -> (0 < Zdigits n)%Z.
Proof using .
intros n Zn.
rewrite <- (Zdigits_abs n).
assert (Hn: (0 < Z.abs n)%Z).
destruct n ; [|easy|easy].
now elim Zn.
destruct (Z.abs n) as [|p|p] ; try easy ; clear.
simpl.
generalize 1%Z (radix_val beta) (refl_equal Lt : (0 < 1)%Z).
induction (digits2_Pnat p).
easy.
simpl.
intros.
case Zlt_bool.
exact H.
apply IHn.
now apply Zlt_lt_succ.
Qed.

Theorem Zdigits_ge_0 :
  forall n, (0 <= Zdigits n)%Z.
Proof using .
intros n.
destruct (Z.eq_dec n 0) as [H|H].
now rewrite H.
apply Zlt_le_weak.
now apply Zdigits_gt_0.
Qed.

Theorem Zdigit_out :
  forall n k, (Zdigits n <= k)%Z ->
  Zdigit n k = Z0.
Proof using .
intros n k Hk.
apply Zdigit_ge_Zpower with (2 := Hk).
apply Zdigits_correct.
Qed.

Theorem Zdigit_digits :
  forall n, n <> Z0 ->
  Zdigit n (Zdigits n - 1) <> Z0.
Proof using .
intros n Zn.
apply Zdigit_not_0.
apply Zlt_0_le_0_pred.
now apply Zdigits_gt_0.
ring_simplify (Zdigits n - 1 + 1)%Z.
apply Zdigits_correct.
Qed.

Theorem Zdigits_slice :
  forall n k l, (0 <= l)%Z ->
  (Zdigits (Zslice n k l) <= l)%Z.
Proof using .
intros n k l Hl.
unfold Zslice.
rewrite Zle_bool_true with (1 := Hl).
destruct (Zdigits_correct (Z.rem (Zscale n (- k)) (Zpower beta l))) as (H1,H2).
apply Zpower_lt_Zpower with beta.
apply Z.le_lt_trans with (1 := H1).
rewrite <- (Z.abs_eq (beta ^ l)) at 2 by apply Zpower_ge_0.
apply Zrem_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
Qed.

Theorem Zdigits_mult_Zpower :
  forall m e,
  m <> Z0 -> (0 <= e)%Z ->
  Zdigits (m * Zpower beta e) = (Zdigits m + e)%Z.
Proof using .
intros m e Hm He.
assert (H := Zdigits_correct m).
apply Zdigits_unique.
rewrite Z.abs_mul, Z.abs_pow, (Z.abs_eq beta).
2: now apply Zlt_le_weak, radix_gt_0.
split.
replace (Zdigits m + e - 1)%Z with (Zdigits m - 1 + e)%Z by ring.
rewrite Zpower_plus with (2 := He).
apply Zmult_le_compat_r.
apply H.
apply Zpower_ge_0.
now apply Zlt_0_le_0_pred, Zdigits_gt_0.
rewrite Zpower_plus with (2 := He).
apply Zmult_lt_compat_r.
now apply Zpower_gt_0.
apply H.
now apply Zlt_le_weak, Zdigits_gt_0.
Qed.

Theorem Zdigits_Zpower :
  forall e,
  (0 <= e)%Z ->
  Zdigits (Zpower beta e) = (e + 1)%Z.
Proof using .
intros e He.
rewrite <- (Zmult_1_l (Zpower beta e)).
rewrite Zdigits_mult_Zpower ; try easy.
apply Zplus_comm.
Qed.

Theorem Zdigits_le :
  forall x y,
  (0 <= x)%Z -> (x <= y)%Z ->
  (Zdigits x <= Zdigits y)%Z.
Proof using .
intros x y Zx Hxy.
assert (Hx := Zdigits_correct x).
assert (Hy := Zdigits_correct y).
apply (Zpower_lt_Zpower beta).
lia.
Qed.

Theorem lt_Zdigits :
  forall x y,
  (0 <= y)%Z ->
  (Zdigits x < Zdigits y)%Z ->
  (x < y)%Z.
Proof using .
intros x y Hy.
cut (y <= x -> Zdigits y <= Zdigits x)%Z.
lia.
now apply Zdigits_le.
Qed.

Theorem Zpower_le_Zdigits :
  forall e x,
  (e < Zdigits x)%Z ->
  (Zpower beta e <= Z.abs x)%Z.
Proof using .
intros e x Hex.
destruct (Zdigits_correct x) as [H1 H2].
apply Z.le_trans with (2 := H1).
apply Zpower_le.
clear -Hex ; lia.
Qed.

Theorem Zdigits_le_Zpower :
  forall e x,
  (Z.abs x < Zpower beta e)%Z ->
  (Zdigits x <= e)%Z.
Proof using .
intros e x.
generalize (Zpower_le_Zdigits e x).
lia.
Qed.

Theorem Zpower_gt_Zdigits :
  forall e x,
  (Zdigits x <= e)%Z ->
  (Z.abs x < Zpower beta e)%Z.
Proof using .
intros e x Hex.
destruct (Zdigits_correct x) as [H1 H2].
apply Z.lt_le_trans with (1 := H2).
now apply Zpower_le.
Qed.

Theorem Zdigits_gt_Zpower :
  forall e x,
  (Zpower beta e <= Z.abs x)%Z ->
  (e < Zdigits x)%Z.
Proof using .
intros e x Hex.
generalize (Zpower_gt_Zdigits e x).
lia.
Qed.

Theorem Zdigits_mult_strong :
  forall x y,
  (0 <= x)%Z -> (0 <= y)%Z ->
  (Zdigits (x + y + x * y) <= Zdigits x + Zdigits y)%Z.
Proof using .
intros x y Hx Hy.
apply Zdigits_le_Zpower.
rewrite Z.abs_eq.
apply Z.lt_le_trans with ((x + 1) * (y + 1))%Z.
ring_simplify.
apply Zle_lt_succ, Z.le_refl.
rewrite Zpower_plus by apply Zdigits_ge_0.
apply Zmult_le_compat.
apply Zlt_le_succ.
rewrite <- (Z.abs_eq x) at 1 by easy.
apply Zdigits_correct.
apply Zlt_le_succ.
rewrite <- (Z.abs_eq y) at 1 by easy.
apply Zdigits_correct.
clear -Hx ; lia.
clear -Hy ; lia.
change Z0 with (0 + 0 + 0)%Z.
apply Zplus_le_compat.
now apply Zplus_le_compat.
now apply Zmult_le_0_compat.
Qed.

Theorem Zdigits_mult :
  forall x y,
  (Zdigits (x * y) <= Zdigits x + Zdigits y)%Z.
Proof using .
intros x y.
rewrite <- Zdigits_abs.
rewrite <- (Zdigits_abs x).
rewrite <- (Zdigits_abs y).
apply Z.le_trans with (Zdigits (Z.abs x + Z.abs y + Z.abs x * Z.abs y)).
apply Zdigits_le.
apply Zabs_pos.
rewrite Zabs_Zmult.
generalize (Zabs_pos x) (Zabs_pos y).
lia.
apply Zdigits_mult_strong ; apply Zabs_pos.
Qed.

Theorem Zdigits_mult_ge :
  forall x y,
  (x <> 0)%Z -> (y <> 0)%Z ->
  (Zdigits x + Zdigits y - 1 <= Zdigits (x * y))%Z.
Proof using .
intros x y Zx Zy.
cut ((Zdigits x - 1) + (Zdigits y - 1) < Zdigits (x * y))%Z.
lia.
apply Zdigits_gt_Zpower.
rewrite Zabs_Zmult.
rewrite Zpower_exp.
apply Zmult_le_compat.
apply Zpower_le_Zdigits.
apply Zlt_pred.
apply Zpower_le_Zdigits.
apply Zlt_pred.
apply Zpower_ge_0.
apply Zpower_ge_0.
generalize (Zdigits_gt_0 x).
lia.
generalize (Zdigits_gt_0 y).
lia.
Qed.

Theorem Zdigits_div_Zpower :
  forall m e,
  (0 <= m)%Z ->
  (0 <= e <= Zdigits m)%Z ->
  Zdigits (m / Zpower beta e) = (Zdigits m - e)%Z.
Proof using .
intros m e Hm He.
assert (H := Zdigits_correct m).
apply Zdigits_unique.
destruct (Zle_lt_or_eq _ _ (proj2 He)) as [He'|He'].
  rewrite Z.abs_eq in H by easy.
  destruct H as [H1 H2].
  rewrite Z.abs_eq.
  split.
  replace (Zdigits m - e - 1)%Z with (Zdigits m - 1 - e)%Z by ring.
  rewrite Z.pow_sub_r.
  2: apply Zgt_not_eq, radix_gt_0.
  2: clear -He He' ; lia.
  apply Z_div_le with (2 := H1).
  now apply Z.lt_gt, Zpower_gt_0.
  apply Zmult_lt_reg_r with (Zpower beta e).
  now apply Zpower_gt_0.
  apply Z.le_lt_trans with m.
  rewrite Zmult_comm.
  apply Z_mult_div_ge.
  now apply Z.lt_gt, Zpower_gt_0.
  rewrite <- Zpower_plus.
  now replace (Zdigits m - e + e)%Z with (Zdigits m) by ring.
  now apply Zle_minus_le_0.
  apply He.
  apply Z_div_pos with (2 := Hm).
  now apply Z.lt_gt, Zpower_gt_0.
rewrite He'.
rewrite (Zeq_minus _ (Zdigits m)) by reflexivity.
simpl.
rewrite Zdiv_small.
easy.
split.
exact Hm.
now rewrite <- (Z.abs_eq m) at 1.
Qed.

Theorem Zdigits_succ_le :
  forall x, (0 <= x)%Z ->
  (Zdigits (x + 1) <= Zdigits x + 1)%Z.
Proof using .
  intros [|p|p]; try easy.
  intros _.
  rewrite <- Zdigits_mult_Zpower by easy.
  apply Zdigits_le.
easy.
  apply Z.le_trans with (Z.pos p * 2)%Z.
  lia.
  apply Zmult_le_compat_l.
2: easy.
  rewrite Z.pow_1_r.
  apply (Zlt_le_succ 1), radix_gt_1.
Qed.

End Fcore_digits.

Section Zdigits2.

Theorem Z_of_nat_S_digits2_Pnat :
  forall m : positive,
  Z_of_nat (S (digits2_Pnat m)) = Zdigits radix2 (Zpos m).
Proof.
intros m.
apply eq_sym, Zdigits_unique.
rewrite <- Zpower_nat_Z.
rewrite Nat2Z.inj_succ.
change (_ - 1)%Z with (Z.pred (Z.succ (Z.of_nat (digits2_Pnat m)))).
rewrite <- Zpred_succ.
rewrite <- Zpower_nat_Z.
apply digits2_Pnat_correct.
Qed.

Theorem Zpos_digits2_pos :
  forall m : positive,
  Zpos (digits2_pos m) = Zdigits radix2 (Zpos m).
Proof.
intros m.
rewrite <- Z_of_nat_S_digits2_Pnat.
unfold Z.of_nat.
apply f_equal.
induction m ; simpl ; try easy ;
  apply f_equal, IHm.
Qed.

Lemma Zdigits2_Zdigits :
  forall n, Zdigits2 n = Zdigits radix2 n.
Proof.
intros [|p|p] ; try easy ;
  apply Zpos_digits2_pos.
Qed.

End Zdigits2.

End Digits.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Digits.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_Float_prop.
Module Export Flocq.
Module Export Core.
Module Export Float_prop.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Digits.

Section Float_prop.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Theorem Rcompare_F2R :
  forall e m1 m2 : Z,
  Rcompare (F2R (Float beta m1 e)) (F2R (Float beta m2 e)) = Z.compare m1 m2.
Proof using .
intros e m1 m2.
unfold F2R.
simpl.
rewrite Rcompare_mult_r.
apply Rcompare_IZR.
apply bpow_gt_0.
Qed.

Theorem le_F2R :
  forall e m1 m2 : Z,
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R ->
  (m1 <= m2)%Z.
Proof using .
intros e m1 m2 H.
apply le_IZR.
apply Rmult_le_reg_r with (bpow e).
apply bpow_gt_0.
exact H.
Qed.

Theorem F2R_le :
  forall m1 m2 e : Z,
  (m1 <= m2)%Z ->
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R.
Proof using .
intros m1 m2 e H.
unfold F2R.
simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply IZR_le.
Qed.

Theorem lt_F2R :
  forall e m1 m2 : Z,
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R ->
  (m1 < m2)%Z.
Proof using .
intros e m1 m2 H.
apply lt_IZR.
apply Rmult_lt_reg_r with (bpow e).
apply bpow_gt_0.
exact H.
Qed.

Theorem F2R_lt :
  forall e m1 m2 : Z,
  (m1 < m2)%Z ->
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R.
Proof using .
intros e m1 m2 H.
unfold F2R.
simpl.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
now apply IZR_lt.
Qed.

Theorem F2R_eq :
  forall e m1 m2 : Z,
  (m1 = m2)%Z ->
  (F2R (Float beta m1 e) = F2R (Float beta m2 e))%R.
Proof using .
intros e m1 m2 H.
now apply (f_equal (fun m => F2R (Float beta m e))).
Qed.

Theorem eq_F2R :
  forall e m1 m2 : Z,
  F2R (Float beta m1 e) = F2R (Float beta m2 e) ->
  m1 = m2.
Proof using .
intros e m1 m2 H.
apply Zle_antisym ;
  apply le_F2R with e ;
  rewrite H ;
  apply Rle_refl.
Qed.

Theorem F2R_Zabs:
  forall m e : Z,
   F2R (Float beta (Z.abs m) e) = Rabs (F2R (Float beta m e)).
Proof using .
intros m e.
unfold F2R.
rewrite Rabs_mult.
rewrite <- abs_IZR.
simpl.
apply f_equal.
apply sym_eq; apply Rabs_right.
apply Rle_ge.
apply bpow_ge_0.
Qed.

Theorem F2R_Zopp :
  forall m e : Z,
  F2R (Float beta (Z.opp m) e) = Ropp (F2R (Float beta m e)).
Proof using .
intros m e.
unfold F2R.
simpl.
rewrite <- Ropp_mult_distr_l_reverse.
now rewrite opp_IZR.
Qed.

Theorem F2R_cond_Zopp :
  forall b m e,
  F2R (Float beta (cond_Zopp b m) e) = cond_Ropp b (F2R (Float beta m e)).
Proof using .
intros [|] m e ; unfold F2R ; simpl.
now rewrite opp_IZR, Ropp_mult_distr_l_reverse.
apply refl_equal.
Qed.

Theorem F2R_0 :
  forall e : Z,
  F2R (Float beta 0 e) = 0%R.
Proof using .
intros e.
unfold F2R.
simpl.
apply Rmult_0_l.
Qed.

Theorem eq_0_F2R :
  forall m e : Z,
  F2R (Float beta m e) = 0%R ->
  m = Z0.
Proof using .
intros m e H.
apply eq_F2R with e.
now rewrite F2R_0.
Qed.

Theorem ge_0_F2R :
  forall m e : Z,
  (0 <= F2R (Float beta m e))%R ->
  (0 <= m)%Z.
Proof using .
intros m e H.
apply le_F2R with e.
now rewrite F2R_0.
Qed.

Theorem le_0_F2R :
  forall m e : Z,
  (F2R (Float beta m e) <= 0)%R ->
  (m <= 0)%Z.
Proof using .
intros m e H.
apply le_F2R with e.
now rewrite F2R_0.
Qed.

Theorem gt_0_F2R :
  forall m e : Z,
  (0 < F2R (Float beta m e))%R ->
  (0 < m)%Z.
Proof using .
intros m e H.
apply lt_F2R with e.
now rewrite F2R_0.
Qed.

Theorem lt_0_F2R :
  forall m e : Z,
  (F2R (Float beta m e) < 0)%R ->
  (m < 0)%Z.
Proof using .
intros m e H.
apply lt_F2R with e.
now rewrite F2R_0.
Qed.

Theorem F2R_ge_0 :
  forall f : float beta,
  (0 <= Fnum f)%Z ->
  (0 <= F2R f)%R.
Proof using .
intros f H.
rewrite <- F2R_0 with (Fexp f).
now apply F2R_le.
Qed.

Theorem F2R_le_0 :
  forall f : float beta,
  (Fnum f <= 0)%Z ->
  (F2R f <= 0)%R.
Proof using .
intros f H.
rewrite <- F2R_0 with (Fexp f).
now apply F2R_le.
Qed.

Theorem F2R_gt_0 :
  forall f : float beta,
  (0 < Fnum f)%Z ->
  (0 < F2R f)%R.
Proof using .
intros f H.
rewrite <- F2R_0 with (Fexp f).
now apply F2R_lt.
Qed.

Theorem F2R_lt_0 :
  forall f : float beta,
  (Fnum f < 0)%Z ->
  (F2R f < 0)%R.
Proof using .
intros f H.
rewrite <- F2R_0 with (Fexp f).
now apply F2R_lt.
Qed.

Theorem F2R_neq_0 :
 forall f : float beta,
  (Fnum f <> 0)%Z ->
  (F2R f <> 0)%R.
Proof using .
intros f H H1.
apply H.
now apply eq_0_F2R with (Fexp f).
Qed.

Lemma Fnum_ge_0: forall (f : float beta),
  (0 <= F2R f)%R -> (0 <= Fnum f)%Z.
Proof using .
intros f H.
case (Zle_or_lt 0 (Fnum f)); trivial.
intros H1; contradict H.
apply Rlt_not_le.
now apply F2R_lt_0.
Qed.

Lemma Fnum_le_0: forall (f : float beta),
  (F2R f <= 0)%R -> (Fnum f <= 0)%Z.
Proof using .
intros f H.
case (Zle_or_lt (Fnum f) 0); trivial.
intros H1; contradict H.
apply Rlt_not_le.
now apply F2R_gt_0.
Qed.

Theorem F2R_bpow :
  forall e : Z,
  F2R (Float beta 1 e) = bpow e.
Proof using .
intros e.
unfold F2R.
simpl.
apply Rmult_1_l.
Qed.

Theorem bpow_le_F2R :
  forall m e : Z,
  (0 < m)%Z ->
  (bpow e <= F2R (Float beta m e))%R.
Proof using .
intros m e H.
rewrite <- F2R_bpow.
apply F2R_le.
now apply (Zlt_le_succ 0).
Qed.

Theorem F2R_p1_le_bpow :
  forall m e1 e2 : Z,
  (0 < m)%Z ->
  (F2R (Float beta m e1) < bpow e2)%R ->
  (F2R (Float beta (m + 1) e1) <= bpow e2)%R.
Proof using .
intros m e1 e2 Hm.
intros H.
assert (He : (e1 <= e2)%Z).

apply (le_bpow beta).
apply Rle_trans with (F2R (Float beta m e1)).
unfold F2R.
simpl.
rewrite <- (Rmult_1_l (bpow e1)) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le.
now apply (Zlt_le_succ 0).
now apply Rlt_le.

revert H.
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite bpow_plus.
unfold F2R.
simpl.
rewrite <- (IZR_Zpower beta (e2 - e1)).
intros H.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_lt_reg_r in H.
apply IZR_le.
apply Zlt_le_succ.
now apply lt_IZR.
apply bpow_gt_0.
now apply Zle_minus_le_0.
Qed.

Theorem bpow_le_F2R_m1 :
  forall m e1 e2 : Z,
  (1 < m)%Z ->
  (bpow e2 < F2R (Float beta m e1))%R ->
  (bpow e2 <= F2R (Float beta (m - 1) e1))%R.
Proof using .
intros m e1 e2 Hm.
case (Zle_or_lt e1 e2); intros He.
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite bpow_plus.
unfold F2R.
simpl.
rewrite <- (IZR_Zpower beta (e2 - e1)).
intros H.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_lt_reg_r in H.
apply IZR_le.
rewrite (Zpred_succ (Zpower _ _)).
apply Zplus_le_compat_r.
apply Zlt_le_succ.
now apply lt_IZR.
apply bpow_gt_0.
now apply Zle_minus_le_0.
intros H.
apply Rle_trans with (1*bpow e1)%R.
rewrite Rmult_1_l.
apply bpow_le.
now apply Zlt_le_weak.
unfold F2R.
simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le.
lia.
Qed.

Theorem F2R_lt_bpow :
  forall f : float beta, forall e',
  (Z.abs (Fnum f) < Zpower beta (e' - Fexp f))%Z ->
  (Rabs (F2R f) < bpow e')%R.
Proof using .
intros (m, e) e' Hm.
rewrite <- F2R_Zabs.
destruct (Zle_or_lt e e') as [He|He].
unfold F2R.
simpl.
apply Rmult_lt_reg_r with (bpow (-e)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- 2!bpow_plus, Zplus_opp_r, Rmult_1_r.
rewrite <-IZR_Zpower.
2: now apply Zle_left.
now apply IZR_lt.
elim Zlt_not_le with (1 := Hm).
simpl.
assert (H: (e' - e < 0)%Z) by lia.
clear -H.
destruct (e' - e)%Z ; try easy.
apply Zabs_pos.
Qed.

Theorem F2R_change_exp :
  forall e' m e : Z,
  (e' <= e)%Z ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e')) e').
Proof using .
intros e' m e He.
unfold F2R.
simpl.
rewrite mult_IZR, IZR_Zpower, Rmult_assoc.
apply f_equal.
pattern e at 1 ; replace e with (e - e' + e')%Z by ring.
apply bpow_plus.
now apply Zle_minus_le_0.
Qed.

Theorem F2R_prec_normalize :
  forall m e e' p : Z,
  (Z.abs m < Zpower beta p)%Z ->
  (bpow (e' - 1)%Z <= Rabs (F2R (Float beta m e)))%R ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e' + p)) (e' - p)).
Proof using .
intros m e e' p Hm Hf.
assert (Hp: (0 <= p)%Z).
destruct p ; try easy.
now elim (Zle_not_lt _ _ (Zabs_pos m)).

replace (e - e' + p)%Z with (e - (e' - p))%Z by ring.
apply F2R_change_exp.
cut (e' - 1 < e + p)%Z.
lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := Hf).
rewrite <- F2R_Zabs, Zplus_comm, bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- IZR_Zpower.
now apply IZR_lt.
exact Hp.
Qed.

Theorem mag_F2R_bounds :
  forall x m e, (0 < m)%Z ->
  (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R ->
  mag beta x = mag beta (F2R (Float beta m e)) :> Z.
Proof using .
intros x m e Hp (Hx,Hx2).
destruct (mag beta (F2R (Float beta m e))) as (ex, He).
simpl.
apply mag_unique.
assert (Hp1: (0 < F2R (Float beta m e))%R).
now apply F2R_gt_0.
specialize (He (Rgt_not_eq _ _ Hp1)).
rewrite Rabs_pos_eq in He.
2: now apply Rlt_le.
destruct He as (He1, He2).
assert (Hx1: (0 < x)%R).
now apply Rlt_le_trans with (2 := Hx).
rewrite Rabs_pos_eq.
2: now apply Rlt_le.
split.
now apply Rle_trans with (1 := He1).
apply Rlt_le_trans with (1 := Hx2).
now apply F2R_p1_le_bpow.
Qed.

Theorem mag_F2R :
  forall m e : Z,
  m <> Z0 ->
  (mag beta (F2R (Float beta m e)) = mag beta (IZR m) + e :> Z)%Z.
Proof using .
intros m e H.
unfold F2R ; simpl.
apply mag_mult_bpow.
now apply IZR_neq.
Qed.

Theorem Zdigits_mag :
  forall n,
  n <> Z0 ->
  Zdigits beta n = mag beta (IZR n).
Proof using .
intros n Hn.
destruct (mag beta (IZR n)) as (e, He) ; simpl.
specialize (He (IZR_neq _ _ Hn)).
rewrite <- abs_IZR in He.
assert (Hd := Zdigits_correct beta n).
assert (Hd' := Zdigits_gt_0 beta n).
apply Zle_antisym ; apply (bpow_lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
rewrite <- IZR_Zpower by lia.
now apply IZR_le.
apply Rle_lt_trans with (1 := proj1 He).
rewrite <- IZR_Zpower by lia.
now apply IZR_lt.
Qed.

Theorem mag_F2R_Zdigits :
  forall m e, m <> Z0 ->
  (mag beta (F2R (Float beta m e)) = Zdigits beta m + e :> Z)%Z.
Proof using .
intros m e Hm.
rewrite mag_F2R with (1 := Hm).
apply (f_equal (fun v => Zplus v e)).
apply sym_eq.
now apply Zdigits_mag.
Qed.

Theorem mag_F2R_bounds_Zdigits :
  forall x m e, (0 < m)%Z ->
  (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R ->
  mag beta x = (Zdigits beta m + e)%Z :> Z.
Proof using .
intros x m e Hm Bx.
apply mag_F2R_bounds with (1 := Hm) in Bx.
rewrite Bx.
apply mag_F2R_Zdigits.
now apply Zgt_not_eq.
Qed.

Theorem float_distribution_pos :
  forall m1 e1 m2 e2 : Z,
  (0 < m1)%Z ->
  (F2R (Float beta m1 e1) < F2R (Float beta m2 e2) < F2R (Float beta (m1 + 1) e1))%R ->
  (e2 < e1)%Z /\ (e1 + mag beta (IZR m1) = e2 + mag beta (IZR m2))%Z.
Proof using .
intros m1 e1 m2 e2 Hp1 (H12, H21).
assert (He: (e2 < e1)%Z).

apply Znot_ge_lt.
intros H0.
elim Rlt_not_le with (1 := H21).
apply Z.ge_le in H0.
apply (F2R_change_exp e1 m2 e2) in H0.
rewrite H0.
apply F2R_le.
apply Zlt_le_succ.
apply (lt_F2R e1).
now rewrite <- H0.

split.
exact He.
rewrite (Zplus_comm e1), (Zplus_comm e2).
assert (Hp2: (0 < m2)%Z).
apply (gt_0_F2R m2 e2).
apply Rlt_trans with (2 := H12).
now apply F2R_gt_0.
rewrite <- 2!mag_F2R.
destruct (mag beta (F2R (Float beta m1 e1))) as (e1', H1).
simpl.
apply sym_eq.
apply mag_unique.
assert (H2 : (bpow (e1' - 1) <= F2R (Float beta m1 e1) < bpow e1')%R).
rewrite <- (Z.abs_eq m1), F2R_Zabs.
apply H1.
apply Rgt_not_eq.
apply Rlt_gt.
now apply F2R_gt_0.
now apply Zlt_le_weak.
clear H1.
rewrite <- F2R_Zabs, Z.abs_eq.
split.
apply Rlt_le.
apply Rle_lt_trans with (2 := H12).
apply H2.
apply Rlt_le_trans with (1 := H21).
now apply F2R_p1_le_bpow.
now apply Zlt_le_weak.
apply sym_not_eq.
now apply Zlt_not_eq.
apply sym_not_eq.
now apply Zlt_not_eq.
Qed.

End Float_prop.

End Float_prop.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Float_prop.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Calc_DOT_Bracket.
Module Export Flocq.
Module Export Calc.
Module Export Bracket.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Float_prop.

Notation location := SpecFloat.location (only parsing).
Notation loc_Exact := SpecFloat.loc_Exact (only parsing).
Notation loc_Inexact := SpecFloat.loc_Inexact (only parsing).

Section Fcalc_bracket.

Variable d u : R.
Hypothesis Hdu : (d < u)%R.

Variable x : R.

Definition inbetween_loc :=
  match Rcompare x d with
  | Gt => loc_Inexact (Rcompare x ((d + u) / 2))
  | _ => loc_Exact
  end.

Inductive inbetween : location -> Prop :=
  | inbetween_Exact : x = d -> inbetween loc_Exact
  | inbetween_Inexact l : (d < x < u)%R -> Rcompare x ((d + u) / 2)%R = l -> inbetween (loc_Inexact l).

Theorem inbetween_spec :
  (d <= x < u)%R -> inbetween inbetween_loc.
Proof using .
intros Hx.
unfold inbetween_loc.
destruct (Rcompare_spec x d) as [H|H|H].
now elim Rle_not_lt with (1 := proj1 Hx).
now constructor.
constructor.
now split.
easy.
Qed.

Theorem inbetween_unique :
  forall l l',
  inbetween l -> inbetween l' -> l = l'.
Proof using .
intros l l' Hl Hl'.
inversion_clear Hl ; inversion_clear Hl'.
apply refl_equal.
rewrite H in H0.
elim Rlt_irrefl with (1 := proj1 H0).
rewrite H1 in H.
elim Rlt_irrefl with (1 := proj1 H).
apply f_equal.
now rewrite <- H0.
Qed.

Section Fcalc_bracket_any.

Variable l : location.

Theorem inbetween_bounds :
  inbetween l ->
  (d <= x < u)%R.
Proof using Hdu.
intros [Hx|l' Hx Hl] ; clear l.
rewrite Hx.
split.
apply Rle_refl.
exact Hdu.
now split ; try apply Rlt_le.
Qed.

Theorem inbetween_bounds_not_Eq :
  inbetween l ->
  l <> loc_Exact ->
  (d < x < u)%R.
Proof using .
intros [Hx|l' Hx Hl] H.
now elim H.
exact Hx.
Qed.

End Fcalc_bracket_any.

Theorem inbetween_distance_inexact :
  forall l,
  inbetween (loc_Inexact l) ->
  Rcompare (x - d) (u - x) = l.
Proof using .
intros l Hl.
inversion_clear Hl as [|l' Hl' Hx].
now rewrite Rcompare_middle.
Qed.

Theorem inbetween_distance_inexact_abs :
  forall l,
  inbetween (loc_Inexact l) ->
  Rcompare (Rabs (d - x)) (Rabs (u - x)) = l.
Proof using Hdu.
intros l Hl.
rewrite Rabs_left1.
rewrite Rabs_pos_eq.
rewrite Ropp_minus_distr.
now apply inbetween_distance_inexact.
apply Rle_0_minus.
apply Rlt_le.
apply (inbetween_bounds _ Hl).
apply Rle_minus.
apply (inbetween_bounds _ Hl).
Qed.

End Fcalc_bracket.

Theorem inbetween_ex :
  forall d u l,
  (d < u)%R ->
  exists x,
  inbetween d u x l.
Proof.
intros d u [|l] Hdu.
exists d.
now constructor.
exists (d + match l with Lt => 1 | Eq => 2 | Gt => 3 end / 4 * (u - d))%R.
constructor.

set (v := (match l with Lt => 1 | Eq => 2 | Gt => 3 end / 4)%R).
assert (0 < v < 1)%R.
split.
unfold v, Rdiv.
apply Rmult_lt_0_compat.
case l ; now apply IZR_lt.
apply Rinv_0_lt_compat.
now apply IZR_lt.
unfold v, Rdiv.
apply Rmult_lt_reg_r with 4%R.
now apply IZR_lt.
rewrite Rmult_assoc, Rinv_l.
rewrite Rmult_1_r, Rmult_1_l.
case l ; now apply IZR_lt.
apply Rgt_not_eq.
now apply IZR_lt.
split.
apply Rplus_lt_reg_r with (d * (v - 1))%R.
ring_simplify.
rewrite Rmult_comm.
now apply Rmult_lt_compat_l.
apply Rplus_lt_reg_l with (-u * v)%R.
replace (- u * v + (d + v * (u - d)))%R with (d * (1 - v))%R by ring.
replace (- u * v + u)%R with (u * (1 - v))%R by ring.
apply Rmult_lt_compat_r.
apply Rplus_lt_reg_r with v.
now ring_simplify.
exact Hdu.

set (v := (match l with Lt => 1 | Eq => 2 | Gt => 3 end)%R).
rewrite <- (Rcompare_plus_r (- (d + u) / 2)).
rewrite <- (Rcompare_mult_r 4).
2: now apply IZR_lt.
replace (((d + u) / 2 + - (d + u) / 2) * 4)%R with ((u - d) * 0)%R by field.
replace ((d + v / 4 * (u - d) + - (d + u) / 2) * 4)%R with ((u - d) * (v - 2))%R by field.
rewrite Rcompare_mult_l.
2: now apply Rlt_Rminus.
rewrite <- (Rcompare_plus_r 2).
ring_simplify (v - 2 + 2)%R (0 + 2)%R.
unfold v.
case l ; apply Rcompare_IZR.
Qed.

Section Fcalc_bracket_step.

Variable start step : R.
Variable nb_steps : Z.
Variable Hstep : (0 < step)%R.

Lemma ordered_steps :
  forall k,
  (start + IZR k * step < start + IZR (k + 1) * step)%R.
Proof using Hstep.
intros k.
apply Rplus_lt_compat_l.
apply Rmult_lt_compat_r.
exact Hstep.
apply IZR_lt.
apply Zlt_succ.
Qed.

Lemma middle_range :
  forall k,
  ((start + (start + IZR k * step)) / 2 = start + (IZR k / 2 * step))%R.
Proof using .
intros k.
field.
Qed.

Hypothesis (Hnb_steps : (1 < nb_steps)%Z).

Lemma inbetween_step_not_Eq :
  forall x k l l',
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  (0 < k < nb_steps)%Z ->
  Rcompare x (start + (IZR nb_steps / 2 * step))%R = l' ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact l').
Proof using Hstep.
intros x k l l' Hx Hk Hl'.
constructor.

assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
split.
apply Rlt_le_trans with (2 := proj1 Hx').
rewrite <- (Rplus_0_r start) at 1.
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
now apply IZR_lt.
exact Hstep.
apply Rlt_le_trans with (1 := proj2 Hx').
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply IZR_le.
lia.

now rewrite middle_range.
Qed.

Theorem inbetween_step_Lo :
  forall x k l,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  (0 < k)%Z -> (2 * k + 1 < nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Lt).
Proof using Hnb_steps Hstep.
intros x k l Hx Hk1 Hk2.
apply inbetween_step_not_Eq with (1 := Hx).
lia.
apply Rcompare_Lt.
assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
apply Rlt_le_trans with (1 := proj2 Hx').
apply Rcompare_not_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
apply Rcompare_not_Lt.
rewrite <- mult_IZR.
apply IZR_le.
lia.
exact Hstep.
Qed.

Theorem inbetween_step_Hi :
  forall x k l,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  (nb_steps < 2 * k)%Z -> (k < nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Gt).
Proof using Hnb_steps Hstep.
intros x k l Hx Hk1 Hk2.
apply inbetween_step_not_Eq with (1 := Hx).
lia.
apply Rcompare_Gt.
assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
apply Rlt_le_trans with (2 := proj1 Hx').
apply Rcompare_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
apply Rcompare_Lt.
rewrite <- mult_IZR.
apply IZR_lt.
lia.
exact Hstep.
Qed.

Theorem inbetween_step_Lo_not_Eq :
  forall x l,
  inbetween start (start + step) x l ->
  l <> loc_Exact ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Lt).
Proof using Hnb_steps Hstep.
intros x l Hx Hl.
assert (Hx' := inbetween_bounds_not_Eq _ _ _ _ Hx Hl).
constructor.

split.
apply Hx'.
apply Rlt_trans with (1 := proj2 Hx').
apply Rplus_lt_compat_l.
rewrite <- (Rmult_1_l step) at 1.
apply Rmult_lt_compat_r.
exact Hstep.
now apply IZR_lt.

apply Rcompare_Lt.
apply Rlt_le_trans with (1 := proj2 Hx').
rewrite middle_range.
apply Rcompare_not_Lt_inv.
rewrite <- (Rmult_1_l step) at 2.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
rewrite Rmult_1_r.
apply Rcompare_not_Lt.
apply IZR_le.
now apply (Zlt_le_succ 1).
exact Hstep.
Qed.

Lemma middle_odd :
  forall k,
  (2 * k + 1 = nb_steps)%Z ->
  (((start + IZR k * step) + (start + IZR (k + 1) * step))/2 = start + IZR nb_steps /2 * step)%R.
Proof using .
intros k Hk.
rewrite <- Hk.
rewrite 2!plus_IZR, mult_IZR.
simpl.
field.
Qed.

Theorem inbetween_step_any_Mi_odd :
  forall x k l,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x (loc_Inexact l) ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact l).
Proof using Hnb_steps Hstep.
intros x k l Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
lia.
inversion_clear Hx as [|l' _ Hl].
now rewrite (middle_odd _ Hk) in Hl.
Qed.

Theorem inbetween_step_Lo_Mi_Eq_odd :
  forall x k,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x loc_Exact ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Lt).
Proof using Hnb_steps Hstep.
intros x k Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
lia.
inversion_clear Hx as [Hl|].
rewrite Hl.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_r.
apply Rcompare_Lt.
rewrite <- mult_IZR.
apply IZR_lt.
rewrite <- Hk.
apply Zlt_succ.
exact Hstep.
Qed.

Theorem inbetween_step_Hi_Mi_even :
  forall x k l,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  l <> loc_Exact ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Gt).
Proof using Hnb_steps Hstep.
intros x k l Hx Hl Hk.
apply inbetween_step_not_Eq with (1 := Hx).
lia.
apply Rcompare_Gt.
assert (Hx' := inbetween_bounds_not_Eq _ _ _ _ Hx Hl).
apply Rle_lt_trans with (2 := proj1 Hx').
apply Rcompare_not_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_r.
rewrite <- mult_IZR.
apply Rcompare_not_Lt.
apply IZR_le.
rewrite Hk.
apply Z.le_refl.
exact Hstep.
Qed.

Theorem inbetween_step_Mi_Mi_even :
  forall x k,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x loc_Exact ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Eq).
Proof using Hnb_steps Hstep.
intros x k Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
lia.
apply Rcompare_Eq.
inversion_clear Hx as [Hx'|].
rewrite Hx', <- Hk, mult_IZR.
field.
Qed.

Definition new_location_even k l :=
  if Zeq_bool k 0 then
    match l with loc_Exact => l | _ => loc_Inexact Lt end
  else
    loc_Inexact
    match Z.compare (2 * k) nb_steps with
    | Lt => Lt
    | Eq => match l with loc_Exact => Eq | _ => Gt end
    | Gt => Gt
    end.

Theorem new_location_even_correct :
  Z.even nb_steps = true ->
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  inbetween start (start + IZR nb_steps * step) x (new_location_even k l).
Proof using Hnb_steps Hstep.
intros He x k l Hk Hx.
unfold new_location_even.
destruct (Zeq_bool_spec k 0) as [Hk0|Hk0].

rewrite Hk0 in Hx.
rewrite Rmult_0_l, Rplus_0_r, Rmult_1_l in Hx.
set (l' := match l with loc_Exact => l | _ => loc_Inexact Lt end).
assert ((l = loc_Exact /\ l' = loc_Exact) \/ (l <> loc_Exact /\ l' = loc_Inexact Lt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
constructor.
rewrite H1 in Hx.
now inversion_clear Hx.
now apply inbetween_step_Lo_not_Eq with (2 := H1).

destruct (Zcompare_spec (2 * k) nb_steps) as [Hk1|Hk1|Hk1].

apply inbetween_step_Lo with (1 := Hx).
lia.
destruct (Zeven_ex nb_steps).
rewrite He in H.
lia.

set (l' := match l with loc_Exact => Eq | _ => Gt end).
assert ((l = loc_Exact /\ l' = Eq) \/ (l <> loc_Exact /\ l' = Gt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
rewrite H1 in Hx.
now apply inbetween_step_Mi_Mi_even with (1 := Hx).
now apply inbetween_step_Hi_Mi_even with (1 := Hx).

apply inbetween_step_Hi with (1 := Hx).
exact Hk1.
apply Hk.
Qed.

Definition new_location_odd k l :=
  if Zeq_bool k 0 then
    match l with loc_Exact => l | _ => loc_Inexact Lt end
  else
    loc_Inexact
    match Z.compare (2 * k + 1) nb_steps with
    | Lt => Lt
    | Eq => match l with loc_Inexact l => l | loc_Exact => Lt end
    | Gt => Gt
    end.

Theorem new_location_odd_correct :
  Z.even nb_steps = false ->
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  inbetween start (start + IZR nb_steps * step) x (new_location_odd k l).
Proof using Hnb_steps Hstep.
intros Ho x k l Hk Hx.
unfold new_location_odd.
destruct (Zeq_bool_spec k 0) as [Hk0|Hk0].

rewrite Hk0 in Hx.
rewrite Rmult_0_l, Rplus_0_r, Rmult_1_l in Hx.
set (l' := match l with loc_Exact => l | _ => loc_Inexact Lt end).
assert ((l = loc_Exact /\ l' = loc_Exact) \/ (l <> loc_Exact /\ l' = loc_Inexact Lt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
constructor.
rewrite H1 in Hx.
now inversion_clear Hx.
now apply inbetween_step_Lo_not_Eq with (2 := H1).

destruct (Zcompare_spec (2 * k + 1) nb_steps) as [Hk1|Hk1|Hk1].

apply inbetween_step_Lo with (1 := Hx) (3 := Hk1).
lia.

destruct l.
apply inbetween_step_Lo_Mi_Eq_odd with (1 := Hx) (2 := Hk1).
apply inbetween_step_any_Mi_odd with (1 := Hx) (2 := Hk1).

apply inbetween_step_Hi with (1 := Hx).
destruct (Zeven_ex nb_steps).
rewrite Ho in H.
lia.
apply Hk.
Qed.

Definition new_location :=
  if Z.even nb_steps then new_location_even else new_location_odd.

Theorem new_location_correct :
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  inbetween start (start + IZR nb_steps * step) x (new_location k l).
Proof using Hnb_steps Hstep.
intros x k l Hk Hx.
unfold new_location.
generalize (refl_equal nb_steps) (Z.le_lt_trans _ _ _ (proj1 Hk) (proj2 Hk)).
pattern nb_steps at 2 3 5 ; case nb_steps.
now intros _.

intros [p|p|] Hp _.
apply new_location_odd_correct with (2 := Hk) (3 := Hx).
now rewrite Hp.
apply new_location_even_correct with (2 := Hk) (3 := Hx).
now rewrite Hp.
now rewrite Hp in Hnb_steps.

now intros p _.
Qed.

End Fcalc_bracket_step.

Section Bracket_plus.

Theorem inbetween_plus_compat :
  forall x d u l t,
  inbetween x d u l ->
  inbetween (x + t) (d + t) (u + t) l.
Proof.
intros x d u l t [Hx|l' Hx Hl] ; constructor.
now rewrite Hx.
now split ; apply Rplus_lt_compat_r.
replace ((x + t + (d + t)) / 2)%R with ((x + d) / 2 + t)%R by field.
now rewrite Rcompare_plus_r.
Qed.

Theorem inbetween_plus_reg :
  forall x d u l t,
  inbetween (x + t) (d + t) (u + t) l ->
  inbetween x d u l.
Proof.
intros x d u l t H.
generalize (inbetween_plus_compat _ _ _ _ (Ropp t) H).
assert (K: forall y, (y + t + -t = y)%R) by (intros y ; ring).
now rewrite 3!K.
Qed.

End Bracket_plus.

Section Fcalc_bracket_scale.

Theorem inbetween_mult_compat :
  forall x d u l s,
  (0 < s)%R ->
  inbetween x d u l ->
  inbetween (x * s) (d * s) (u * s) l.
Proof.
intros x d u l s Hs [Hx|l' Hx Hl] ; constructor.
now rewrite Hx.
now split ; apply Rmult_lt_compat_r.
replace ((x * s + d * s) / 2)%R with ((x + d) / 2 * s)%R by field.
now rewrite Rcompare_mult_r.
Qed.

Theorem inbetween_mult_reg :
  forall x d u l s,
  (0 < s)%R ->
  inbetween (x * s) (d * s) (u * s) l ->
  inbetween x d u l.
Proof.
intros x d u l s Hs H.
generalize (inbetween_mult_compat _ _ _ _ _ (Rinv_0_lt_compat s Hs) H).
assert (K: forall y, (y * s * /s = y)%R).
{
 intros y.
field.
now apply Rgt_not_eq.
}
now rewrite 3!K.
Qed.

End Fcalc_bracket_scale.

Section Fcalc_bracket_generic.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Definition inbetween_float m e x l :=
  inbetween (F2R (Float beta m e)) (F2R (Float beta (m + 1) e)) x l.

Theorem inbetween_float_bounds :
  forall x m e l,
  inbetween_float m e x l ->
  (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R.
Proof using .
intros x m e l [Hx|l' Hx Hl].
rewrite Hx.
split.
apply Rle_refl.
apply F2R_lt.
apply Zlt_succ.
split.
now apply Rlt_le.
apply Hx.
Qed.

Definition inbetween_int m x l :=
  inbetween (IZR m) (IZR (m + 1)) x l.

Theorem inbetween_float_new_location :
  forall x m e l k,
  (0 < k)%Z ->
  inbetween_float m e x l ->
  inbetween_float (Z.div m (Zpower beta k)) (e + k) x (new_location (Zpower beta k) (Zmod m (Zpower beta k)) l).
Proof using .
intros x m e l k Hk Hx.
unfold inbetween_float in *.
assert (Hr: forall m, F2R (Float beta m (e + k)) = F2R (Float beta (m * Zpower beta k) e)).
clear -Hk.
intros m.
rewrite (F2R_change_exp beta e).
apply (f_equal (fun r => F2R (Float beta (m * Zpower _ r) e))).
ring.
lia.
assert (Hp: (Zpower beta k > 0)%Z).
apply Z.lt_gt.
apply Zpower_gt_0.
now apply Zlt_le_weak.

rewrite 2!Hr.
rewrite Zmult_plus_distr_l, Zmult_1_l.
unfold F2R at 2.
simpl.
rewrite plus_IZR, Rmult_plus_distr_r.
apply new_location_correct; unfold F2R; simpl.
apply bpow_gt_0.
now apply Zpower_gt_1.
now apply Z_mod_lt.
rewrite <- 2!Rmult_plus_distr_r, <- 2!plus_IZR.
rewrite Zmult_comm, Zplus_assoc.
now rewrite <- Z_div_mod_eq_full.
Qed.

Theorem inbetween_float_new_location_single :
  forall x m e l,
  inbetween_float m e x l ->
  inbetween_float (Z.div m beta) (e + 1) x (new_location beta (Zmod m beta) l).
Proof using .
intros x m e l Hx.
replace (radix_val beta) with (Zpower beta 1).
now apply inbetween_float_new_location.
apply Zmult_1_r.
Qed.

Theorem inbetween_float_ex :
  forall m e l,
  exists x,
  inbetween_float m e x l.
Proof using .
intros m e l.
apply inbetween_ex.
apply F2R_lt.
apply Zlt_succ.
Qed.

Theorem inbetween_float_unique :
  forall x e m l m' l',
  inbetween_float m e x l ->
  inbetween_float m' e x l' ->
  m = m' /\ l = l'.
Proof using .
intros x e m l m' l' H H'.
refine ((fun Hm => conj Hm _) _).
rewrite <- Hm in H'.
clear -H H'.
apply inbetween_unique with (1 := H) (2 := H').
destruct (inbetween_float_bounds x m e l H) as (H1,H2).
destruct (inbetween_float_bounds x m' e l' H') as (H3,H4).
cut (m < m' + 1 /\ m' < m + 1)%Z.
clear ; lia.
now split ; apply lt_F2R with beta e ; apply Rle_lt_trans with x.
Qed.

End Fcalc_bracket_generic.

End Bracket.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Bracket.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_Round_pred.
Module Export Flocq.
Module Export Core.
Module Export Round_pred.

Import Stdlib.Reals.Reals.
Import Flocq.Core.Raux Flocq.Core.Defs.

Section RND_prop.

Open Scope R_scope.

Definition Rnd_DN (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_DN_pt F x (rnd x).

Definition Rnd_UP (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_UP_pt F x (rnd x).

Definition Rnd_ZR (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_ZR_pt F x (rnd x).

Definition Rnd_N (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_N_pt F x (rnd x).

Definition Rnd_NG (F : R -> Prop) (P : R -> R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_NG_pt F P x (rnd x).

Definition Rnd_NA (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_NA_pt F x (rnd x).

Definition Rnd_N0 (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_N0_pt F x (rnd x).

Theorem round_val_of_pred :
  forall rnd : R -> R -> Prop,
  round_pred rnd ->
  forall x, { f : R | rnd x f }.
Proof.
intros rnd (H1,H2) x.
specialize (H1 x).

assert (H3 : bound (rnd x)).
destruct H1 as (f, H1).
exists f.
intros g Hg.
now apply H2 with (3 := Rle_refl x).

exists (proj1_sig (completeness _ H3 H1)).
destruct completeness as (f1, (H4, H5)).
simpl.
destruct H1 as (f2, H1).
assert (f1 = f2).
apply Rle_antisym.
apply H5.
intros f3 H.
now apply H2 with (3 := Rle_refl x).
now apply H4.
now rewrite H.
Qed.

Theorem round_fun_of_pred :
  forall rnd : R -> R -> Prop,
  round_pred rnd ->
  { f : R -> R | forall x, rnd x (f x) }.
Proof.
intros rnd H.
exists (fun x => proj1_sig (round_val_of_pred rnd H x)).
intros x.
now destruct round_val_of_pred as (f, H1).
Qed.

Theorem round_unique :
  forall rnd : R -> R -> Prop,
  round_pred_monotone rnd ->
  forall x f1 f2,
  rnd x f1 ->
  rnd x f2 ->
  f1 = f2.
Proof.
intros rnd Hr x f1 f2 H1 H2.
apply Rle_antisym.
now apply Hr with (3 := Rle_refl x).
now apply Hr with (3 := Rle_refl x).
Qed.

Theorem Rnd_DN_pt_monotone :
  forall F : R -> Prop,
  round_pred_monotone (Rnd_DN_pt F).
Proof.
intros F x y f g (Hx1,(Hx2,_)) (Hy1,(_,Hy2)) Hxy.
apply Hy2.
apply Hx1.
now apply Rle_trans with (2 := Hxy).
Qed.

Theorem Rnd_DN_pt_unique :
  forall F : R -> Prop,
  forall x f1 f2 : R,
  Rnd_DN_pt F x f1 -> Rnd_DN_pt F x f2 ->
  f1 = f2.
Proof.
intros F.
apply round_unique.
apply Rnd_DN_pt_monotone.
Qed.

Theorem Rnd_DN_unique :
  forall F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_DN F rnd1 -> Rnd_DN F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F rnd1 rnd2 H1 H2 x.
now eapply Rnd_DN_pt_unique.
Qed.

Theorem Rnd_UP_pt_monotone :
  forall F : R -> Prop,
  round_pred_monotone (Rnd_UP_pt F).
Proof.
intros F x y f g (Hx1,(_,Hx2)) (Hy1,(Hy2,_)) Hxy.
apply Hx2.
apply Hy1.
now apply Rle_trans with (1 := Hxy).
Qed.

Theorem Rnd_UP_pt_unique :
  forall F : R -> Prop,
  forall x f1 f2 : R,
  Rnd_UP_pt F x f1 -> Rnd_UP_pt F x f2 ->
  f1 = f2.
Proof.
intros F.
apply round_unique.
apply Rnd_UP_pt_monotone.
Qed.

Theorem Rnd_UP_unique :
  forall F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_UP F rnd1 -> Rnd_UP F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F rnd1 rnd2 H1 H2 x.
now eapply Rnd_UP_pt_unique.
Qed.

Theorem Rnd_UP_pt_opp :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_DN_pt F x f -> Rnd_UP_pt F (-x) (-f).
Proof.
intros F HF x f H.
repeat split.
apply HF.
apply H.
apply Ropp_le_contravar.
apply H.
intros g Hg.
rewrite <- (Ropp_involutive g).
intros Hxg.
apply Ropp_le_contravar.
apply H.
now apply HF.
now apply Ropp_le_cancel.
Qed.

Theorem Rnd_DN_pt_opp :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_UP_pt F x f -> Rnd_DN_pt F (-x) (-f).
Proof.
intros F HF x f H.
repeat split.
apply HF.
apply H.
apply Ropp_le_contravar.
apply H.
intros g Hg.
rewrite <- (Ropp_involutive g).
intros Hxg.
apply Ropp_le_contravar.
apply H.
now apply HF.
now apply Ropp_le_cancel.
Qed.

Theorem Rnd_DN_opp :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall rnd1 rnd2 : R -> R,
  Rnd_DN F rnd1 -> Rnd_UP F rnd2 ->
  forall x, rnd1 (- x) = - rnd2 x.
Proof.
intros F HF rnd1 rnd2 H1 H2 x.
rewrite <- (Ropp_involutive (rnd1 (-x))).
apply f_equal.
apply (Rnd_UP_unique F (fun x => - rnd1 (-x))) ; trivial.
intros y.
pattern y at 1 ; rewrite <- Ropp_involutive.
apply Rnd_UP_pt_opp.
apply HF.
apply H1.
Qed.

Theorem Rnd_DN_UP_pt_split :
  forall F : R -> Prop,
  forall x d u,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  forall f, F f ->
  (f <= d) \/ (u <= f).
Proof.
intros F x d u Hd Hu f Hf.
destruct (Rle_or_lt f x).
left.
now apply Hd.
right.
assert (H' := Rlt_le _ _ H).
now apply Hu.
Qed.

Theorem Rnd_DN_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_DN_pt F x x.
Proof.
intros F x Hx.
repeat split.
exact Hx.
apply Rle_refl.
now intros.
Qed.

Theorem Rnd_DN_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_DN_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,(Hx1,Hx2)) Hx.
apply Rle_antisym.
exact Hx1.
apply Hx2.
exact Hx.
apply Rle_refl.
Qed.

Theorem Rnd_UP_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_UP_pt F x x.
Proof.
intros F x Hx.
repeat split.
exact Hx.
apply Rle_refl.
now intros.
Qed.

Theorem Rnd_UP_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_UP_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,(Hx1,Hx2)) Hx.
apply Rle_antisym.
apply Hx2.
exact Hx.
apply Rle_refl.
exact Hx1.
Qed.

Theorem Only_DN_or_UP :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  F f -> (fd <= f <= fu)%R ->
  f = fd \/ f = fu.
Proof.
intros F x fd fu f Hd Hu Hf [Hdf Hfu].
destruct (Rle_or_lt x f) ; [right|left].
apply Rle_antisym with (1 := Hfu).
now apply Hu.
apply Rlt_le in H.
apply Rle_antisym with (2 := Hdf).
now apply Hd.
Qed.

Theorem Rnd_ZR_abs :
  forall (F : R -> Prop) (rnd: R-> R),
  Rnd_ZR F rnd ->
  forall x : R,  (Rabs (rnd x) <= Rabs x)%R.
Proof.
intros F rnd H x.
assert (F 0%R).
replace 0%R with (rnd 0%R).
eapply H.
apply Rle_refl.
destruct (H 0%R) as (H1, H2).
apply Rle_antisym.
apply H1.
apply Rle_refl.
apply H2.
apply Rle_refl.

destruct (Rle_or_lt 0 x).

rewrite Rabs_pos_eq with (1 := H1).
rewrite Rabs_pos_eq.
now apply (proj1 (H x)).
now apply (proj1 (H x)).

apply Rlt_le in H1.
rewrite Rabs_left1 with (1 := H1).
rewrite Rabs_left1.
apply Ropp_le_contravar.
now apply (proj2 (H x)).
now apply (proj2 (H x)).
Qed.

Theorem Rnd_ZR_pt_monotone :
  forall F : R -> Prop, F 0 ->
  round_pred_monotone (Rnd_ZR_pt F).
Proof.
intros F F0 x y f g (Hx1, Hx2) (Hy1, Hy2) Hxy.
destruct (Rle_or_lt 0 x) as [Hx|Hx].

apply Hy1.
now apply Rle_trans with x.
now apply Hx1.
apply Rle_trans with (2 := Hxy).
now apply Hx1.

apply Rlt_le in Hx.
destruct (Rle_or_lt 0 y) as [Hy|Hy].
apply Rle_trans with 0.
now apply Hx2.
now apply Hy1.
apply Rlt_le in Hy.
apply Hx2.
exact Hx.
now apply Hy2.
apply Rle_trans with (1 := Hxy).
now apply Hy2.
Qed.

Theorem Rnd_N_pt_DN_or_UP :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N_pt F x f ->
  Rnd_DN_pt F x f \/ Rnd_UP_pt F x f.
Proof.
intros F x f (Hf1,Hf2).
destruct (Rle_or_lt x f) as [Hxf|Hxf].

right.
repeat split ; try assumption.
intros g Hg Hxg.
specialize (Hf2 g Hg).
rewrite 2!Rabs_pos_eq in Hf2.
now apply Rplus_le_reg_r with (-x)%R.
now apply Rle_0_minus.
now apply Rle_0_minus.

left.
repeat split ; try assumption.
now apply Rlt_le.
intros g Hg Hxg.
specialize (Hf2 g Hg).
rewrite 2!Rabs_left1 in Hf2.
generalize (Ropp_le_cancel _ _ Hf2).
intros H.
now apply Rplus_le_reg_r with (-x)%R.
now apply Rle_minus.
apply Rlt_le.
now apply Rlt_minus.
Qed.

Theorem Rnd_N_pt_DN_or_UP_eq :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  Rnd_N_pt F x f ->
  f = fd \/ f = fu.
Proof.
intros F x fd fu f Hd Hu Hf.
destruct (Rnd_N_pt_DN_or_UP F x f Hf) as [H|H].
left.
apply Rnd_DN_pt_unique with (1 := H) (2 := Hd).
right.
apply Rnd_UP_pt_unique with (1 := H) (2 := Hu).
Qed.

Theorem Rnd_N_pt_opp_inv :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_N_pt F (-x) (-f) -> Rnd_N_pt F x f.
Proof.
intros F HF x f (H1,H2).
rewrite <- (Ropp_involutive f).
repeat split.
apply HF.
apply H1.
intros g H3.
rewrite Ropp_involutive.
replace (f - x)%R with (-(-f - -x))%R by ring.
replace (g - x)%R with (-(-g - -x))%R by ring.
rewrite 2!Rabs_Ropp.
apply H2.
now apply HF.
Qed.

Theorem Rnd_N_pt_monotone :
  forall F : R -> Prop,
  forall x y f g : R,
  Rnd_N_pt F x f -> Rnd_N_pt F y g ->
  x < y -> f <= g.
Proof.
intros F x y f g (Hf,Hx) (Hg,Hy) Hxy.
apply Rnot_lt_le.
intros Hgf.
assert (Hfgx := Hx g Hg).
assert (Hgfy := Hy f Hf).
clear F Hf Hg Hx Hy.
destruct (Rle_or_lt x g) as [Hxg|Hgx].

apply Rle_not_lt with (1 := Hfgx).
rewrite 2!Rabs_pos_eq.
now apply Rplus_lt_compat_r.
apply Rle_0_minus.
apply Rlt_le.
now apply Rle_lt_trans with (1 := Hxg).
now apply Rle_0_minus.
assert (Hgy := Rlt_trans _ _ _ Hgx Hxy).
destruct (Rle_or_lt f y) as [Hfy|Hyf].

apply Rle_not_lt with (1 := Hgfy).
rewrite (Rabs_left (g - y)).
2: now apply Rlt_minus.
rewrite Rabs_left1.
apply Ropp_lt_contravar.
now apply Rplus_lt_compat_r.
now apply Rle_minus.

rewrite Rabs_left, Rabs_pos_eq, Ropp_minus_distr in Hgfy.
rewrite Rabs_pos_eq, Rabs_left, Ropp_minus_distr in Hfgx.
apply Rle_not_lt with (1 := Rplus_le_compat _ _ _ _ Hfgx Hgfy).
apply Rminus_lt.
ring_simplify.
apply Rlt_minus.
apply Rmult_lt_compat_l.
now apply IZR_lt.
exact Hxy.
now apply Rlt_minus.
apply Rle_0_minus.
apply Rlt_le.
now apply Rlt_trans with (1 := Hxy).
apply Rle_0_minus.
now apply Rlt_le.
now apply Rlt_minus.
Qed.

Theorem Rnd_N_pt_unique :
  forall F : R -> Prop,
  forall x d u f1 f2 : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  x - d <> u - x ->
  Rnd_N_pt F x f1 ->
  Rnd_N_pt F x f2 ->
  f1 = f2.
Proof.
intros F x d u f1 f2 Hd Hu Hdu.
assert (forall f1 f2, Rnd_N_pt F x f1 -> Rnd_N_pt F x f2 -> f1 < f2 -> False).
clear f1 f2.
intros f1 f2 Hf1 Hf2 H12.
destruct (Rnd_N_pt_DN_or_UP F x f1 Hf1) as [Hd1|Hu1] ;
  destruct (Rnd_N_pt_DN_or_UP F x f2 Hf2) as [Hd2|Hu2].
apply Rlt_not_eq with (1 := H12).
now apply Rnd_DN_pt_unique with (1 := Hd1).
apply Hdu.
rewrite Rnd_DN_pt_unique with (1 := Hd) (2 := Hd1).
rewrite Rnd_UP_pt_unique with (1 := Hu) (2 := Hu2).
rewrite <- (Rabs_pos_eq (x - f1)).
rewrite <- (Rabs_pos_eq (f2 - x)).
rewrite Rabs_minus_sym.
apply Rle_antisym.
apply Hf1.
apply Hf2.
apply Hf2.
apply Hf1.
apply Rle_0_minus.
apply Hu2.
apply Rle_0_minus.
apply Hd1.
apply Rlt_not_le with (1 := H12).
apply Rle_trans with x.
apply Hd2.
apply Hu1.
apply Rgt_not_eq with (1 := H12).
now apply Rnd_UP_pt_unique with (1 := Hu2).
intros Hf1 Hf2.
now apply Rle_antisym ; apply Rnot_lt_le ; refine (H _ _ _ _).
Qed.

Theorem Rnd_N_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_N_pt F x x.
Proof.
intros F x Hx.
repeat split.
exact Hx.
intros g _.
unfold Rminus at 1.
rewrite Rplus_opp_r, Rabs_R0.
apply Rabs_pos.
Qed.

Theorem Rnd_N_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,Hf) Hx.
apply Rminus_diag_uniq.
destruct (Req_dec (f - x) 0) as [H|H].
exact H.
elim Rabs_no_R0 with (1 := H).
apply Rle_antisym.
replace 0 with (Rabs (x - x)).
now apply Hf.
unfold Rminus.
rewrite Rplus_opp_r.
apply Rabs_R0.
apply Rabs_pos.
Qed.

Theorem Rnd_N_pt_0 :
  forall F : R -> Prop,
  F 0 ->
  Rnd_N_pt F 0 0.
Proof.
intros F HF.
split.
exact HF.
intros g _.
rewrite 2!Rminus_0_r, Rabs_R0.
apply Rabs_pos.
Qed.

Theorem Rnd_N_pt_ge_0 :
  forall F : R -> Prop, F 0 ->
  forall x f, 0 <= x ->
  Rnd_N_pt F x f ->
  0 <= f.
Proof.
intros F HF x f [Hx|Hx] Hxf.
eapply Rnd_N_pt_monotone ; try eassumption.
now apply Rnd_N_pt_0.
right.
apply sym_eq.
apply Rnd_N_pt_idempotent with F.
now rewrite Hx.
exact HF.
Qed.

Theorem Rnd_N_pt_le_0 :
  forall F : R -> Prop, F 0 ->
  forall x f, x <= 0 ->
  Rnd_N_pt F x f ->
  f <= 0.
Proof.
intros F HF x f [Hx|Hx] Hxf.
eapply Rnd_N_pt_monotone ; try eassumption.
now apply Rnd_N_pt_0.
right.
apply Rnd_N_pt_idempotent with F.
now rewrite <- Hx.
exact HF.
Qed.

Theorem Rnd_N_pt_abs :
  forall F : R -> Prop,
  F 0 ->
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_N_pt F x f -> Rnd_N_pt F (Rabs x) (Rabs f).
Proof.
intros F HF0 HF x f Hxf.
unfold Rabs at 1.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite Rabs_left1.
apply Rnd_N_pt_opp_inv.
exact HF.
now rewrite 2!Ropp_involutive.
apply Rnd_N_pt_le_0 with (3 := Hxf).
exact HF0.
now apply Rlt_le.
rewrite Rabs_pos_eq.
exact Hxf.
apply Rnd_N_pt_ge_0 with (3 := Hxf).
exact HF0.
now apply Rge_le.
Qed.

Theorem Rnd_N_pt_DN_UP :
  forall F : R -> Prop,
  forall x d u f : R,
  F f ->
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (Rabs (f - x) <= x - d)%R ->
  (Rabs (f - x) <= u - x)%R ->
  Rnd_N_pt F x f.
Proof.
intros F x d u f Hf Hxd Hxu Hd Hu.
split.
exact Hf.
intros g Hg.
destruct (Rnd_DN_UP_pt_split F x d u Hxd Hxu g Hg) as [Hgd|Hgu].

apply Rle_trans with (1 := Hd).
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rplus_le_compat_l.
now apply Ropp_le_contravar.
apply Rle_minus.
apply Rle_trans with (1 := Hgd).
apply Hxd.

apply Rle_trans with (1 := Hu).
rewrite Rabs_pos_eq.
now apply Rplus_le_compat_r.
apply Rle_0_minus.
apply Rle_trans with (2 := Hgu).
apply Hxu.
Qed.

Theorem Rnd_N_pt_DN :
  forall F : R -> Prop,
  forall x d u : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (x - d <= u - x)%R ->
  Rnd_N_pt F x d.
Proof.
intros F x d u Hd Hu Hx.
assert (Hdx: (Rabs (d - x) = x - d)%R).
rewrite Rabs_minus_sym.
apply Rabs_pos_eq.
apply Rle_0_minus.
apply Hd.
apply Rnd_N_pt_DN_UP with (2 := Hd) (3 := Hu).
apply Hd.
rewrite Hdx.
apply Rle_refl.
now rewrite Hdx.
Qed.

Theorem Rnd_N_pt_UP :
  forall F : R -> Prop,
  forall x d u : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (u - x <= x - d)%R ->
  Rnd_N_pt F x u.
Proof.
intros F x d u Hd Hu Hx.
assert (Hux: (Rabs (u - x) = u - x)%R).
apply Rabs_pos_eq.
apply Rle_0_minus.
apply Hu.
apply Rnd_N_pt_DN_UP with (2 := Hd) (3 := Hu).
apply Hu.
now rewrite Hux.
rewrite Hux.
apply Rle_refl.
Qed.

Definition Rnd_NG_pt_unique_prop F P :=
  forall x d u,
  Rnd_DN_pt F x d -> Rnd_N_pt F x d ->
  Rnd_UP_pt F x u -> Rnd_N_pt F x u ->
  P x d -> P x u -> d = u.

Theorem Rnd_NG_pt_unique :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unique_prop F P ->
  forall x f1 f2 : R,
  Rnd_NG_pt F P x f1 -> Rnd_NG_pt F P x f2 ->
  f1 = f2.
Proof.
intros F P HP x f1 f2 (H1a,H1b) (H2a,H2b).
destruct H1b as [H1b|H1b].
destruct H2b as [H2b|H2b].
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1a) as [H1c|H1c] ;
  destruct (Rnd_N_pt_DN_or_UP _ _ _ H2a) as [H2c|H2c].
eapply Rnd_DN_pt_unique ; eassumption.
now apply (HP x f1 f2).
apply sym_eq.
now apply (HP x f2 f1 H2c H2a H1c H1a).
eapply Rnd_UP_pt_unique ; eassumption.
now apply H2b.
apply sym_eq.
now apply H1b.
Qed.

Theorem Rnd_NG_pt_monotone :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unique_prop F P ->
  round_pred_monotone (Rnd_NG_pt F P).
Proof.
intros F P HP x y f g (Hf,Hx) (Hg,Hy) [Hxy|Hxy].
now apply Rnd_N_pt_monotone with F x y.
apply Req_le.
rewrite <- Hxy in Hg, Hy.
eapply Rnd_NG_pt_unique ; try split ; eassumption.
Qed.

Theorem Rnd_NG_pt_refl :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  forall x, F x -> Rnd_NG_pt F P x x.
Proof.
intros F P x Hx.
split.
now apply Rnd_N_pt_refl.
right.
intros f2 Hf2.
now apply Rnd_N_pt_idempotent with F.
Qed.

Theorem Rnd_NG_pt_opp_inv :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  ( forall x, F x -> F (-x) ) ->
  ( forall x f, P x f -> P (-x) (-f) ) ->
  forall x f : R,
  Rnd_NG_pt F P (-x) (-f) -> Rnd_NG_pt F P x f.
Proof.
intros F P HF HP x f (H1,H2).
split.
now apply Rnd_N_pt_opp_inv.
destruct H2 as [H2|H2].
left.
rewrite <- (Ropp_involutive x), <- (Ropp_involutive f).
now apply HP.
right.
intros f2 Hxf2.
rewrite <- (Ropp_involutive f).
rewrite <- H2 with (-f2).
apply sym_eq.
apply Ropp_involutive.
apply Rnd_N_pt_opp_inv.
exact HF.
now rewrite 2!Ropp_involutive.
Qed.

Theorem Rnd_NG_unique :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unique_prop F P ->
  forall rnd1 rnd2 : R -> R,
  Rnd_NG F P rnd1 -> Rnd_NG F P rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F P HP rnd1 rnd2 H1 H2 x.
now apply Rnd_NG_pt_unique with F P x.
Qed.

Theorem Rnd_NA_NG_pt :
  forall F : R -> Prop,
  F 0 ->
  forall x f,
  Rnd_NA_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs x <= Rabs f) x f.
Proof.
intros F HF x f.
destruct (Rle_or_lt 0 x) as [Hx|Hx].

split ; intros (H1, H2).

assert (Hf := Rnd_N_pt_ge_0 F HF x f Hx H1).
split.
exact H1.
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1) as [H3|H3].

right.
intros f2 Hxf2.
specialize (H2 _ Hxf2).
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H4|H4].
eapply Rnd_DN_pt_unique ; eassumption.
apply Rle_antisym.
rewrite Rabs_pos_eq with (1 := Hf) in H2.
rewrite Rabs_pos_eq in H2.
exact H2.
now apply Rnd_N_pt_ge_0 with F x.
apply Rle_trans with x.
apply H3.
apply H4.

left.
rewrite Rabs_pos_eq with (1 := Hf).
rewrite Rabs_pos_eq with (1 := Hx).
apply H3.

split.
exact H1.
intros f2 Hxf2.
destruct H2 as [H2|H2].
assert (Hf := Rnd_N_pt_ge_0 F HF x f Hx H1).
assert (Hf2 := Rnd_N_pt_ge_0 F HF x f2 Hx Hxf2).
rewrite 2!Rabs_pos_eq ; trivial.
rewrite 2!Rabs_pos_eq in H2 ; trivial.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H3|H3].
apply Rle_trans with (2 := H2).
apply H3.
apply H3.
apply H1.
apply H2.
rewrite (H2 _ Hxf2).
apply Rle_refl.

assert (Hx' := Rlt_le _ _ Hx).
clear Hx.
rename Hx' into Hx.
split ; intros (H1, H2).

assert (Hf := Rnd_N_pt_le_0 F HF x f Hx H1).
split.
exact H1.
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1) as [H3|H3].

left.
rewrite Rabs_left1 with (1 := Hf).
rewrite Rabs_left1 with (1 := Hx).
apply Ropp_le_contravar.
apply H3.

right.
intros f2 Hxf2.
specialize (H2 _ Hxf2).
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H4|H4].
apply Rle_antisym.
apply Rle_trans with x.
apply H4.
apply H3.
rewrite Rabs_left1 with (1 := Hf) in H2.
rewrite Rabs_left1 in H2.
now apply Ropp_le_cancel.
now apply Rnd_N_pt_le_0 with F x.
eapply Rnd_UP_pt_unique ; eassumption.

split.
exact H1.
intros f2 Hxf2.
destruct H2 as [H2|H2].
assert (Hf := Rnd_N_pt_le_0 F HF x f Hx H1).
assert (Hf2 := Rnd_N_pt_le_0 F HF x f2 Hx Hxf2).
rewrite 2!Rabs_left1 ; trivial.
rewrite 2!Rabs_left1 in H2 ; trivial.
apply Ropp_le_contravar.
apply Ropp_le_cancel in H2.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H3|H3].
apply H3.
apply H1.
apply H2.
apply Rle_trans with (1 := H2).
apply H3.
rewrite (H2 _ Hxf2).
apply Rle_refl.
Qed.

Lemma Rnd_NA_pt_unique_prop :
  forall F : R -> Prop,
  F 0 ->
  Rnd_NG_pt_unique_prop F (fun a b => (Rabs a <= Rabs b)%R).
Proof.
intros F HF x d u Hxd1 Hxd2 Hxu1 Hxu2 Hd Hu.
apply Rle_antisym.
apply Rle_trans with x.
apply Hxd1.
apply Hxu1.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
apply Hxu1.
apply Hxd1.
rewrite Rabs_pos_eq with (1 := Hx) in Hd.
rewrite Rabs_pos_eq in Hd.
exact Hd.
now apply Hxd1.
apply Hxd1.
apply Hxu1.
rewrite Rabs_left with (1 := Hx) in Hu.
rewrite Rabs_left1 in Hu.
now apply Ropp_le_cancel.
apply Hxu1.
apply HF.
now apply Rlt_le.
Qed.

Theorem Rnd_NA_pt_unique :
  forall F : R -> Prop,
  F 0 ->
  forall x f1 f2 : R,
  Rnd_NA_pt F x f1 -> Rnd_NA_pt F x f2 ->
  f1 = f2.
Proof.
intros F HF x f1 f2 H1 H2.
apply (Rnd_NG_pt_unique F _ (Rnd_NA_pt_unique_prop F HF) x).
now apply -> Rnd_NA_NG_pt.
now apply -> Rnd_NA_NG_pt.
Qed.

Theorem Rnd_NA_pt_N :
  forall F : R -> Prop,
  F 0 ->
  forall x f : R,
  Rnd_N_pt F x f ->
  (Rabs x <= Rabs f)%R ->
  Rnd_NA_pt F x f.
Proof.
intros F HF x f Rxf Hxf.
split.
apply Rxf.
intros g Rxg.
destruct (Rabs_eq_Rabs (f - x) (g - x)) as [H|H].
apply Rle_antisym.
apply Rxf.
apply Rxg.
apply Rxg.
apply Rxf.

replace g with f.
apply Rle_refl.
apply Rplus_eq_reg_r with (1 := H).

assert (g = 2 * x - f)%R.
replace (2 * x - f)%R with (x - (f - x))%R by ring.
rewrite H.
ring.
destruct (Rle_lt_dec 0 x) as [Hx|Hx].

revert Hxf.
rewrite Rabs_pos_eq with (1 := Hx).
rewrite 2!Rabs_pos_eq ; try ( apply (Rnd_N_pt_ge_0 F HF x) ; assumption ).
intros Hxf.
rewrite H0.
apply Rplus_le_reg_r with f.
ring_simplify.
apply Rmult_le_compat_l with (2 := Hxf).
now apply IZR_le.

revert Hxf.
apply Rlt_le in Hx.
rewrite Rabs_left1 with (1 := Hx).
rewrite 2!Rabs_left1 ; try ( apply (Rnd_N_pt_le_0 F HF x) ; assumption ).
intros Hxf.
rewrite H0.
apply Ropp_le_contravar.
apply Rplus_le_reg_r with f.
ring_simplify.
apply Rmult_le_compat_l.
now apply IZR_le.
now apply Ropp_le_cancel.
Qed.

Theorem Rnd_NA_unique :
  forall (F : R -> Prop),
  F 0 ->
  forall rnd1 rnd2 : R -> R,
  Rnd_NA F rnd1 -> Rnd_NA F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F HF rnd1 rnd2 H1 H2 x.
now apply Rnd_NA_pt_unique with F x.
Qed.

Theorem Rnd_NA_pt_monotone :
  forall F : R -> Prop,
  F 0 ->
  round_pred_monotone (Rnd_NA_pt F).
Proof.
intros F HF x y f g Hxf Hyg Hxy.
apply (Rnd_NG_pt_monotone F _ (Rnd_NA_pt_unique_prop F HF) x y).
now apply -> Rnd_NA_NG_pt.
now apply -> Rnd_NA_NG_pt.
exact Hxy.
Qed.

Theorem Rnd_NA_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_NA_pt F x x.
Proof.
intros F x Hx.
split.
now apply Rnd_N_pt_refl.
intros f Hxf.
apply Req_le.
apply f_equal.
now apply Rnd_N_pt_idempotent with (1 := Hxf).
Qed.

Theorem Rnd_NA_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_NA_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (Hf,_) Hx.
now apply Rnd_N_pt_idempotent with F.
Qed.

Theorem Rnd_N0_NG_pt :
  forall F : R -> Prop,
  F 0 ->
  forall x f,
  Rnd_N0_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs f <= Rabs x) x f.
Proof.
intros F HF x f.
destruct (Rle_or_lt 0 x) as [Hx|Hx].

split ; intros (H1, H2).

assert (Hf := Rnd_N_pt_ge_0 F HF x f Hx H1).
split.
exact H1.
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1) as [H3|H3].

left.
rewrite Rabs_pos_eq with (1 := Hf).
rewrite Rabs_pos_eq with (1 := Hx).
apply H3.

right.
intros f2 Hxf2.
specialize (H2 _ Hxf2).
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H4|H4].
apply Rle_antisym.
apply Rle_trans with x.
apply H4.
apply H3.
rewrite Rabs_pos_eq with (1 := Hf) in H2.
rewrite Rabs_pos_eq in H2.
exact H2.
now apply Rnd_N_pt_ge_0 with F x.
eapply Rnd_UP_pt_unique ; eassumption.

split.
exact H1.
intros f2 Hxf2.
destruct H2 as [H2|H2].
assert (Hf := Rnd_N_pt_ge_0 F HF x f Hx H1).
assert (Hf2 := Rnd_N_pt_ge_0 F HF x f2 Hx Hxf2).
rewrite 2!Rabs_pos_eq ; trivial.
rewrite 2!Rabs_pos_eq in H2 ; trivial.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H3|H3].
apply H3.
apply H1.
apply H2.
apply Rle_trans with (1 := H2).
apply H3.
rewrite (H2 _ Hxf2).
apply Rle_refl.

assert (Hx' := Rlt_le _ _ Hx).
clear Hx.
rename Hx' into Hx.
split ; intros (H1, H2).

assert (Hf := Rnd_N_pt_le_0 F HF x f Hx H1).
split.
exact H1.
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1) as [H3|H3].

right.
intros f2 Hxf2.
specialize (H2 _ Hxf2).
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H4|H4].
eapply Rnd_DN_pt_unique ; eassumption.
apply Rle_antisym.
2: apply Rle_trans with x.
2: apply H3.
2: apply H4.
rewrite Rabs_left1 with (1 := Hf) in H2.
rewrite Rabs_left1 in H2.
now apply Ropp_le_cancel.
now apply Rnd_N_pt_le_0 with F x.

left.
rewrite Rabs_left1 with (1 := Hf).
rewrite Rabs_left1 with (1 := Hx).
apply Ropp_le_contravar.
apply H3.

split.
exact H1.
intros f2 Hxf2.
destruct H2 as [H2|H2].
assert (Hf := Rnd_N_pt_le_0 F HF x f Hx H1).
assert (Hf2 := Rnd_N_pt_le_0 F HF x f2 Hx Hxf2).
rewrite 2!Rabs_left1 ; trivial.
rewrite 2!Rabs_left1 in H2 ; trivial.
apply Ropp_le_contravar.
apply Ropp_le_cancel in H2.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H3|H3].
2: apply H3.
2: apply H1.
2: apply H2.
apply Rle_trans with (2 := H2).
apply H3.
rewrite (H2 _ Hxf2).
apply Rle_refl.
Qed.

Lemma Rnd_N0_pt_unique_prop :
  forall F : R -> Prop,
  F 0 ->
  Rnd_NG_pt_unique_prop F (fun x f => Rabs f <= Rabs x).
Proof.
intros F HF x d u Hxd1 Hxd2 Hxu1 Hxu2 Hd Hu.
apply Rle_antisym.
apply Rle_trans with x.
apply Hxd1.
apply Hxu1.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
apply Hxd1.
apply Hxu1.
rewrite Rabs_pos_eq with (1 := Hx) in Hu.
rewrite Rabs_pos_eq in Hu.
exact Hu.
apply Rle_trans with (1:=Hx).
apply Hxu1.

apply Hxu1.
apply Hxd1.
rewrite Rabs_left with (1 := Hx) in Hd.
rewrite Rabs_left1 in Hd.
now apply Ropp_le_cancel.
apply Rlt_le, Rle_lt_trans with (2:=Hx).
apply Hxd1.
Qed.

Theorem Rnd_N0_pt_unique :
  forall F : R -> Prop,
  F 0 ->
  forall x f1 f2 : R,
  Rnd_N0_pt F x f1 -> Rnd_N0_pt F x f2 ->
  f1 = f2.
Proof.
intros F HF x f1 f2 H1 H2.
apply (Rnd_NG_pt_unique F _ (Rnd_N0_pt_unique_prop F HF) x).
now apply -> Rnd_N0_NG_pt.
now apply -> Rnd_N0_NG_pt.
Qed.

Theorem Rnd_N0_pt_N :
  forall F : R -> Prop,
  F 0 ->
  forall x f : R,
  Rnd_N_pt F x f ->
  (Rabs f <= Rabs x)%R ->
  Rnd_N0_pt F x f.
Proof.
intros F HF x f Rxf Hxf.
split.
apply Rxf.
intros g Rxg.
destruct (Rabs_eq_Rabs (f - x) (g - x)) as [H|H].
apply Rle_antisym.
apply Rxf.
apply Rxg.
apply Rxg.
apply Rxf.

replace g with f.
apply Rle_refl.
apply Rplus_eq_reg_r with (1 := H).

assert (g = 2 * x - f)%R.
replace (2 * x - f)%R with (x - (f - x))%R by ring.
rewrite H.
ring.
destruct (Rle_lt_dec 0 x) as [Hx|Hx].

revert Hxf.
rewrite Rabs_pos_eq with (1 := Hx).
rewrite 2!Rabs_pos_eq ; try ( apply (Rnd_N_pt_ge_0 F HF x) ; assumption ).
intros Hxf.
rewrite H0.
apply Rplus_le_reg_r with f.
ring_simplify.
apply Rmult_le_compat_l with (2 := Hxf).
now apply IZR_le.

revert Hxf.
apply Rlt_le in Hx.
rewrite Rabs_left1 with (1 := Hx).
rewrite 2!Rabs_left1 ; try ( apply (Rnd_N_pt_le_0 F HF x) ; assumption ).
intros Hxf.
rewrite H0.
apply Ropp_le_contravar.
apply Rplus_le_reg_r with f.
ring_simplify.
apply Rmult_le_compat_l.
now apply IZR_le.
now apply Ropp_le_cancel.
Qed.

Theorem Rnd_N0_unique :
  forall (F : R -> Prop),
  F 0 ->
  forall rnd1 rnd2 : R -> R,
  Rnd_N0 F rnd1 -> Rnd_N0 F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F HF rnd1 rnd2 H1 H2 x.
now apply Rnd_N0_pt_unique with F x.
Qed.

Theorem Rnd_N0_pt_monotone :
  forall F : R -> Prop,
  F 0 ->
  round_pred_monotone (Rnd_N0_pt F).
Proof.
intros F HF x y f g Hxf Hyg Hxy.
apply (Rnd_NG_pt_monotone F _ (Rnd_N0_pt_unique_prop F HF) x y).
now apply -> Rnd_N0_NG_pt.
now apply -> Rnd_N0_NG_pt.
exact Hxy.
Qed.

Theorem Rnd_N0_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_N0_pt F x x.
Proof.
intros F x Hx.
split.
now apply Rnd_N_pt_refl.
intros f Hxf.
apply Req_le.
apply f_equal.
now apply sym_eq, Rnd_N_pt_idempotent with (1 := Hxf).
Qed.

Theorem Rnd_N0_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N0_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (Hf,_) Hx.
now apply Rnd_N_pt_idempotent with F.
Qed.

Theorem round_pred_ge_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> 0 <= x -> 0 <= f.
Proof.
intros P HP HP0 x f Hxf Hx.
now apply (HP 0 x).
Qed.

Theorem round_pred_gt_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> 0 < f -> 0 < x.
Proof.
intros P HP HP0 x f Hxf Hf.
apply Rnot_le_lt.
intros Hx.
apply Rlt_not_le with (1 := Hf).
now apply (HP x 0).
Qed.

Theorem round_pred_le_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> x <= 0 -> f <= 0.
Proof.
intros P HP HP0 x f Hxf Hx.
now apply (HP x 0).
Qed.

Theorem round_pred_lt_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> f < 0 -> x < 0.
Proof.
intros P HP HP0 x f Hxf Hf.
apply Rnot_le_lt.
intros Hx.
apply Rlt_not_le with (1 := Hf).
now apply (HP 0 x).
Qed.

Theorem Rnd_DN_pt_equiv_format :
  forall F1 F2 : R -> Prop,
  forall a b : R,
  F1 a ->
  ( forall x, a <= x <= b -> (F1 x <-> F2 x) ) ->
  forall x f, a <= x <= b -> Rnd_DN_pt F1 x f -> Rnd_DN_pt F2 x f.
Proof.
intros F1 F2 a b Ha HF x f Hx (H1, (H2, H3)).
split.
apply -> HF.
exact H1.
split.
now apply H3.
now apply Rle_trans with (1 := H2).
split.
exact H2.
intros k Hk Hl.
destruct (Rlt_or_le k a) as [H|H].
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
now apply H3.
apply H3.
apply <- HF.
exact Hk.
split.
exact H.
now apply Rle_trans with (1 := Hl).
exact Hl.
Qed.

Theorem Rnd_UP_pt_equiv_format :
  forall F1 F2 : R -> Prop,
  forall a b : R,
  F1 b ->
  ( forall x, a <= x <= b -> (F1 x <-> F2 x) ) ->
  forall x f, a <= x <= b -> Rnd_UP_pt F1 x f -> Rnd_UP_pt F2 x f.
Proof.
intros F1 F2 a b Hb HF x f Hx (H1, (H2, H3)).
split.
apply -> HF.
exact H1.
split.
now apply Rle_trans with (2 := H2).
now apply H3.
split.
exact H2.
intros k Hk Hl.
destruct (Rle_or_lt k b) as [H|H].
apply H3.
apply <- HF.
exact Hk.
split.
now apply Rle_trans with (2 := Hl).
exact H.
exact Hl.
apply Rlt_le.
apply Rle_lt_trans with (2 := H).
now apply H3.
Qed.

Inductive satisfies_any (F : R -> Prop) :=
  Satisfies_any :
    F 0 -> ( forall x : R, F x -> F (-x) ) ->
    round_pred_total (Rnd_DN_pt F) -> satisfies_any F.

Theorem satisfies_any_eq :
  forall F1 F2 : R -> Prop,
  ( forall x, F1 x <-> F2 x ) ->
  satisfies_any F1 ->
  satisfies_any F2.
Proof.
intros F1 F2 Heq (Hzero, Hsym, Hrnd).
split.
now apply -> Heq.
intros x Hx.
apply -> Heq.
apply Hsym.
now apply <- Heq.
intros x.
destruct (Hrnd x) as (f, (H1, (H2, H3))).
exists f.
split.
now apply -> Heq.
split.
exact H2.
intros g Hg Hgx.
apply H3.
now apply <- Heq.
exact Hgx.
Qed.

Theorem satisfies_any_imp_DN :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_DN_pt F).
Proof.
intros F (_,_,Hrnd).
split.
apply Hrnd.
apply Rnd_DN_pt_monotone.
Qed.

Theorem satisfies_any_imp_UP :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_UP_pt F).
Proof.
intros F Hany.
split.
intros x.
destruct (proj1 (satisfies_any_imp_DN F Hany) (-x)) as (f, Hf).
exists (-f).
rewrite <- (Ropp_involutive x).
apply Rnd_UP_pt_opp.
apply Hany.
exact Hf.
apply Rnd_UP_pt_monotone.
Qed.

Theorem satisfies_any_imp_ZR :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_ZR_pt F).
Proof.
intros F Hany.
split.
intros x.
destruct (Rle_or_lt 0 x) as [Hx|Hx].

destruct (proj1 (satisfies_any_imp_DN F Hany) x) as (f, Hf).
exists f.
split.
now intros _.
intros Hx'.

assert (x = 0).
now apply Rle_antisym.
rewrite H in Hf |- *.
clear H Hx Hx'.
rewrite Rnd_DN_pt_idempotent with (1 := Hf).
apply Rnd_UP_pt_refl.
apply Hany.
apply Hany.

destruct (proj1 (satisfies_any_imp_UP F Hany) x) as (f, Hf).
exists f.
split.
intros Hx'.
elim (Rlt_irrefl 0).
now apply Rle_lt_trans with x.
now intros _.

apply Rnd_ZR_pt_monotone.
apply Hany.
Qed.

Definition NG_existence_prop (F : R -> Prop) (P : R -> R -> Prop) :=
  forall x d u, ~F x -> Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> P x u \/ P x d.

Theorem satisfies_any_imp_NG :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  satisfies_any F ->
  NG_existence_prop F P ->
  round_pred_total (Rnd_NG_pt F P).
Proof.
intros F P Hany HP x.
destruct (proj1 (satisfies_any_imp_DN F Hany) x) as (d, Hd).
destruct (proj1 (satisfies_any_imp_UP F Hany) x) as (u, Hu).
destruct (total_order_T (Rabs (u - x)) (Rabs (d - x))) as [[H|H]|H].

exists u.
split.

split.
apply Hu.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
do 2 rewrite <- (Rabs_minus_sym x).
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
now apply Hd.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hd.

right.
intros f Hf.
destruct (Rnd_N_pt_DN_or_UP_eq F x _ _ _ Hd Hu Hf) as [K|K] ; rewrite K.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hf.
apply Hu.
apply refl_equal.

destruct (Req_dec x d) as [He|Hne].

exists x.
split.
apply Rnd_N_pt_refl.
rewrite He.
apply Hd.
right.
intros.
apply Rnd_N_pt_idempotent with (1 := H0).
rewrite He.
apply Hd.
assert (Hf : ~F x).
intros Hf.
apply Hne.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
destruct (HP x _ _ Hf Hd Hu) as [H'|H'].

exists u.
split.
split.
apply Hu.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite H.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
now left.

exists d.
split.
split.
apply Hd.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite <- H.
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
now left.

exists d.
split.
split.
apply Hd.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
right.
intros f Hf.
destruct (Rnd_N_pt_DN_or_UP_eq F x _ _ _ Hd Hu Hf) as [K|K] ; rewrite K.
apply refl_equal.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hf.
apply Hd.
Qed.

Theorem satisfies_any_imp_NA :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_NA_pt F).
Proof.
intros F Hany.
split.
assert (H : round_pred_total (Rnd_NG_pt F (fun a b => (Rabs a <= Rabs b)%R))).
apply satisfies_any_imp_NG.
apply Hany.
intros x d u Hf Hd Hu.
destruct (Rle_lt_dec 0 x) as [Hx|Hx].
left.
rewrite Rabs_pos_eq with (1 := Hx).
rewrite Rabs_pos_eq.
apply Hu.
apply Rle_trans with (1 := Hx).
apply Hu.
right.
rewrite Rabs_left with (1 := Hx).
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Hd.
apply Rlt_le in Hx.
apply Rle_trans with (2 := Hx).
apply Hd.
intros x.
destruct (H x) as (f, Hf).
exists f.
apply <- Rnd_NA_NG_pt.
apply Hf.
apply Hany.
apply Rnd_NA_pt_monotone.
apply Hany.
Qed.

Theorem satisfies_any_imp_N0 :
  forall F : R -> Prop,
  F 0 -> satisfies_any F ->
  round_pred (Rnd_N0_pt F).
Proof.
intros F HF0 Hany.
split.
assert (H : round_pred_total (Rnd_NG_pt F (fun a b => (Rabs b <= Rabs a)%R))).
apply satisfies_any_imp_NG.
apply Hany.
intros x d u Hf Hd Hu.
destruct (Rle_lt_dec 0 x) as [Hx|Hx].
right.
rewrite Rabs_pos_eq with (1 := Hx).
rewrite Rabs_pos_eq.
apply Hd.
apply Hd; try easy.
left.
rewrite Rabs_left with (1 := Hx).
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Hu.
apply Hu; try easy.
now apply Rlt_le.
intros x.
destruct (H x) as (f, Hf).
exists f.
apply <- Rnd_N0_NG_pt.
apply Hf.
apply HF0.
apply Rnd_N0_pt_monotone.
apply HF0.
Qed.

End RND_prop.

End Round_pred.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Round_pred.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_Generic_fmt.
Module Export Flocq.
Module Export Core.
Module Export Generic_fmt.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Round_pred Flocq.Core.Float_prop.

Section Generic.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Section Format.

Variable fexp : Z -> Z.

Class Valid_exp :=
  valid_exp :
  forall k : Z,
  ( (fexp k < k)%Z -> (fexp (k + 1) <= k)%Z ) /\
  ( (k <= fexp k)%Z ->
    (fexp (fexp k + 1) <= fexp k)%Z /\
    forall l : Z, (l <= fexp k)%Z -> fexp l = fexp k ).

Context { valid_exp_ : Valid_exp }.

Theorem valid_exp_large :
  forall k l,
  (fexp k < k)%Z -> (k <= l)%Z ->
  (fexp l < l)%Z.
Proof using valid_exp_.
intros k l Hk H.
apply Znot_ge_lt.
intros Hl.
apply Z.ge_le in Hl.
assert (H' := proj2 (proj2 (valid_exp l) Hl) k).
lia.
Qed.

Theorem valid_exp_large' :
  forall k l,
  (fexp k < k)%Z -> (l <= k)%Z ->
  (fexp l < k)%Z.
Proof using valid_exp_.
intros k l Hk H.
apply Znot_ge_lt.
intros H'.
apply Z.ge_le in H'.
assert (Hl := Z.le_trans _ _ _ H H').
apply valid_exp in Hl.
assert (H1 := proj2 Hl k H').
lia.
Qed.

Definition cexp x :=
  fexp (mag beta x).

Definition canonical (f : float beta) :=
  Fexp f = cexp (F2R f).

Definition scaled_mantissa x :=
  (x * bpow (- cexp x))%R.

Definition generic_format (x : R) :=
  x = F2R (Float beta (Ztrunc (scaled_mantissa x)) (cexp x)).

Theorem generic_format_0 :
  generic_format 0.
Proof using .
unfold generic_format, scaled_mantissa.
rewrite Rmult_0_l.
now rewrite Ztrunc_IZR, F2R_0.
Qed.

Theorem cexp_opp :
  forall x,
  cexp (-x) = cexp x.
Proof using .
intros x.
unfold cexp.
now rewrite mag_opp.
Qed.

Theorem cexp_abs :
  forall x,
  cexp (Rabs x) = cexp x.
Proof using .
intros x.
unfold cexp.
now rewrite mag_abs.
Qed.

Theorem canonical_generic_format :
  forall x,
  generic_format x ->
  exists f : float beta,
  x = F2R f /\ canonical f.
Proof using .
intros x Hx.
rewrite Hx.
eexists.
apply (conj eq_refl).
unfold canonical.
now rewrite <- Hx.
Qed.

Theorem generic_format_bpow :
  forall e, (fexp (e + 1) <= e)%Z ->
  generic_format (bpow e).
Proof using .
intros e H.
unfold generic_format, scaled_mantissa, cexp.
rewrite mag_bpow.
rewrite <- bpow_plus.
rewrite <- (IZR_Zpower beta (e + - fexp (e + 1))).
rewrite Ztrunc_IZR.
rewrite <- F2R_bpow.
rewrite F2R_change_exp with (1 := H).
now rewrite Zmult_1_l.
now apply Zle_minus_le_0.
Qed.

Theorem generic_format_bpow' :
  forall e, (fexp e <= e)%Z ->
  generic_format (bpow e).
Proof using valid_exp_.
intros e He.
apply generic_format_bpow.
destruct (Zle_lt_or_eq _ _ He).
now apply valid_exp_.
rewrite <- H.
apply valid_exp.
rewrite H.
apply Z.le_refl.
Qed.

Theorem generic_format_F2R :
  forall m e,
  ( m <> 0 -> cexp (F2R (Float beta m e)) <= e )%Z ->
  generic_format (F2R (Float beta m e)).
Proof using .
intros m e.
destruct (Z.eq_dec m 0) as [Zm|Zm].
intros _.
rewrite Zm, F2R_0.
apply generic_format_0.
unfold generic_format, scaled_mantissa.
set (e' := cexp (F2R (Float beta m e))).
intros He.
specialize (He Zm).
unfold F2R at 3.
simpl.
rewrite  F2R_change_exp with (1 := He).
apply F2R_eq.
rewrite Rmult_assoc, <- bpow_plus, <- IZR_Zpower, <- mult_IZR.
now rewrite Ztrunc_IZR.
now apply Zle_left.
Qed.

Lemma generic_format_F2R' :
  forall (x : R) (f : float beta),
  F2R f = x ->
  (x <> 0%R -> (cexp x <= Fexp f)%Z) ->
  generic_format x.
Proof using .
intros x f H1 H2.
rewrite <- H1; destruct f as (m,e).
apply generic_format_F2R.
simpl in *; intros H3.
rewrite H1; apply H2.
intros Y; apply H3.
apply eq_0_F2R with beta e.
now rewrite H1.
Qed.

Theorem canonical_opp :
  forall m e,
  canonical (Float beta m e) ->
  canonical (Float beta (-m) e).
Proof using .
intros m e H.
unfold canonical.
now rewrite F2R_Zopp, cexp_opp.
Qed.

Theorem canonical_abs :
  forall m e,
  canonical (Float beta m e) ->
  canonical (Float beta (Z.abs m) e).
Proof using .
intros m e H.
unfold canonical.
now rewrite F2R_Zabs, cexp_abs.
Qed.

Theorem canonical_0 :
  canonical (Float beta 0 (fexp (mag beta 0%R))).
Proof using .
unfold canonical; simpl ; unfold cexp.
now rewrite F2R_0.
Qed.

Theorem canonical_unique :
  forall f1 f2,
  canonical f1 ->
  canonical f2 ->
  F2R f1 = F2R f2 ->
  f1 = f2.
Proof using .
intros (m1, e1) (m2, e2).
unfold canonical.
simpl.
intros H1 H2 H.
rewrite H in H1.
rewrite <- H2 in H1.
clear H2.
rewrite H1 in H |- *.
apply (f_equal (fun m => Float beta m e2)).
apply eq_F2R with (1 := H).
Qed.

Theorem scaled_mantissa_generic :
  forall x,
  generic_format x ->
  scaled_mantissa x = IZR (Ztrunc (scaled_mantissa x)).
Proof using .
intros x Hx.
unfold scaled_mantissa.
pattern x at 1 3 ; rewrite Hx.
unfold F2R.
simpl.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
now rewrite Ztrunc_IZR.
Qed.

Theorem scaled_mantissa_mult_bpow :
  forall x,
  (scaled_mantissa x * bpow (cexp x))%R = x.
Proof using .
intros x.
unfold scaled_mantissa.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_l.
apply Rmult_1_r.
Qed.

Theorem scaled_mantissa_0 :
  scaled_mantissa 0 = 0%R.
Proof using .
apply Rmult_0_l.
Qed.

Theorem scaled_mantissa_opp :
  forall x,
  scaled_mantissa (-x) = (-scaled_mantissa x)%R.
Proof using .
intros x.
unfold scaled_mantissa.
rewrite cexp_opp.
now rewrite Ropp_mult_distr_l_reverse.
Qed.

Theorem scaled_mantissa_abs :
  forall x,
  scaled_mantissa (Rabs x) = Rabs (scaled_mantissa x).
Proof using .
intros x.
unfold scaled_mantissa.
rewrite cexp_abs, Rabs_mult.
apply f_equal.
apply sym_eq.
apply Rabs_pos_eq.
apply bpow_ge_0.
Qed.

Theorem generic_format_opp :
  forall x, generic_format x -> generic_format (-x).
Proof using .
intros x Hx.
unfold generic_format.
rewrite scaled_mantissa_opp, cexp_opp.
rewrite Ztrunc_opp.
rewrite F2R_Zopp.
now apply f_equal.
Qed.

Theorem generic_format_abs :
  forall x, generic_format x -> generic_format (Rabs x).
Proof using .
intros x Hx.
unfold generic_format.
rewrite scaled_mantissa_abs, cexp_abs.
rewrite Ztrunc_abs.
rewrite F2R_Zabs.
now apply f_equal.
Qed.

Theorem generic_format_abs_inv :
  forall x, generic_format (Rabs x) -> generic_format x.
Proof using .
intros x.
unfold generic_format, Rabs.
case Rcase_abs ; intros _.
rewrite scaled_mantissa_opp, cexp_opp, Ztrunc_opp.
intros H.
rewrite <- (Ropp_involutive x) at 1.
rewrite H, F2R_Zopp.
apply Ropp_involutive.
easy.
Qed.

Theorem cexp_fexp :
  forall x ex,
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
  cexp x = fexp ex.
Proof using .
intros x ex Hx.
unfold cexp.
now rewrite mag_unique with (1 := Hx).
Qed.

Theorem cexp_fexp_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  cexp x = fexp ex.
Proof using .
intros x ex Hx.
apply cexp_fexp.
rewrite Rabs_pos_eq.
exact Hx.
apply Rle_trans with (2 := proj1 Hx).
apply bpow_ge_0.
Qed.

Theorem mantissa_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  (0 < x * bpow (- fexp ex) < 1)%R.
Proof using .
intros x ex Hx He.
split.
apply Rmult_lt_0_compat.
apply Rlt_le_trans with (2 := proj1 Hx).
apply bpow_gt_0.
apply bpow_gt_0.
apply Rmult_lt_reg_r with (bpow (fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_l.
rewrite Rmult_1_r, Rmult_1_l.
apply Rlt_le_trans with (1 := proj2 Hx).
now apply bpow_le.
Qed.

Theorem scaled_mantissa_lt_1 :
  forall x ex,
  (Rabs x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  (Rabs (scaled_mantissa x) < 1)%R.
Proof using valid_exp_.
intros x ex Ex He.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, scaled_mantissa_0, Rabs_R0.
now apply IZR_lt.
rewrite <- scaled_mantissa_abs.
unfold scaled_mantissa.
rewrite cexp_abs.
unfold cexp.
destruct (mag beta x) as (ex', Ex').
simpl.
specialize (Ex' Zx).
apply (mantissa_small_pos _ _ Ex').
assert (ex' <= fexp ex)%Z.
apply Z.le_trans with (2 := He).
apply bpow_lt_bpow with beta.
now apply Rle_lt_trans with (2 := Ex).
now rewrite (proj2 (proj2 (valid_exp _) He)).
Qed.

Theorem scaled_mantissa_lt_bpow :
  forall x,
  (Rabs (scaled_mantissa x) < bpow (mag beta x - cexp x))%R.
Proof using .
intros x.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, scaled_mantissa_0, Rabs_R0.
apply bpow_gt_0.
apply Rlt_le_trans with (1 := bpow_mag_gt beta _).
apply bpow_le.
unfold scaled_mantissa.
rewrite mag_mult_bpow with (1 := Zx).
apply Z.le_refl.
Qed.

Theorem mag_generic_gt :
  forall x, (x <> 0)%R ->
  generic_format x ->
  (cexp x < mag beta x)%Z.
Proof using valid_exp_.
intros x Zx Gx.
apply Znot_ge_lt.
unfold cexp.
destruct (mag beta x) as (ex,Ex) ; simpl.
specialize (Ex Zx).
intros H.
apply Z.ge_le in H.
generalize (scaled_mantissa_lt_1 x ex (proj2 Ex) H).
contradict Zx.
rewrite Gx.
replace (Ztrunc (scaled_mantissa x)) with Z0.
apply F2R_0.
cut (Z.abs (Ztrunc (scaled_mantissa x)) < 1)%Z.
clear ; lia.
apply lt_IZR.
rewrite abs_IZR.
now rewrite <- scaled_mantissa_generic.
Qed.

Lemma mantissa_DN_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Zfloor (x * bpow (- fexp ex)) = Z0.
Proof using .
intros x ex Hx He.
apply Zfloor_imp.
simpl.
assert (H := mantissa_small_pos x ex Hx He).
split ; try apply Rlt_le ; apply H.
Qed.

Lemma mantissa_UP_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Zceil (x * bpow (- fexp ex)) = 1%Z.
Proof using .
intros x ex Hx He.
apply Zceil_imp.
simpl.
assert (H := mantissa_small_pos x ex Hx He).
split ; try apply Rlt_le ; apply H.
Qed.

Theorem generic_format_discrete :
  forall x m,
  let e := cexp x in
  (F2R (Float beta m e) < x < F2R (Float beta (m + 1) e))%R ->
  ~ generic_format x.
Proof using .
intros x m e (Hx,Hx2) Hf.
apply Rlt_not_le with (1 := Hx2).
clear Hx2.
rewrite Hf.
fold e.
apply F2R_le.
apply Zlt_le_succ.
apply lt_IZR.
rewrite <- scaled_mantissa_generic with (1 := Hf).
apply Rmult_lt_reg_r with (bpow e).
apply bpow_gt_0.
now rewrite scaled_mantissa_mult_bpow.
Qed.

Theorem generic_format_canonical :
  forall f, canonical f ->
  generic_format (F2R f).
Proof using .
intros (m, e) Hf.
unfold canonical in Hf.
simpl in Hf.
unfold generic_format, scaled_mantissa.
rewrite <- Hf.
apply F2R_eq.
unfold F2R.
simpl.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
now rewrite Ztrunc_IZR.
Qed.

Theorem generic_format_ge_bpow :
  forall emin,
  ( forall e, (emin <= fexp e)%Z ) ->
  forall x,
  (0 < x)%R ->
  generic_format x ->
  (bpow emin <= x)%R.
Proof using .
intros emin Emin x Hx Fx.
rewrite Fx.
apply Rle_trans with (bpow (fexp (mag beta x))).
now apply bpow_le.
apply bpow_le_F2R.
apply gt_0_F2R with beta (cexp x).
now rewrite <- Fx.
Qed.

Theorem abs_lt_bpow_prec:
  forall prec,
  (forall e, (e - prec <= fexp e)%Z) ->

  forall x,
  (Rabs x < bpow (prec + cexp x))%R.
Proof using .
intros prec Hp x.
case (Req_dec x 0); intros Hxz.
rewrite Hxz, Rabs_R0.
apply bpow_gt_0.
unfold cexp.
destruct (mag beta x) as (ex,Ex) ; simpl.
specialize (Ex Hxz).
apply Rlt_le_trans with (1 := proj2 Ex).
apply bpow_le.
specialize (Hp ex).
lia.
Qed.

Theorem generic_format_bpow_inv' :
  forall e,
  generic_format (bpow e) ->
  (fexp (e + 1) <= e)%Z.
Proof using .
intros e He.
apply Znot_gt_le.
contradict He.
unfold generic_format, scaled_mantissa, cexp, F2R.
simpl.
rewrite mag_bpow, <- bpow_plus.
apply Rgt_not_eq.
rewrite Ztrunc_floor.
2: apply bpow_ge_0.
rewrite Zfloor_imp with (n := Z0).
rewrite Rmult_0_l.
apply bpow_gt_0.
split.
apply bpow_ge_0.
apply (bpow_lt _ _ 0).
clear -He ; lia.
Qed.

Theorem generic_format_bpow_inv :
  forall e,
  generic_format (bpow e) ->
  (fexp e <= e)%Z.
Proof using valid_exp_.
intros e He.
apply generic_format_bpow_inv' in He.
assert (H := valid_exp_large' (e + 1) e).
lia.
Qed.

Section Fcore_generic_round_pos.

Variable rnd : R -> Z.

Class Valid_rnd := {
  Zrnd_le : forall x y, (x <= y)%R -> (rnd x <= rnd y)%Z ;
  Zrnd_IZR : forall n, rnd (IZR n) = n
}.

Context { valid_rnd : Valid_rnd }.

Theorem Zrnd_DN_or_UP :
  forall x, rnd x = Zfloor x \/ rnd x = Zceil x.
Proof using valid_rnd.
intros x.
destruct (Zle_or_lt (rnd x) (Zfloor x)) as [Hx|Hx].
left.
apply Zle_antisym with (1 := Hx).
rewrite <- (Zrnd_IZR (Zfloor x)).
apply Zrnd_le.
apply Zfloor_lb.
right.
apply Zle_antisym.
rewrite <- (Zrnd_IZR (Zceil x)).
apply Zrnd_le.
apply Zceil_ub.
rewrite Zceil_floor_neq.
lia.
intros H.
rewrite <- H in Hx.
rewrite Zfloor_IZR, Zrnd_IZR in Hx.
apply Z.lt_irrefl with (1 := Hx).
Qed.

Theorem Zrnd_ZR_or_AW :
  forall x, rnd x = Ztrunc x \/ rnd x = Zaway x.
Proof using valid_rnd.
intros x.
unfold Ztrunc, Zaway.
destruct (Zrnd_DN_or_UP x) as [Hx|Hx] ;
  case Rlt_bool.
now right.
now left.
now left.
now right.
Qed.

Definition round x :=
  F2R (Float beta (rnd (scaled_mantissa x)) (cexp x)).

Theorem round_bounded_large_pos :
  forall x ex,
  (fexp ex < ex)%Z ->
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (bpow (ex - 1) <= round x <= bpow ex)%R.
Proof using valid_rnd.
intros x ex He Hx.
unfold round, scaled_mantissa.
rewrite (cexp_fexp_pos _ _ Hx).
unfold F2R.
simpl.
destruct (Zrnd_DN_or_UP (x * bpow (- fexp ex))) as [Hr|Hr] ; rewrite Hr.

split.
replace (ex - 1)%Z with (ex - 1 + - fexp ex + fexp ex)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (Hf: IZR (Zpower beta (ex - 1 - fexp ex)) = bpow (ex - 1 + - fexp ex)).
apply IZR_Zpower.
lia.
rewrite <- Hf.
apply IZR_le.
apply Zfloor_lub.
rewrite Hf.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Hx.
apply Rle_trans with (2 := Rlt_le _ _ (proj2 Hx)).
apply Rmult_le_reg_r with (bpow (- fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
apply Zfloor_lb.

split.
apply Rle_trans with (1 := proj1 Hx).
apply Rmult_le_reg_r with (bpow (- fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
apply Zceil_ub.
pattern ex at 3 ; replace ex with (ex - fexp ex + fexp ex)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (Hf: IZR (Zpower beta (ex - fexp ex)) = bpow (ex - fexp ex)).
apply IZR_Zpower.
lia.
rewrite <- Hf.
apply IZR_le.
apply Zceil_glb.
rewrite Hf.
unfold Zminus.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rlt_le.
apply Hx.
Qed.

Theorem round_bounded_small_pos :
  forall x ex,
  (ex <= fexp ex)%Z ->
  (bpow (ex - 1) <= x < bpow ex)%R ->
  round x = 0%R \/ round x = bpow (fexp ex).
Proof using valid_rnd.
intros x ex He Hx.
unfold round, scaled_mantissa.
rewrite (cexp_fexp_pos _ _ Hx).
unfold F2R.
simpl.
destruct (Zrnd_DN_or_UP (x * bpow (-fexp ex))) as [Hr|Hr] ; rewrite Hr.

left.
apply Rmult_eq_0_compat_r.
apply IZR_eq.
apply Zfloor_imp.
refine (let H := _ in conj (Rlt_le _ _ (proj1 H)) (proj2 H)).
now apply mantissa_small_pos.

right.
pattern (bpow (fexp ex)) at 2 ; rewrite <- Rmult_1_l.
apply (f_equal (fun m => (m * bpow (fexp ex))%R)).
apply IZR_eq.
apply Zceil_imp.
refine (let H := _ in conj (proj1 H) (Rlt_le _ _ (proj2 H))).
now apply mantissa_small_pos.
Qed.

Lemma round_le_pos :
  forall x y, (0 < x)%R -> (x <= y)%R -> (round x <= round y)%R.
Proof using valid_exp_ valid_rnd.
intros x y Hx Hxy.
destruct (mag beta x) as [ex Hex].
destruct (mag beta y) as [ey Hey].
specialize (Hex (Rgt_not_eq _ _ Hx)).
specialize (Hey (Rgt_not_eq _ _ (Rlt_le_trans _ _ _ Hx Hxy))).
rewrite Rabs_pos_eq in Hex.
2: now apply Rlt_le.
rewrite Rabs_pos_eq in Hey.
2: apply Rle_trans with (2:=Hxy); now apply Rlt_le.
assert (He: (ex <= ey)%Z).
  apply bpow_lt_bpow with beta.
  apply Rle_lt_trans with (1 := proj1 Hex).
  now apply Rle_lt_trans with y.
assert (Heq: fexp ex = fexp ey -> (round x <= round y)%R).
  intros H.
  unfold round, scaled_mantissa, cexp.
  rewrite mag_unique_pos with (1 := Hex).
  rewrite mag_unique_pos with (1 := Hey).
  rewrite H.
  apply F2R_le.
  apply Zrnd_le.
  apply Rmult_le_compat_r with (2 := Hxy).
  apply bpow_ge_0.
destruct (Zle_or_lt ey (fexp ey)) as [Hy1|Hy1].
  apply Heq.
  apply valid_exp with (1 := Hy1).
  now apply Z.le_trans with ey.
destruct (Zle_lt_or_eq _ _ He) as [He'|He'].
2: now apply Heq, f_equal.
apply Rle_trans with (bpow (ey - 1)).
2: now apply round_bounded_large_pos.
destruct (Zle_or_lt ex (fexp ex)) as [Hx1|Hx1].
  destruct (round_bounded_small_pos _ _ Hx1 Hex) as [-> | ->].
  apply bpow_ge_0.
  apply bpow_le.
  apply valid_exp, proj2 in Hx1.
  specialize (Hx1 ey).
  lia.
apply Rle_trans with (bpow ex).
now apply round_bounded_large_pos.
apply bpow_le.
now apply Z.lt_le_pred.
Qed.

Theorem round_generic :
  forall x,
  generic_format x ->
  round x = x.
Proof using valid_rnd.
intros x Hx.
unfold round.
rewrite scaled_mantissa_generic with (1 := Hx).
rewrite Zrnd_IZR.
now apply sym_eq.
Qed.

Theorem round_0 :
  round 0 = 0%R.
Proof using valid_rnd.
unfold round, scaled_mantissa.
rewrite Rmult_0_l.
rewrite Zrnd_IZR.
apply F2R_0.
Qed.

Theorem exp_small_round_0_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  round x = 0%R -> (ex <= fexp ex)%Z .
Proof using valid_rnd.
intros x ex H H1.
case (Zle_or_lt ex (fexp ex)); trivial; intros V.
contradict H1.
apply Rgt_not_eq.
apply Rlt_le_trans with (bpow (ex-1)).
apply bpow_gt_0.
apply (round_bounded_large_pos); assumption.
Qed.

Lemma generic_format_round_pos :
  forall x,
  (0 < x)%R ->
  generic_format (round x).
Proof using valid_exp_ valid_rnd.
intros x Hx0.
destruct (mag beta x) as (ex, Hex).
specialize (Hex (Rgt_not_eq _ _ Hx0)).
rewrite Rabs_pos_eq in Hex.
2: now apply Rlt_le.
destruct (Zle_or_lt ex (fexp ex)) as [He|He].

destruct (round_bounded_small_pos _ _ He Hex) as [Hr|Hr] ; rewrite Hr.
apply generic_format_0.
apply generic_format_bpow.
now apply valid_exp.

generalize (round_bounded_large_pos _ _ He Hex).
intros (Hr1, Hr2).
destruct (Rle_or_lt (bpow ex) (round x)) as [Hr|Hr].
rewrite <- (Rle_antisym _ _ Hr Hr2).
apply generic_format_bpow.
now apply valid_exp.
apply generic_format_F2R.
intros _.
rewrite (cexp_fexp_pos (F2R _) _ (conj Hr1 Hr)).
rewrite (cexp_fexp_pos _ _ Hex).
now apply Zeq_le.
Qed.

End Fcore_generic_round_pos.

Theorem round_ext :
  forall rnd1 rnd2,
  ( forall x, rnd1 x = rnd2 x ) ->
  forall x,
  round rnd1 x = round rnd2 x.
Proof using .
intros rnd1 rnd2 Hext x.
unfold round.
now rewrite Hext.
Qed.

Section Zround_opp.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Definition Zrnd_opp x := Z.opp (rnd (-x)).

Global Instance valid_rnd_opp : Valid_rnd Zrnd_opp.
Proof using valid_rnd.
Proof with auto with typeclass_instances.
split.

intros x y Hxy.
unfold Zrnd_opp.
apply Zopp_le_cancel.
rewrite 2!Z.opp_involutive.
apply Zrnd_le...
now apply Ropp_le_contravar.

intros n.
unfold Zrnd_opp.
rewrite <- opp_IZR, Zrnd_IZR...
apply Z.opp_involutive.
Qed.

Theorem round_opp :
  forall x,
  round rnd (- x) = Ropp (round Zrnd_opp x).
Proof using .
intros x.
unfold round.
rewrite <- F2R_Zopp, cexp_opp, scaled_mantissa_opp.
apply F2R_eq.
apply sym_eq.
exact (Z.opp_involutive _).
Qed.

End Zround_opp.

Global Instance valid_rnd_DN : Valid_rnd Zfloor.
Proof using .
split.
apply Zfloor_le.
apply Zfloor_IZR.
Qed.

Global Instance valid_rnd_UP : Valid_rnd Zceil.
Proof using .
split.
apply Zceil_le.
apply Zceil_IZR.
Qed.

Global Instance valid_rnd_ZR : Valid_rnd Ztrunc.
Proof using .
split.
apply Ztrunc_le.
apply Ztrunc_IZR.
Qed.

Global Instance valid_rnd_AW : Valid_rnd Zaway.
Proof using .
split.
apply Zaway_le.
apply Zaway_IZR.
Qed.

Section monotone.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_DN_or_UP :
  forall x,
  round rnd x = round Zfloor x \/ round rnd x = round Zceil x.
Proof using valid_rnd.
intros x.
unfold round.
destruct (Zrnd_DN_or_UP rnd (scaled_mantissa x)) as [Hx|Hx].
left.
now rewrite Hx.
right.
now rewrite Hx.
Qed.

Theorem round_ZR_or_AW :
  forall x,
  round rnd x = round Ztrunc x \/ round rnd x = round Zaway x.
Proof using valid_rnd.
intros x.
unfold round.
destruct (Zrnd_ZR_or_AW rnd (scaled_mantissa x)) as [Hx|Hx].
left.
now rewrite Hx.
right.
now rewrite Hx.
Qed.

Theorem round_le :
  forall x y, (x <= y)%R -> (round rnd x <= round rnd y)%R.
Proof using valid_exp_ valid_rnd.
Proof with auto with typeclass_instances.
intros x y Hxy.
destruct (total_order_T x 0) as [[Hx|Hx]|Hx].
3: now apply round_le_pos.

unfold round.
destruct (Rlt_or_le y 0) as [Hy|Hy].

rewrite <- (Ropp_involutive x), <- (Ropp_involutive y).
rewrite (scaled_mantissa_opp (-x)), (scaled_mantissa_opp (-y)).
rewrite (cexp_opp (-x)), (cexp_opp (-y)).
apply Ropp_le_cancel.
rewrite <- 2!F2R_Zopp.
apply (round_le_pos (Zrnd_opp rnd) (-y) (-x)).
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
now apply Ropp_le_contravar.

apply Rle_trans with 0%R.
apply F2R_le_0.
simpl.
rewrite <- (Zrnd_IZR rnd 0).
apply Zrnd_le...
simpl.
rewrite <- (Rmult_0_l (bpow (- fexp (mag beta x)))).
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply Rlt_le.
apply F2R_ge_0.
simpl.
rewrite <- (Zrnd_IZR rnd 0).
apply Zrnd_le...
apply Rmult_le_pos.
exact Hy.
apply bpow_ge_0.

rewrite Hx.
rewrite round_0...
apply F2R_ge_0.
simpl.
rewrite <- (Zrnd_IZR rnd 0).
apply Zrnd_le...
apply Rmult_le_pos.
now rewrite <- Hx.
apply bpow_ge_0.
Qed.

Theorem round_ge_generic :
  forall x y, generic_format x -> (x <= y)%R -> (x <= round rnd y)%R.
Proof using valid_exp_ valid_rnd.
intros x y Hx Hxy.
rewrite <- (round_generic rnd x Hx).
now apply round_le.
Qed.

Theorem round_le_generic :
  forall x y, generic_format y -> (x <= y)%R -> (round rnd x <= y)%R.
Proof using valid_exp_ valid_rnd.
intros x y Hy Hxy.
rewrite <- (round_generic rnd y Hy).
now apply round_le.
Qed.

End monotone.

Theorem round_abs_abs :
  forall P : R -> R -> Prop,
  ( forall rnd (Hr : Valid_rnd rnd) x, (0 <= x)%R -> P x (round rnd x) ) ->
  forall rnd {Hr : Valid_rnd rnd} x, P (Rabs x) (Rabs (round rnd x)).
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros P HP rnd Hr x.
destruct (Rle_or_lt 0 x) as [Hx|Hx].

rewrite 2!Rabs_pos_eq.
now apply HP.
rewrite <- (round_0 rnd).
now apply round_le.
exact Hx.

rewrite (Rabs_left _ Hx).
rewrite Rabs_left1.
pattern x at 2 ; rewrite <- Ropp_involutive.
rewrite round_opp.
rewrite Ropp_involutive.
apply HP...
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite <- (round_0 rnd).
apply round_le...
now apply Rlt_le.
Qed.

Theorem round_bounded_large :
  forall rnd {Hr : Valid_rnd rnd} x ex,
  (fexp ex < ex)%Z ->
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
  (bpow (ex - 1) <= Rabs (round rnd x) <= bpow ex)%R.
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros rnd Hr x ex He.
apply round_abs_abs...
clear rnd Hr x.
intros rnd' Hr x _.
apply round_bounded_large_pos...
Qed.

Theorem exp_small_round_0 :
  forall rnd {Hr : Valid_rnd rnd} x ex,
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
   round rnd x = 0%R -> (ex <= fexp ex)%Z .
Proof using valid_exp_.
intros rnd Hr x ex H1 H2.
generalize Rabs_R0.
rewrite <- H2 at 1.
apply (round_abs_abs (fun t rt => forall (ex : Z),
(bpow (ex - 1) <= t < bpow ex)%R ->
rt = 0%R -> (ex <= fexp ex)%Z)); trivial.
clear; intros rnd Hr x Hx.
now apply exp_small_round_0_pos.
Qed.

Section monotone_abs.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem abs_round_ge_generic :
  forall x y, generic_format x -> (x <= Rabs y)%R -> (x <= Rabs (round rnd y))%R.
Proof using valid_exp_ valid_rnd.
Proof with auto with typeclass_instances.
intros x y.
apply round_abs_abs...
clear rnd valid_rnd y.
intros rnd' Hrnd y Hy.
apply round_ge_generic...
Qed.

Theorem abs_round_le_generic :
  forall x y, generic_format y -> (Rabs x <= y)%R -> (Rabs (round rnd x) <= y)%R.
Proof using valid_exp_ valid_rnd.
Proof with auto with typeclass_instances.
intros x y.
apply round_abs_abs...
clear rnd valid_rnd x.
intros rnd' Hrnd x Hx.
apply round_le_generic...
Qed.

End monotone_abs.

Theorem round_DN_opp :
  forall x,
  round Zfloor (-x) = (- round Zceil x)%R.
Proof using .
intros x.
unfold round.
rewrite scaled_mantissa_opp.
rewrite <- F2R_Zopp.
unfold Zceil.
rewrite Z.opp_involutive.
now rewrite cexp_opp.
Qed.

Theorem round_UP_opp :
  forall x,
  round Zceil (-x) = (- round Zfloor x)%R.
Proof using .
intros x.
unfold round.
rewrite scaled_mantissa_opp.
rewrite <- F2R_Zopp.
unfold Zceil.
rewrite Ropp_involutive.
now rewrite cexp_opp.
Qed.

Theorem round_ZR_opp :
  forall x,
  round Ztrunc (- x) = Ropp (round Ztrunc x).
Proof using .
intros x.
unfold round.
rewrite scaled_mantissa_opp, cexp_opp, Ztrunc_opp.
apply F2R_Zopp.
Qed.

Theorem round_ZR_abs :
  forall x,
  round Ztrunc (Rabs x) = Rabs (round Ztrunc x).
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros x.
apply sym_eq.
unfold Rabs at 2.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite round_ZR_opp.
apply Rabs_left1.
rewrite <- (round_0 Ztrunc).
apply round_le...
now apply Rlt_le.
apply Rabs_pos_eq.
rewrite <- (round_0 Ztrunc).
apply round_le...
now apply Rge_le.
Qed.

Theorem round_AW_opp :
  forall x,
  round Zaway (- x) = Ropp (round Zaway x).
Proof using .
intros x.
unfold round.
rewrite scaled_mantissa_opp, cexp_opp, Zaway_opp.
apply F2R_Zopp.
Qed.

Theorem round_AW_abs :
  forall x,
  round Zaway (Rabs x) = Rabs (round Zaway x).
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros x.
apply sym_eq.
unfold Rabs at 2.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite round_AW_opp.
apply Rabs_left1.
rewrite <- (round_0 Zaway).
apply round_le...
now apply Rlt_le.
apply Rabs_pos_eq.
rewrite <- (round_0 Zaway).
apply round_le...
now apply Rge_le.
Qed.

Theorem round_ZR_DN :
  forall x,
  (0 <= x)%R ->
  round Ztrunc x = round Zfloor x.
Proof using .
intros x Hx.
unfold round, Ztrunc.
case Rlt_bool_spec.
intros H.
elim Rlt_not_le with (1 := H).
rewrite <- (Rmult_0_l (bpow (- cexp x))).
apply Rmult_le_compat_r with (2 := Hx).
apply bpow_ge_0.
easy.
Qed.

Theorem round_ZR_UP :
  forall x,
  (x <= 0)%R ->
  round Ztrunc x = round Zceil x.
Proof using .
intros x Hx.
unfold round, Ztrunc.
case Rlt_bool_spec.
easy.
intros [H|H].
elim Rlt_not_le with (1 := H).
rewrite <- (Rmult_0_l (bpow (- cexp x))).
apply Rmult_le_compat_r with (2 := Hx).
apply bpow_ge_0.
rewrite <- H.
now rewrite Zfloor_IZR, Zceil_IZR.
Qed.

Theorem round_AW_UP :
  forall x,
  (0 <= x)%R ->
  round Zaway x = round Zceil x.
Proof using .
intros x Hx.
unfold round, Zaway.
case Rlt_bool_spec.
intros H.
elim Rlt_not_le with (1 := H).
rewrite <- (Rmult_0_l (bpow (- cexp x))).
apply Rmult_le_compat_r with (2 := Hx).
apply bpow_ge_0.
easy.
Qed.

Theorem round_AW_DN :
  forall x,
  (x <= 0)%R ->
  round Zaway x = round Zfloor x.
Proof using .
intros x Hx.
unfold round, Zaway.
case Rlt_bool_spec.
easy.
intros [H|H].
elim Rlt_not_le with (1 := H).
rewrite <- (Rmult_0_l (bpow (- cexp x))).
apply Rmult_le_compat_r with (2 := Hx).
apply bpow_ge_0.
rewrite <- H.
now rewrite Zfloor_IZR, Zceil_IZR.
Qed.

Theorem generic_format_round :
  forall rnd { Hr : Valid_rnd rnd } x,
  generic_format (round rnd x).
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros rnd Zrnd x.
destruct (total_order_T x 0) as [[Hx|Hx]|Hx].
rewrite <- (Ropp_involutive x).
destruct (round_DN_or_UP rnd (- - x)) as [Hr|Hr] ; rewrite Hr.
rewrite round_DN_opp.
apply generic_format_opp.
apply generic_format_round_pos...
now apply Ropp_0_gt_lt_contravar.
rewrite round_UP_opp.
apply generic_format_opp.
apply generic_format_round_pos...
now apply Ropp_0_gt_lt_contravar.
rewrite Hx.
rewrite round_0...
apply generic_format_0.
now apply generic_format_round_pos.
Qed.

Theorem round_DN_pt :
  forall x,
  Rnd_DN_pt generic_format x (round Zfloor x).
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros x.
split.
apply generic_format_round...
split.
pattern x at 2 ; rewrite <- scaled_mantissa_mult_bpow.
unfold round, F2R.
simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Zfloor_lb.
intros g Hg Hgx.
apply round_ge_generic...
Qed.

Theorem generic_format_satisfies_any :
  satisfies_any generic_format.
Proof using valid_exp_.
split.

exact generic_format_0.
exact generic_format_opp.

intros x.
eexists.
apply round_DN_pt.
Qed.

Theorem round_UP_pt :
  forall x,
  Rnd_UP_pt generic_format x (round Zceil x).
Proof using valid_exp_.
intros x.
rewrite <- (Ropp_involutive x).
rewrite round_UP_opp.
apply Rnd_UP_pt_opp.
apply generic_format_opp.
apply round_DN_pt.
Qed.

Theorem round_ZR_pt :
  forall x,
  Rnd_ZR_pt generic_format x (round Ztrunc x).
Proof using valid_exp_.
intros x.
split ; intros Hx.
rewrite round_ZR_DN with (1 := Hx).
apply round_DN_pt.
rewrite round_ZR_UP with (1 := Hx).
apply round_UP_pt.
Qed.

Lemma round_DN_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  round Zfloor x = 0%R.
Proof using .
intros x ex Hx He.
rewrite <- (F2R_0 beta (cexp x)).
rewrite <- mantissa_DN_small_pos with (1 := Hx) (2 := He).
now rewrite <- cexp_fexp_pos with (1 := Hx).
Qed.

Theorem round_DN_UP_lt :
  forall x, ~ generic_format x ->
  (round Zfloor x < x < round Zceil x)%R.
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros x Fx.
assert (Hx:(round  Zfloor x <= x <= round Zceil x)%R).
split.
apply round_DN_pt.
apply round_UP_pt.
split.
  destruct Hx as [Hx _].
  apply Rnot_le_lt; intro Hle.
  assert (x = round Zfloor x) by now apply Rle_antisym.
  rewrite H in Fx.
  contradict Fx.
  apply generic_format_round...
destruct Hx as [_ Hx].
apply Rnot_le_lt; intro Hle.
assert (x = round Zceil x) by now apply Rle_antisym.
rewrite H in Fx.
contradict Fx.
apply generic_format_round...
Qed.

Lemma round_UP_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  round Zceil x = (bpow (fexp ex)).
Proof using .
intros x ex Hx He.
rewrite <- F2R_bpow.
rewrite <- mantissa_UP_small_pos with (1 := Hx) (2 := He).
now rewrite <- cexp_fexp_pos with (1 := Hx).
Qed.

Theorem generic_format_EM :
  forall x,
  generic_format x \/ ~generic_format x.
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros x.
destruct (Req_dec (round Zfloor x) x) as [Hx|Hx].
left.
rewrite <- Hx.
apply generic_format_round...
right.
intros H.
apply Hx.
apply round_generic...
Qed.

Section round_large.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma round_large_pos_ge_bpow :
  forall x e,
  (0 < round rnd x)%R ->
  (bpow e <= x)%R ->
  (bpow e <= round rnd x)%R.
Proof using valid_rnd.
intros x e Hd Hex.
destruct (mag beta x) as (ex, He).
assert (Hx: (0 < x)%R).
apply Rlt_le_trans with (2 := Hex).
apply bpow_gt_0.
specialize (He (Rgt_not_eq _ _ Hx)).
rewrite Rabs_pos_eq in He.
2: now apply Rlt_le.
apply Rle_trans with (bpow (ex - 1)).
apply bpow_le.
cut (e < ex)%Z.
lia.
apply (lt_bpow beta).
now apply Rle_lt_trans with (2 := proj2 He).
destruct (Zle_or_lt ex (fexp ex)).
destruct (round_bounded_small_pos rnd x ex H He) as [Hr|Hr].
rewrite Hr in Hd.
elim Rlt_irrefl with (1 := Hd).
rewrite Hr.
apply bpow_le.
lia.
apply (round_bounded_large_pos rnd x ex H He).
Qed.

End round_large.

Theorem mag_round_ZR :
  forall x,
  (round Ztrunc x <> 0)%R ->
  (mag beta (round Ztrunc x) = mag beta x :> Z).
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros x Zr.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, round_0...
apply mag_unique.
destruct (mag beta x) as (ex, Ex) ; simpl.
specialize (Ex Zx).
rewrite <- round_ZR_abs.
split.
apply round_large_pos_ge_bpow...
rewrite round_ZR_abs.
now apply Rabs_pos_lt.
apply Ex.
apply Rle_lt_trans with (2 := proj2 Ex).
rewrite round_ZR_DN.
apply round_DN_pt.
apply Rabs_pos.
Qed.

Theorem mag_round :
  forall rnd {Hrnd : Valid_rnd rnd} x,
  (round rnd x <> 0)%R ->
  (mag beta (round rnd x) = mag beta x :> Z) \/
  Rabs (round rnd x) = bpow (Z.max (mag beta x) (fexp (mag beta x))).
Proof using valid_exp_.
Proof with auto with typeclass_instances.
intros rnd Hrnd x.
destruct (round_ZR_or_AW rnd x) as [Hr|Hr] ; rewrite Hr ; clear Hr rnd Hrnd.
left.
now apply mag_round_ZR.
intros Zr.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, round_0...
destruct (mag beta x) as (ex, Ex) ; simpl.
specialize (Ex Zx).
rewrite <- mag_abs.
rewrite <- round_AW_abs.
destruct (Zle_or_lt ex (fexp ex)) as [He|He].
right.
rewrite Z.max_r with (1 := He).
rewrite round_AW_UP with (1 := Rabs_pos _).
now apply round_UP_small_pos.
destruct (round_bounded_large_pos Zaway _ ex He Ex) as (H1,[H2|H2]).
left.
apply mag_unique.
rewrite <- round_AW_abs, Rabs_Rabsolu.
now split.
right.
now rewrite Z.max_l with (1 := Zlt_le_weak _ _ He).
Qed.

Theorem mag_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  (mag beta (round Zfloor x) = mag beta x :> Z).
Proof using valid_exp_.
intros x Hd.
assert (0 < x)%R.
apply Rlt_le_trans with (1 := Hd).
apply round_DN_pt.
revert Hd.
rewrite <- round_ZR_DN.
intros Hd.
apply mag_round_ZR.
now apply Rgt_not_eq.
now apply Rlt_le.
Qed.

Theorem cexp_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  cexp (round Zfloor x) = cexp x.
Proof using valid_exp_.
intros x Hd.
apply (f_equal fexp).
now apply mag_DN.
Qed.

Theorem scaled_mantissa_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  scaled_mantissa (round Zfloor x) = IZR (Zfloor (scaled_mantissa x)).
Proof using valid_exp_.
intros x Hd.
unfold scaled_mantissa.
rewrite cexp_DN with (1 := Hd).
unfold round, F2R.
simpl.
now rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
Qed.

Theorem generic_N_pt_DN_or_UP :
  forall x f,
  Rnd_N_pt generic_format x f ->
  f = round Zfloor x \/ f = round Zceil x.
Proof using valid_exp_.
intros x f Hxf.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf).
left.
apply Rnd_DN_pt_unique with (1 := H).
apply round_DN_pt.
right.
apply Rnd_UP_pt_unique with (1 := H).
apply round_UP_pt.
Qed.

Section not_FTZ.

Class Exp_not_FTZ :=
  exp_not_FTZ : forall e, (fexp (fexp e + 1) <= fexp e)%Z.

Context { exp_not_FTZ_ : Exp_not_FTZ }.

Theorem subnormal_exponent :
  forall e x,
  (e <= fexp e)%Z ->
  generic_format x ->
  x = F2R (Float beta (Ztrunc (x * bpow (- fexp e))) (fexp e)).
Proof using exp_not_FTZ_ valid_exp_.
intros e x He Hx.
pattern x at 2 ; rewrite Hx.
unfold F2R at 2.
simpl.
rewrite Rmult_assoc, <- bpow_plus.
assert (H: IZR (Zpower beta (cexp x + - fexp e)) = bpow (cexp x + - fexp e)).
apply IZR_Zpower.
unfold cexp.
set (ex := mag beta x).
generalize (exp_not_FTZ ex).
generalize (proj2 (proj2 (valid_exp _) He) (fexp ex + 1)%Z).
lia.
rewrite <- H.
rewrite <- mult_IZR, Ztrunc_IZR.
unfold F2R.
simpl.
rewrite mult_IZR.
rewrite H.
rewrite Rmult_assoc, <- bpow_plus.
now ring_simplify (cexp x + - fexp e + fexp e)%Z.
Qed.

End not_FTZ.

Section monotone_exp.

Class Monotone_exp :=
  monotone_exp : forall ex ey, (ex <= ey)%Z -> (fexp ex <= fexp ey)%Z.

Context { monotone_exp_ : Monotone_exp }.

Global Instance monotone_exp_not_FTZ : Exp_not_FTZ.
Proof using monotone_exp_ valid_exp_.
intros e.
destruct (Z_lt_le_dec (fexp e) e) as [He|He].
apply monotone_exp.
now apply Zlt_le_succ.
now apply valid_exp.
Qed.

Lemma cexp_le_bpow :
  forall (x : R) (e : Z),
  x <> 0%R ->
  (Rabs x < bpow e)%R ->
  (cexp x <= fexp e)%Z.
Proof using monotone_exp_.
intros x e Zx Hx.
apply monotone_exp.
now apply mag_le_bpow.
Qed.

Lemma cexp_ge_bpow :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= Rabs x)%R ->
  (fexp e <= cexp x)%Z.
Proof using monotone_exp_.
intros x e Hx.
apply monotone_exp.
rewrite (Zsucc_pred e).
apply Zlt_le_succ.
now apply mag_gt_bpow.
Qed.

Lemma lt_cexp_pos :
  forall x y,
  (0 < y)%R ->
  (cexp x < cexp y)%Z ->
  (x < y)%R.
Proof using monotone_exp_.
intros x y Zy He.
unfold cexp in He.
apply (lt_mag beta) with (1 := Zy).
generalize (monotone_exp (mag beta y) (mag beta x)).
lia.
Qed.

Theorem lt_cexp :
  forall x y,
  (y <> 0)%R ->
  (cexp x < cexp y)%Z ->
  (Rabs x < Rabs y)%R.
Proof using monotone_exp_.
intros x y Zy He.
apply lt_cexp_pos.
now apply Rabs_pos_lt.
now rewrite 2!cexp_abs.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem mag_round_ge :
  forall x,
  round rnd x <> 0%R ->
  (mag beta x <= mag beta (round rnd x))%Z.
Proof using valid_exp_ valid_rnd.
Proof with auto with typeclass_instances.
intros x.
destruct (round_ZR_or_AW rnd x) as [H|H] ; rewrite H ; clear H ; intros Zr.
rewrite mag_round_ZR with (1 := Zr).
apply Z.le_refl.
apply mag_le_abs.
contradict Zr.
rewrite Zr.
apply round_0...
rewrite <- round_AW_abs.
rewrite round_AW_UP.
apply round_UP_pt.
apply Rabs_pos.
Qed.

Theorem cexp_round_ge :
  forall x,
  round rnd x <> 0%R ->
  (cexp x <= cexp (round rnd x))%Z.
Proof using monotone_exp_ valid_exp_ valid_rnd.
Proof with auto with typeclass_instances.
intros x Zr.
unfold cexp.
apply monotone_exp.
now apply mag_round_ge.
Qed.

End monotone_exp.

Section Znearest.

Variable choice : Z -> bool.

Definition Znearest x :=
  match Rcompare (x - IZR (Zfloor x)) (/2) with
  | Lt => Zfloor x
  | Eq => if choice (Zfloor x) then Zceil x else Zfloor x
  | Gt => Zceil x
  end.

Theorem Znearest_DN_or_UP :
  forall x,
  Znearest x = Zfloor x \/ Znearest x = Zceil x.
Proof using .
intros x.
unfold Znearest.
case Rcompare_spec ; intros _.
now left.
case choice.
now right.
now left.
now right.
Qed.

Theorem Znearest_ge_floor :
  forall x,
  (Zfloor x <= Znearest x)%Z.
Proof using .
intros x.
destruct (Znearest_DN_or_UP x) as [Hx|Hx] ; rewrite Hx.
apply Z.le_refl.
apply le_IZR.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
Qed.

Theorem Znearest_le_ceil :
  forall x,
  (Znearest x <= Zceil x)%Z.
Proof using .
intros x.
destruct (Znearest_DN_or_UP x) as [Hx|Hx] ; rewrite Hx.
apply le_IZR.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
apply Z.le_refl.
Qed.

Global Instance valid_rnd_N : Valid_rnd Znearest.
Proof using .
split.

intros x y Hxy.
destruct (Rle_or_lt (IZR (Zceil x)) y) as [H|H].
apply Z.le_trans with (1 := Znearest_le_ceil x).
apply Z.le_trans with (2 := Znearest_ge_floor y).
now apply Zfloor_lub.

assert (Hf: Zfloor y = Zfloor x).
apply Zfloor_imp.
split.
apply Rle_trans with (2 := Zfloor_lb y).
apply IZR_le.
now apply Zfloor_le.
apply Rlt_le_trans with (1 := H).
apply IZR_le.
apply Zceil_glb.
apply Rlt_le.
rewrite plus_IZR.
apply Zfloor_ub.

unfold Znearest at 1.
case Rcompare_spec ; intro Hx.

rewrite <- Hf.
apply Znearest_ge_floor.

unfold Znearest.
rewrite Hf.
case Rcompare_spec ; intro Hy.
elim Rlt_not_le with (1 := Hy).
rewrite <- Hx.
now apply Rplus_le_compat_r.
replace y with x.
apply Z.le_refl.
apply Rplus_eq_reg_l with (- IZR (Zfloor x))%R.
rewrite 2!(Rplus_comm (- (IZR (Zfloor x)))).
change (x - IZR (Zfloor x) = y - IZR (Zfloor x))%R.
now rewrite Hy.
apply Z.le_trans with (Zceil x).
case choice.
apply Z.le_refl.
apply le_IZR.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
now apply Zceil_le.

unfold Znearest.
rewrite Hf.
rewrite Rcompare_Gt.
now apply Zceil_le.
apply Rlt_le_trans with (1 := Hx).
now apply Rplus_le_compat_r.

intros n.
unfold Znearest.
rewrite Zfloor_IZR.
rewrite Rcompare_Lt.
easy.
unfold Rminus.
rewrite Rplus_opp_r.
apply Rinv_0_lt_compat.
now apply IZR_lt.
Qed.

Theorem Znearest_N_strict :
  forall x,
  (x - IZR (Zfloor x) <> /2)%R ->
  (Rabs (x - IZR (Znearest x)) < /2)%R.
Proof using .
intros x Hx.
unfold Znearest.
case Rcompare_spec ; intros H.
rewrite Rabs_pos_eq.
exact H.
apply Rle_0_minus.
apply Zfloor_lb.
now elim Hx.
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
rewrite Zceil_floor_neq.
rewrite plus_IZR.
apply Ropp_lt_cancel.
apply Rplus_lt_reg_l with 1%R.
replace (1 + -/2)%R with (/2)%R by field.
now replace (1 + - (IZR (Zfloor x) + 1 - x))%R with (x - IZR (Zfloor x))%R by ring.
apply Rlt_not_eq.
apply Rplus_lt_reg_l with (- IZR (Zfloor x))%R.
apply Rlt_trans with (/2)%R.
rewrite Rplus_opp_l.
apply Rinv_0_lt_compat.
now apply IZR_lt.
now rewrite <- (Rplus_comm x).
apply Rle_minus.
apply Zceil_ub.
Qed.

Theorem Znearest_half :
  forall x,
  (Rabs (x - IZR (Znearest x)) <= /2)%R.
Proof using .
intros x.
destruct (Req_dec (x - IZR (Zfloor x)) (/2)) as [Hx|Hx].
assert (K: (Rabs (/2) <= /2)%R).
apply Req_le.
apply Rabs_pos_eq.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
destruct (Znearest_DN_or_UP x) as [H|H] ; rewrite H ; clear H.
now rewrite Hx.
rewrite Zceil_floor_neq.
rewrite plus_IZR.
replace (x - (IZR (Zfloor x) + 1))%R with (x - IZR (Zfloor x) - 1)%R by ring.
rewrite Hx.
rewrite Rabs_minus_sym.
now replace (1 - /2)%R with (/2)%R by field.
apply Rlt_not_eq.
apply Rplus_lt_reg_l with (- IZR (Zfloor x))%R.
rewrite Rplus_opp_l, Rplus_comm.
fold (x - IZR (Zfloor x))%R.
rewrite Hx.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply Rlt_le.
now apply Znearest_N_strict.
Qed.

Theorem Znearest_imp :
  forall x n,
  (Rabs (x - IZR n) < /2)%R ->
  Znearest x = n.
Proof using .
intros x n Hd.
cut (Z.abs (Znearest x - n) < 1)%Z.
clear ; lia.
apply lt_IZR.
rewrite abs_IZR, minus_IZR.
replace (IZR (Znearest x) - IZR n)%R with (- (x - IZR (Znearest x)) + (x - IZR n))%R by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
simpl.
replace 1%R with (/2 + /2)%R by field.
apply Rplus_le_lt_compat with (2 := Hd).
rewrite Rabs_Ropp.
apply Znearest_half.
Qed.

Theorem round_N_pt :
  forall x,
  Rnd_N_pt generic_format x (round Znearest x).
Proof using valid_exp_.
intros x.
set (d := round Zfloor x).
set (u := round Zceil x).
set (mx := scaled_mantissa x).
set (bx := bpow (cexp x)).

assert (H: (Rabs (round Znearest x - x) <= Rmin (x - d) (u - x))%R).
pattern x at -1 ; rewrite <- scaled_mantissa_mult_bpow.
unfold d, u, round, F2R.
simpl.
fold mx bx.
rewrite <- 3!Rmult_minus_distr_r.
rewrite Rabs_mult, (Rabs_pos_eq bx).
2: apply bpow_ge_0.
rewrite <- Rmult_min_distr_r.
2: apply bpow_ge_0.
apply Rmult_le_compat_r.
apply bpow_ge_0.
unfold Znearest.
destruct (Req_dec (IZR (Zfloor mx)) mx) as [Hm|Hm].

rewrite Hm.
unfold Rminus at 2.
rewrite Rplus_opp_r.
rewrite Rcompare_Lt.
rewrite Hm.
unfold Rminus at -3.
rewrite Rplus_opp_r.
rewrite Rabs_R0.
unfold Rmin.
destruct (Rle_dec 0 (IZR (Zceil mx) - mx)) as [H|H].
apply Rle_refl.
apply Rle_0_minus.
apply Zceil_ub.
apply Rinv_0_lt_compat.
now apply IZR_lt.

rewrite Rcompare_floor_ceil_middle with (1 := Hm).
rewrite Rmin_compare.
assert (H: (Rabs (mx - IZR (Zfloor mx)) <= mx - IZR (Zfloor mx))%R).
rewrite Rabs_pos_eq.
apply Rle_refl.
apply Rle_0_minus.
apply Zfloor_lb.
case Rcompare_spec ; intros Hm'.
now rewrite Rabs_minus_sym.
case choice.
rewrite <- Hm'.
exact H.
now rewrite Rabs_minus_sym.
rewrite Rabs_pos_eq.
apply Rle_refl.
apply Rle_0_minus.
apply Zceil_ub.

apply Rnd_N_pt_DN_UP with d u.
apply generic_format_round.
auto with typeclass_instances.
now apply round_DN_pt.
now apply round_UP_pt.
apply Rle_trans with (1 := H).
apply Rmin_l.
apply Rle_trans with (1 := H).
apply Rmin_r.
Qed.

Theorem round_N_middle :
  forall x,
  (x - round Zfloor x = round Zceil x - x)%R ->
  round Znearest x = if choice (Zfloor (scaled_mantissa x)) then round Zceil x else round Zfloor x.
Proof using .
intros x.
pattern x at 1 4 ; rewrite <- scaled_mantissa_mult_bpow.
unfold round, Znearest, F2R.
simpl.
destruct (Req_dec (IZR (Zfloor (scaled_mantissa x))) (scaled_mantissa x)) as [Fx|Fx].

intros _.
rewrite <- Fx.
rewrite Zceil_IZR, Zfloor_IZR.
set (m := Zfloor (scaled_mantissa x)).
now case (Rcompare (IZR m - IZR m) (/ 2)) ; case (choice m).

intros H.
rewrite Rcompare_floor_ceil_middle with (1 := Fx).
rewrite Rcompare_Eq.
now case choice.
apply Rmult_eq_reg_r with (bpow (cexp x)).
now rewrite 2!Rmult_minus_distr_r.
apply Rgt_not_eq.
apply bpow_gt_0.
Qed.

Lemma round_N_small_pos :
  forall x,
  forall ex,
  (Raux.bpow beta (ex - 1) <= x < Raux.bpow beta ex)%R ->
  (ex < fexp ex)%Z ->
  (round Znearest x = 0)%R.
Proof using .
intros x ex Hex Hf.
unfold round, F2R, scaled_mantissa, cexp; simpl.
apply (Rmult_eq_reg_r (bpow (- fexp (mag beta x))));
  [|now apply Rgt_not_eq; apply bpow_gt_0].
rewrite Rmult_0_l, Rmult_assoc, <- bpow_plus.
replace (_ + - _)%Z with 0%Z by ring; simpl; rewrite Rmult_1_r.
apply IZR_eq.
apply Znearest_imp.
unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
assert (H : (x >= 0)%R).
{
 apply Rle_ge; apply Rle_trans with (bpow (ex - 1)); [|exact (proj1 Hex)].
  now apply bpow_ge_0.
}
assert (H' : (x * bpow (- fexp (mag beta x)) >= 0)%R).
{
 apply Rle_ge; apply Rmult_le_pos.
  -
 now apply Rge_le.
  -
 now apply bpow_ge_0.
}
rewrite Rabs_right; [|exact H'].
apply (Rmult_lt_reg_r (bpow (fexp (mag beta x)))); [now apply bpow_gt_0|].
rewrite Rmult_assoc, <- bpow_plus.
replace (- _ + _)%Z with 0%Z by ring; simpl; rewrite Rmult_1_r.
apply (Rlt_le_trans _ _ _ (proj2 Hex)).
apply Rle_trans with (bpow (fexp (mag beta x) - 1)).
-
 apply bpow_le.
  rewrite (mag_unique beta x ex); [lia|].
  now rewrite Rabs_right.
-
 unfold Zminus; rewrite bpow_plus.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r; [now apply bpow_ge_0|].
  unfold Raux.bpow, Z.pow_pos; simpl.
  rewrite Zmult_1_r.
  apply Rinv_le; [exact Rlt_0_2|].
  apply IZR_le.
  destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
Qed.

End Znearest.

Section rndNA.

Global Instance valid_rnd_NA : Valid_rnd (Znearest (Zle_bool 0)) := valid_rnd_N _.

Theorem round_NA_pt :
  forall x,
  Rnd_NA_pt generic_format x (round (Znearest (Zle_bool 0)) x).
Proof using valid_exp_.
intros x.
generalize (round_N_pt (Zle_bool 0) x).
set (f := round (Znearest (Zle_bool 0)) x).
intros Rxf.
destruct (Req_dec (x - round Zfloor x) (round Zceil x - x)) as [Hm|Hm].

apply Rnd_NA_pt_N.
exact generic_format_0.
exact Rxf.
destruct (Rle_or_lt 0 x) as [Hx|Hx].

rewrite Rabs_pos_eq with (1 := Hx).
rewrite Rabs_pos_eq.
unfold f.
rewrite round_N_middle with (1 := Hm).
rewrite Zle_bool_true.
apply (round_UP_pt x).
apply Zfloor_lub.
apply Rmult_le_pos with (1 := Hx).
apply bpow_ge_0.
apply Rnd_N_pt_ge_0 with (2 := Hx) (3 := Rxf).
exact generic_format_0.

rewrite Rabs_left with (1 := Hx).
rewrite Rabs_left1.
apply Ropp_le_contravar.
unfold f.
rewrite round_N_middle with (1 := Hm).
rewrite Zle_bool_false.
apply (round_DN_pt x).
apply lt_IZR.
apply Rle_lt_trans with (scaled_mantissa x).
apply Zfloor_lb.
simpl.
rewrite <- (Rmult_0_l (bpow (- cexp x))).
apply Rmult_lt_compat_r with (2 := Hx).
apply bpow_gt_0.
apply Rnd_N_pt_le_0 with (3 := Rxf).
exact generic_format_0.
now apply Rlt_le.

split.
apply Rxf.
intros g Rxg.
rewrite Rnd_N_pt_unique with (3 := Hm) (4 := Rxf) (5 := Rxg).
apply Rle_refl.
apply round_DN_pt.
apply round_UP_pt.
Qed.

End rndNA.

Notation Znearest0 := (Znearest (fun x => (Zlt_bool x 0))).

Section rndN0.

Global Instance valid_rnd_N0 : Valid_rnd Znearest0 := valid_rnd_N _.

Theorem round_N0_pt :
  forall x,
  Rnd_N0_pt generic_format x (round Znearest0 x).
Proof using valid_exp_.
intros x.
generalize (round_N_pt (fun t => Zlt_bool t 0) x).
set (f := round (Znearest (fun t => Zlt_bool t 0)) x).
intros Rxf.
destruct (Req_dec (x - round Zfloor x) (round Zceil x - x)) as [Hm|Hm].

apply Rnd_N0_pt_N.
apply generic_format_0.
exact Rxf.
destruct (Rle_or_lt 0 x) as [Hx|Hx].

rewrite Rabs_pos_eq with (1 := Hx).
rewrite Rabs_pos_eq.
unfold f.
rewrite round_N_middle with (1 := Hm).
rewrite Zlt_bool_false.
now apply round_DN_pt.
apply Zfloor_lub.
apply Rmult_le_pos with (1 := Hx).
apply bpow_ge_0.
apply Rnd_N_pt_ge_0 with (2 := Hx) (3 := Rxf).
apply generic_format_0.

rewrite Rabs_left with (1 := Hx).
rewrite Rabs_left1.
apply Ropp_le_contravar.
unfold f.
rewrite round_N_middle with (1 := Hm).
rewrite Zlt_bool_true.
now apply round_UP_pt.
apply lt_IZR.
apply Rle_lt_trans with (scaled_mantissa x).
apply Zfloor_lb.
simpl.
rewrite <- (Rmult_0_l (bpow (- (cexp x))%Z)%R).
apply Rmult_lt_compat_r with (2 := Hx).
apply bpow_gt_0.
apply Rnd_N_pt_le_0 with (3 := Rxf).
apply generic_format_0.
now apply Rlt_le.

split.
apply Rxf.
intros g Rxg.
rewrite Rnd_N_pt_unique with (3 := Hm) (4 := Rxf) (5 := Rxg).
apply Rle_refl.
apply round_DN_pt; easy.
apply round_UP_pt; easy.
Qed.

End rndN0.

Section rndN_opp.

Theorem Znearest_opp :
  forall choice x,
  Znearest choice (- x) = (- Znearest (fun t => negb (choice (- (t + 1))%Z)) x)%Z.
Proof using .
Proof with auto with typeclass_instances.
intros choice x.
destruct (Req_dec (IZR (Zfloor x)) x) as [Hx|Hx].
rewrite <- Hx.
rewrite <- opp_IZR.
rewrite 2!Zrnd_IZR...
unfold Znearest.
replace (- x - IZR (Zfloor (-x)))%R with (IZR (Zceil x) - x)%R.
rewrite Rcompare_ceil_floor_middle with (1 := Hx).
rewrite Rcompare_floor_ceil_middle with (1 := Hx).
rewrite Rcompare_sym.
rewrite <- Zceil_floor_neq with (1 := Hx).
unfold Zceil.
rewrite Ropp_involutive.
case Rcompare ; simpl ; trivial.
rewrite Z.opp_involutive.
case (choice (Zfloor (- x))) ; simpl ; trivial.
now rewrite Z.opp_involutive.
now rewrite Z.opp_involutive.
unfold Zceil.
rewrite opp_IZR.
apply Rplus_comm.
Qed.

Theorem round_N_opp :
  forall choice,
  forall x,
  round (Znearest choice) (-x) = (- round (Znearest (fun t => negb (choice (- (t + 1))%Z))) x)%R.
Proof using .
intros choice x.
unfold round, F2R.
simpl.
rewrite cexp_opp.
rewrite scaled_mantissa_opp.
rewrite Znearest_opp.
rewrite opp_IZR.
now rewrite Ropp_mult_distr_l_reverse.
Qed.

Lemma round_N0_opp :
  forall x,
  (round Znearest0 (- x) = - round Znearest0 x)%R.
Proof using .
intros x.
rewrite round_N_opp.
apply Ropp_eq_compat.
apply round_ext.
clear x; intro x.
unfold Znearest.
case_eq (Rcompare (x - IZR (Zfloor x)) (/ 2)); intro C;
[|reflexivity|reflexivity].
apply Rcompare_Eq_inv in C.
assert (H : negb (- (Zfloor x + 1) <? 0)%Z = (Zfloor x <? 0)%Z);
  [|now rewrite H].
rewrite negb_Zlt_bool.
case_eq (Zfloor x <? 0)%Z; intro C'.
apply Zlt_is_lt_bool in C'.
apply Zle_bool_true.
lia.
apply Z.ltb_ge in C'.
apply Zle_bool_false.
lia.
Qed.

End rndN_opp.

Lemma round_N_small :
  forall choice,
  forall x,
  forall ex,
  (Raux.bpow beta (ex - 1) <= Rabs x < Raux.bpow beta ex)%R ->
  (ex < fexp ex)%Z ->
  (round (Znearest choice) x = 0)%R.
Proof using .
intros choice x ex Hx Hex.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{
 now revert Hex; apply round_N_small_pos; revert Hx; rewrite Rabs_pos_eq.
}
rewrite <-(Ropp_involutive x), round_N_opp, <-Ropp_0; f_equal.
now revert Hex; apply round_N_small_pos; revert Hx; rewrite Rabs_left.
Qed.

End Format.

Section Inclusion.

Variables fexp1 fexp2 : Z -> Z.

Context { valid_exp1 : Valid_exp fexp1 }.
Context { valid_exp2 : Valid_exp fexp2 }.

Theorem generic_inclusion_mag :
  forall x,
  ( x <> 0%R -> (fexp2 (mag beta x) <= fexp1 (mag beta x))%Z ) ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using .
intros x He Fx.
rewrite Fx.
apply generic_format_F2R.
intros Zx.
rewrite <- Fx.
apply He.
contradict Zx.
rewrite Zx, scaled_mantissa_0.
apply Ztrunc_IZR.
Qed.

Theorem generic_inclusion_lt_ge :
  forall e1 e2,
  ( forall e, (e1 < e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x < bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using .
intros e1 e2 He x (Hx1,Hx2).
apply generic_inclusion_mag.
intros Zx.
apply He.
split.
now apply mag_gt_bpow.
now apply mag_le_bpow.
Qed.

Theorem generic_inclusion :
  forall e,
  (fexp2 e <= fexp1 e)%Z ->
  forall x,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using valid_exp1 valid_exp2.
Proof with auto with typeclass_instances.
intros e He x (Hx1,[Hx2|Hx2]).
apply generic_inclusion_mag.
now rewrite mag_unique with (1 := conj Hx1 Hx2).
intros Fx.
apply generic_format_abs_inv.
rewrite Hx2.
apply generic_format_bpow'...
apply Z.le_trans with (1 := He).
apply generic_format_bpow_inv...
rewrite <- Hx2.
now apply generic_format_abs.
Qed.

Theorem generic_inclusion_le_ge :
  forall e1 e2,
  (e1 < e2)%Z ->
  ( forall e, (e1 < e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x <= bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using valid_exp1 valid_exp2.
intros e1 e2 He' He x (Hx1,[Hx2|Hx2]).

apply generic_inclusion_mag.
intros Zx.
apply He.
split.
now apply mag_gt_bpow.
now apply mag_le_bpow.

apply generic_inclusion with (e := e2).
apply He.
split.
apply He'.
apply Z.le_refl.
rewrite Hx2.
split.
apply bpow_le.
apply Zle_pred.
apply Rle_refl.
Qed.

Theorem generic_inclusion_le :
  forall e2,
  ( forall e, (e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (Rabs x <= bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using valid_exp1 valid_exp2.
intros e2 He x [Hx|Hx].
apply generic_inclusion_mag.
intros Zx.
apply He.
now apply mag_le_bpow.
apply generic_inclusion with (e := e2).
apply He.
apply Z.le_refl.
rewrite Hx.
split.
apply bpow_le.
apply Zle_pred.
apply Rle_refl.
Qed.

Theorem generic_inclusion_ge :
  forall e1,
  ( forall e, (e1 < e)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using .
intros e1 He x Hx.
apply generic_inclusion_mag.
intros Zx.
apply He.
now apply mag_gt_bpow.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem generic_round_generic :
  forall x,
  generic_format fexp1 x ->
  generic_format fexp1 (round fexp2 rnd x).
Proof using valid_exp1 valid_exp2 valid_rnd.
Proof with auto with typeclass_instances.
intros x Gx.
apply generic_format_abs_inv.
apply generic_format_abs in Gx.
revert rnd valid_rnd x Gx.
refine (round_abs_abs _ (fun x y => generic_format fexp1 x -> generic_format fexp1 y) _).
intros rnd valid_rnd x [Hx|Hx] Gx.

generalize (mag_generic_gt _ x (Rgt_not_eq _ _ Hx) Gx).
unfold cexp.
destruct (mag beta x) as (ex,Ex) ; simpl.
specialize (Ex (Rgt_not_eq _ _ Hx)).
intros He'.
rewrite Rabs_pos_eq in Ex by now apply Rlt_le.
destruct (Zle_or_lt ex (fexp2 ex)) as [He|He].

destruct (round_bounded_small_pos fexp2 rnd x ex He Ex) as [Hr|Hr].
rewrite Hr.
apply generic_format_0.
rewrite Hr.
apply generic_format_bpow'...
apply Zlt_le_weak.
apply valid_exp_large with ex...

destruct (Zle_or_lt (cexp fexp2 x) (cexp fexp1 x)) as [He''|He''].

rewrite round_generic...
rewrite Gx.
apply generic_format_F2R.
fold (round fexp1 Ztrunc x).
intros Zx.
unfold cexp at 1.
rewrite mag_round_ZR...
contradict Zx.
apply eq_0_F2R with (1 := Zx).

destruct (round_bounded_large_pos fexp2 rnd x ex He Ex) as (Hr1,[Hr2|Hr2]).
apply generic_format_F2R.
intros Zx.
fold (round fexp2 rnd x).
unfold cexp at 1.
rewrite mag_unique_pos with (1 := conj Hr1 Hr2).
rewrite <- mag_unique_pos with (1 := Ex).
now apply Zlt_le_weak.
rewrite Hr2.
apply generic_format_bpow'...
now apply Zlt_le_weak.

rewrite <- Hx, round_0...
apply generic_format_0.
Qed.

End Inclusion.

End Generic.

Notation ZnearestA := (Znearest (Zle_bool 0)).

Section rndNA_opp.

Lemma round_NA_opp :
  forall beta : radix,
  forall (fexp : Z -> Z),
  forall x,
  (round beta fexp ZnearestA (- x) = - round beta fexp ZnearestA x)%R.
Proof.
intros beta fexp x.
rewrite round_N_opp.
apply Ropp_eq_compat.
apply round_ext.
clear x; intro x.
unfold Znearest.
case_eq (Rcompare (x - IZR (Zfloor x)) (/ 2)); intro C;
[|reflexivity|reflexivity].
apply Rcompare_Eq_inv in C.
assert (H : negb (0 <=? - (Zfloor x + 1))%Z = (0 <=? Zfloor x)%Z);
  [|now rewrite H].
rewrite negb_Zle_bool.
case_eq (0 <=? Zfloor x)%Z; intro C'.
-
 apply Zle_bool_imp_le in C'.
  apply Zlt_bool_true.
  lia.
-
 rewrite Z.leb_gt in C'.
  apply Zlt_bool_false.
  lia.
Qed.

End rndNA_opp.

Notation rndDN := Zfloor (only parsing).
Notation rndUP := Zceil (only parsing).
Notation rndZR := Ztrunc (only parsing).
Notation rndNA := ZnearestA (only parsing).

End Generic_fmt.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Generic_fmt.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Calc_DOT_Div.
Module Export Flocq.
Module Export Calc.
Module Export Div.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Generic_fmt Flocq.Core.Float_prop Flocq.Core.Digits Flocq.Calc.Bracket.

Set Implicit Arguments.
Set Strongly Strict Implicit.

Section Fcalc_div.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Lemma mag_div_F2R :
  forall m1 e1 m2 e2,
  (0 < m1)%Z -> (0 < m2)%Z ->
  let e := ((Zdigits beta m1 + e1) - (Zdigits beta m2 + e2))%Z in
  (e <= mag beta (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) <= e + 1)%Z.
Proof using .
intros m1 e1 m2 e2 Hm1 Hm2.
rewrite <- (mag_F2R_Zdigits beta m1 e1) by now apply Zgt_not_eq.
rewrite <- (mag_F2R_Zdigits beta m2 e2) by now apply Zgt_not_eq.
apply mag_div.
now apply F2R_neq_0, Zgt_not_eq.
now apply F2R_neq_0, Zgt_not_eq.
Qed.

Definition Fdiv_core m1 e1 m2 e2 e :=
  let (m1', m2') :=
    if Zle_bool e (e1 - e2)%Z
    then (m1 * Zpower beta (e1 - e2 - e), m2)%Z
    else (m1, m2 * Zpower beta (e - (e1 - e2)))%Z in
  let '(q, r) :=  Z.div_eucl m1' m2' in
  (q, new_location m2' r loc_Exact).

Theorem Fdiv_core_correct :
  forall m1 e1 m2 e2 e,
  (0 < m1)%Z -> (0 < m2)%Z ->
  let '(m, l) := Fdiv_core m1 e1 m2 e2 e in
  inbetween_float beta m e (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) l.
Proof using .
intros m1 e1 m2 e2 e Hm1 Hm2.
unfold Fdiv_core.
match goal with |- context [if ?b then ?b1 else ?b2] => set (m12 := if b then b1 else b2) end.
case_eq m12 ; intros m1' m2' Hm.
assert ((F2R (Float beta m1 e1) / F2R (Float beta m2 e2) = IZR m1' / IZR m2' * bpow e)%R /\ (0 < m2')%Z) as [Hf Hm2'].
{
 unfold F2R, Zminus ; simpl.
  destruct (Zle_bool e (e1 - e2)) eqn:He' ; injection Hm ; intros ; subst.
  -
 split ; try easy.
    apply Zle_bool_imp_le in He'.
    rewrite mult_IZR, IZR_Zpower by lia.
    unfold Zminus ; rewrite 2!bpow_plus, 2!bpow_opp.
    field.
    repeat split ; try apply Rgt_not_eq, bpow_gt_0.
    now apply IZR_neq, Zgt_not_eq.
  -
 apply Z.leb_gt in He'.
    split ; cycle 1.
    {
 apply Z.mul_pos_pos with (1 := Hm2).
      apply Zpower_gt_0 ; lia.
}
    rewrite mult_IZR, IZR_Zpower by lia.
    unfold Zminus ; rewrite bpow_plus, bpow_opp, bpow_plus, bpow_opp.
    field.
    repeat split ; try apply Rgt_not_eq, bpow_gt_0.
    now apply IZR_neq, Zgt_not_eq.
}
clearbody m12 ; clear Hm Hm1 Hm2.
generalize (Z_div_mod m1' m2' (Z.lt_gt _ _ Hm2')).
destruct (Z.div_eucl m1' m2') as (q, r).
intros (Hq, Hr).
rewrite Hf.
unfold inbetween_float, F2R.
simpl.
rewrite Hq, 2!plus_IZR, mult_IZR.
apply inbetween_mult_compat.
  apply bpow_gt_0.
destruct (Z_lt_le_dec 1 m2') as [Hm2''|Hm2''].
-
 replace 1%R with (IZR m2' * /IZR m2')%R.
  apply new_location_correct ; try easy.
  apply Rinv_0_lt_compat.
  now apply IZR_lt.
  constructor.
  field.
  now apply IZR_neq, Zgt_not_eq.
  field.
  now apply IZR_neq, Zgt_not_eq.
-
 assert (r = 0 /\ m2' = 1)%Z as [-> ->] by (clear -Hr Hm2'' ; lia).
  unfold Rdiv.
  rewrite Rmult_1_l, Rplus_0_r, Rinv_1, Rmult_1_r.
  now constructor.
Qed.

Definition Fdiv (x y : float beta) :=
  let (m1, e1) := x in
  let (m2, e2) := y in
  let e' := ((Zdigits beta m1 + e1) - (Zdigits beta m2 + e2))%Z in
  let e := Z.min (Z.min (fexp e') (fexp (e' + 1))) (e1 - e2) in
  let '(m, l) := Fdiv_core m1 e1 m2 e2 e in
  (m, e, l).

Theorem Fdiv_correct :
  forall x y,
  (0 < F2R x)%R -> (0 < F2R y)%R ->
  let '(m, e, l) := Fdiv x y in
  (e <= cexp beta fexp (F2R x / F2R y))%Z /\
  inbetween_float beta m e (F2R x / F2R y) l.
Proof using .
intros [m1 e1] [m2 e2] Hm1 Hm2.
apply gt_0_F2R in Hm1.
apply gt_0_F2R in Hm2.
unfold Fdiv.
generalize (mag_div_F2R m1 e1 m2 e2 Hm1 Hm2).
set (e := Zminus _ _).
set (e' := Z.min (Z.min (fexp e) (fexp (e + 1))) (e1 - e2)).
intros [H1 H2].
generalize (Fdiv_core_correct m1 e1 m2 e2 e' Hm1 Hm2).
destruct Fdiv_core as [m' l].
apply conj.
apply Z.le_trans with (1 := Z.le_min_l _ _).
unfold cexp.
destruct (Zle_lt_or_eq _ _ H1) as [H|H].
-
 replace (fexp (mag _ _)) with (fexp (e + 1)).
  apply Z.le_min_r.
  clear -H1 H2 H ; apply f_equal ; lia.
-
 replace (fexp (mag _ _)) with (fexp e).
  apply Z.le_min_l.
  clear -H1 H2 H ; apply f_equal ; lia.
Qed.

End Fcalc_div.

End Div.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Div.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Calc_DOT_Operations.
Module Export Flocq.
Module Export Calc.
Module Export Operations.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Float_prop.

Set Implicit Arguments.
Set Strongly Strict Implicit.

Section Float_ops.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Arguments Float {beta}.

Definition Falign (f1 f2 : float beta) :=
  let '(Float m1 e1) := f1 in
  let '(Float m2 e2) := f2 in
  if Zle_bool e1 e2
  then (m1, (m2 * Zpower beta (e2 - e1))%Z, e1)
  else ((m1 * Zpower beta (e1 - e2))%Z, m2, e2).

Theorem Falign_spec :
  forall f1 f2 : float beta,
  let '(m1, m2, e) := Falign f1 f2 in
  F2R f1 = @F2R beta (Float m1 e) /\ F2R f2 = @F2R beta (Float m2 e).
Proof using .
unfold Falign.
intros (m1, e1) (m2, e2).
generalize (Zle_cases e1 e2).
case (Zle_bool e1 e2) ; intros He ; split ; trivial.
now rewrite <- F2R_change_exp.
rewrite <- F2R_change_exp.
apply refl_equal.
lia.
Qed.

Theorem Falign_spec_exp:
  forall f1 f2 : float beta,
  snd (Falign f1 f2) = Z.min (Fexp f1) (Fexp f2).
Proof using .
intros (m1,e1) (m2,e2).
unfold Falign; simpl.
generalize (Zle_cases e1 e2);case (Zle_bool e1 e2); intros He.
case (Zmin_spec e1 e2); intros (H1,H2); easy.
case (Zmin_spec e1 e2); intros (H1,H2); easy.
Qed.

Definition Fopp (f1 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  Float (-m1)%Z e1.

Theorem F2R_opp :
  forall f1 : float beta,
  (F2R (Fopp f1) = -F2R f1)%R.
Proof using .
intros (m1,e1).
apply F2R_Zopp.
Qed.

Definition Fabs (f1 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  Float (Z.abs m1)%Z e1.

Theorem F2R_abs :
  forall f1 : float beta,
  (F2R (Fabs f1) = Rabs (F2R f1))%R.
Proof using .
intros (m1,e1).
apply F2R_Zabs.
Qed.

Definition Fplus (f1 f2 : float beta) : float beta :=
  let '(m1, m2 ,e) := Falign f1 f2 in
  Float (m1 + m2) e.

Theorem F2R_plus :
  forall f1 f2 : float beta,
  F2R (Fplus f1 f2) = (F2R f1 + F2R f2)%R.
Proof using .
intros f1 f2.
unfold Fplus.
generalize (Falign_spec f1 f2).
destruct (Falign f1 f2) as ((m1, m2), e).
intros (H1, H2).
rewrite H1, H2.
unfold F2R.
simpl.
rewrite plus_IZR.
apply Rmult_plus_distr_r.
Qed.

Theorem Fplus_same_exp :
  forall m1 m2 e,
  Fplus (Float m1 e) (Float m2 e) = Float (m1 + m2) e.
Proof using .
intros m1 m2 e.
unfold Fplus.
simpl.
now rewrite Zle_bool_refl, Zminus_diag, Zmult_1_r.
Qed.

Theorem Fexp_Fplus :
  forall f1 f2 : float beta,
  Fexp (Fplus f1 f2) = Z.min (Fexp f1) (Fexp f2).
Proof using .
intros f1 f2.
unfold Fplus.
rewrite <- Falign_spec_exp.
now destruct (Falign f1 f2) as ((p,q),e).
Qed.

Definition Fminus (f1 f2 : float beta) :=
  Fplus f1 (Fopp f2).

Theorem F2R_minus :
  forall f1 f2 : float beta,
  F2R (Fminus f1 f2) = (F2R f1 - F2R f2)%R.
Proof using .
intros f1 f2; unfold Fminus.
rewrite F2R_plus, F2R_opp.
ring.
Qed.

Theorem Fminus_same_exp :
  forall m1 m2 e,
  Fminus (Float m1 e) (Float m2 e) = Float (m1 - m2) e.
Proof using .
intros m1 m2 e.
unfold Fminus.
apply Fplus_same_exp.
Qed.

Definition Fmult (f1 f2 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  let '(Float m2 e2) := f2 in
  Float (m1 * m2) (e1 + e2).

Theorem F2R_mult :
  forall f1 f2 : float beta,
  F2R (Fmult f1 f2) = (F2R f1 * F2R f2)%R.
Proof using .
intros (m1, e1) (m2, e2).
unfold Fmult, F2R.
simpl.
rewrite mult_IZR, bpow_plus.
ring.
Qed.

End Float_ops.

End Operations.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Operations.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_Ulp.
Module Export Flocq.
Module Export Core.
Module Export Ulp.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Float_prop.

Section Fcore_ulp.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Lemma Z_le_dec_aux: forall x y : Z, (x <= y)%Z \/ ~ (x <= y)%Z.
Proof using .
intros.
destruct (Z_le_dec x y).
now left.
now right.
Qed.

Definition negligible_exp: option Z :=
  match (LPO_Z _ (fun z => Z_le_dec_aux z (fexp z))) with
   | inleft N => Some (proj1_sig N)
   | inright _ => None
 end.

Inductive negligible_exp_prop: option Z -> Prop :=
  | negligible_None: (forall n, (fexp n < n)%Z) -> negligible_exp_prop None
  | negligible_Some: forall n, (n <= fexp n)%Z -> negligible_exp_prop (Some n).

Lemma negligible_exp_spec: negligible_exp_prop negligible_exp.
Proof using .
unfold negligible_exp; destruct LPO_Z as [(n,Hn)|Hn].
now apply negligible_Some.
apply negligible_None.
intros n; specialize (Hn n); lia.
Qed.

Lemma negligible_exp_spec': (negligible_exp = None /\ forall n, (fexp n < n)%Z)
           \/ exists n, (negligible_exp = Some n /\ (n <= fexp n)%Z).
Proof using .
unfold negligible_exp; destruct LPO_Z as [(n,Hn)|Hn].
right; simpl; exists n; now split.
left; split; trivial.
intros n; specialize (Hn n); lia.
Qed.

Context { valid_exp : Valid_exp fexp }.

Lemma fexp_negligible_exp_eq: forall n m, (n <= fexp n)%Z -> (m <= fexp m)%Z -> fexp n = fexp m.
Proof using valid_exp.
intros n m Hn Hm.
case (Zle_or_lt n m); intros H.
apply valid_exp; lia.
apply sym_eq, valid_exp; lia.
Qed.

Definition ulp x := match Req_bool x 0 with
  | true   => match negligible_exp with
            | Some n => bpow (fexp n)
            | None => 0%R
            end
  | false  => bpow (cexp beta fexp x)
 end.

Lemma ulp_neq_0 :
  forall x, x <> 0%R ->
  ulp x = bpow (cexp beta fexp x).
Proof using .
intros  x Hx.
unfold ulp; case (Req_bool_spec x); trivial.
intros H; now contradict H.
Qed.

Notation F := (generic_format beta fexp).

Theorem ulp_opp :
  forall x, ulp (- x) = ulp x.
Proof using .
intros x.
unfold ulp.
case Req_bool_spec; intros H1.
rewrite Req_bool_true; trivial.
rewrite <- (Ropp_involutive x), H1; ring.
rewrite Req_bool_false.
now rewrite cexp_opp.
intros H2; apply H1; rewrite H2; ring.
Qed.

Theorem ulp_abs :
  forall x, ulp (Rabs x) = ulp x.
Proof using .
intros x.
unfold ulp; case (Req_bool_spec x 0); intros H1.
rewrite Req_bool_true; trivial.
now rewrite H1, Rabs_R0.
rewrite Req_bool_false.
now rewrite cexp_abs.
now apply Rabs_no_R0.
Qed.

Theorem ulp_ge_0:
  forall x, (0 <= ulp x)%R.
Proof using .
intros x; unfold ulp; case Req_bool_spec; intros.
case negligible_exp; intros.
apply bpow_ge_0.
apply Rle_refl.
apply bpow_ge_0.
Qed.

Theorem ulp_le_id:
  forall x,
    (0 < x)%R ->
    F x ->
    (ulp x <= x)%R.
Proof using .
intros x Zx Fx.
rewrite <- (Rmult_1_l (ulp x)).
pattern x at 2; rewrite Fx.
rewrite ulp_neq_0.
2: now apply Rgt_not_eq.
unfold F2R; simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le, (Zlt_le_succ 0).
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
Qed.

Theorem ulp_le_abs:
  forall x,
    (x <> 0)%R ->
    F x ->
    (ulp x <= Rabs x)%R.
Proof using .
intros x Zx Fx.
rewrite <- ulp_abs.
apply ulp_le_id.
now apply Rabs_pos_lt.
now apply generic_format_abs.
Qed.

Theorem round_UP_DN_ulp :
  forall x, ~ F x ->
  round beta fexp Zceil x = (round beta fexp Zfloor x + ulp x)%R.
Proof using .
intros x Fx.
rewrite ulp_neq_0.
unfold round.
simpl.
unfold F2R.
simpl.
rewrite Zceil_floor_neq.
rewrite plus_IZR.
simpl.
ring.
intros H.
apply Fx.
unfold generic_format, F2R.
simpl.
rewrite <- H.
rewrite Ztrunc_IZR.
rewrite H.
now rewrite scaled_mantissa_mult_bpow.
intros V; apply Fx.
rewrite V.
apply generic_format_0.
Qed.

Theorem ulp_canonical :
  forall m e,
  m <> 0%Z ->
  canonical beta fexp (Float beta m e) ->
  ulp (F2R (Float beta m e)) = bpow e.
Proof using .
intros m e Hm Hc.
rewrite ulp_neq_0 by now apply F2R_neq_0.
apply f_equal.
now apply sym_eq.
Qed.

Theorem ulp_bpow :
  forall e, ulp (bpow e) = bpow (fexp (e + 1)).
Proof using .
intros e.
rewrite ulp_neq_0.
apply f_equal.
apply cexp_fexp.
rewrite Rabs_pos_eq.
split.
ring_simplify (e + 1 - 1)%Z.
apply Rle_refl.
apply bpow_lt.
apply Zlt_succ.
apply bpow_ge_0.
apply Rgt_not_eq, Rlt_gt, bpow_gt_0.
Qed.

Lemma generic_format_ulp_0 :
  F (ulp 0).
Proof using valid_exp.
unfold ulp.
rewrite Req_bool_true; trivial.
case negligible_exp_spec.
intros _; apply generic_format_0.
intros n H1.
apply generic_format_bpow.
now apply valid_exp.
Qed.

Lemma generic_format_bpow_ge_ulp_0 :
  forall e, (ulp 0 <= bpow e)%R ->
  F (bpow e).
Proof using valid_exp.
intros e; unfold ulp.
rewrite Req_bool_true; trivial.
case negligible_exp_spec.
intros H1 _.
apply generic_format_bpow.
specialize (H1 (e+1)%Z); lia.
intros n H1 H2.
apply generic_format_bpow.
case (Zle_or_lt (e+1) (fexp (e+1))); intros H4.
absurd (e+1 <= e)%Z.
lia.
apply Z.le_trans with (1:=H4).
replace (fexp (e+1)) with (fexp n).
now apply le_bpow with beta.
now apply fexp_negligible_exp_eq.
lia.
Qed.

Lemma generic_format_ulp :
  Exp_not_FTZ fexp ->
  forall x, F (ulp x).
Proof using valid_exp.
unfold Exp_not_FTZ; intros H x.
case (Req_dec x 0); intros Hx.
rewrite Hx; apply generic_format_ulp_0.
rewrite (ulp_neq_0 _ Hx).
apply generic_format_bpow.
apply H.
Qed.

Lemma not_FTZ_generic_format_ulp :
  (forall x,  F (ulp x)) ->
  Exp_not_FTZ fexp.
Proof using .
intros H e.
specialize (H (bpow (e-1))).
rewrite ulp_neq_0 in H.
2: apply Rgt_not_eq, bpow_gt_0.
unfold cexp in H.
rewrite mag_bpow in H.
apply generic_format_bpow_inv' in H.
now replace (e-1+1)%Z with e in H by ring.
Qed.

Lemma ulp_ge_ulp_0 :
  Exp_not_FTZ fexp ->
  forall x, (ulp 0 <= ulp x)%R.
Proof using valid_exp.
unfold Exp_not_FTZ; intros H x.
case (Req_dec x 0); intros Hx.
rewrite Hx; now right.
unfold ulp at 1.
rewrite Req_bool_true; trivial.
case negligible_exp_spec'.
intros (H1,H2); rewrite H1; apply ulp_ge_0.
intros (n,(H1,H2)); rewrite H1.
rewrite ulp_neq_0; trivial.
apply bpow_le; unfold cexp.
generalize (mag beta x); intros l.
case (Zle_or_lt l (fexp l)); intros Hl.
rewrite (fexp_negligible_exp_eq n l); trivial; apply Z.le_refl.
case (Zle_or_lt (fexp n) (fexp l)); trivial; intros K.
absurd (fexp n <= fexp l)%Z.
lia.
apply Z.le_trans with (2:= H _).
apply Zeq_le, sym_eq, valid_exp; trivial.
lia.
Qed.

Lemma not_FTZ_ulp_ge_ulp_0:
  (forall x, (ulp 0 <= ulp x)%R) ->
  Exp_not_FTZ fexp.
Proof using valid_exp.
intros H e.
apply generic_format_bpow_inv' with beta.
apply generic_format_bpow_ge_ulp_0.
replace e with ((e-1)+1)%Z by ring.
rewrite <- ulp_bpow.
apply H.
Qed.

Lemma ulp_le_pos :
  forall { Hm : Monotone_exp fexp },
  forall x y: R,
  (0 <= x)%R -> (x <= y)%R ->
  (ulp x <= ulp y)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros Hm x y Hx Hxy.
destruct Hx as [Hx|Hx].
rewrite ulp_neq_0.
rewrite ulp_neq_0.
apply bpow_le.
apply Hm.
now apply mag_le.
apply Rgt_not_eq, Rlt_gt.
now apply Rlt_le_trans with (1:=Hx).
now apply Rgt_not_eq.
rewrite <- Hx.
apply ulp_ge_ulp_0.
apply monotone_exp_not_FTZ...
Qed.

Theorem ulp_le :
  forall { Hm : Monotone_exp fexp },
  forall x y: R,
  (Rabs x <= Rabs y)%R ->
  (ulp x <= ulp y)%R.
Proof using valid_exp.
intros Hm x y Hxy.
rewrite <- ulp_abs.
rewrite <- (ulp_abs y).
apply ulp_le_pos; trivial.
apply Rabs_pos.
Qed.

Theorem eq_0_round_0_negligible_exp :
   negligible_exp = None -> forall rnd {Vr: Valid_rnd rnd} x,
     round beta fexp rnd x = 0%R -> x = 0%R.
Proof using valid_exp.
intros H rnd Vr x Hx.
case (Req_dec x 0); try easy; intros Hx2.
absurd (Rabs (round beta fexp rnd x) = 0%R).
2: rewrite Hx, Rabs_R0; easy.
apply Rgt_not_eq.
apply Rlt_le_trans with (bpow (mag beta x - 1)).
apply bpow_gt_0.
apply abs_round_ge_generic; try assumption.
apply generic_format_bpow.
case negligible_exp_spec'; [intros (K1,K2)|idtac].
ring_simplify (mag beta x-1+1)%Z.
specialize (K2 (mag beta x)); now auto with zarith.
intros (n,(Hn1,Hn2)).
rewrite Hn1 in H; discriminate.
now apply bpow_mag_le.
Qed.

Definition pred_pos x :=
  if Req_bool x (bpow (mag beta x - 1)) then
    (x - bpow (fexp (mag beta x - 1)))%R
  else
    (x - ulp x)%R.

Definition succ x :=
  if (Rle_bool 0 x) then
    (x+ulp x)%R
  else
    (- pred_pos (-x))%R.

Definition pred x := (- succ (-x))%R.

Theorem pred_eq_pos :
  forall x, (0 <= x)%R ->
  pred x = pred_pos x.
Proof using .
intros x Hx; unfold pred, succ.
case Rle_bool_spec; intros Hx'.
assert (K:(x = 0)%R).
apply Rle_antisym; try assumption.
apply Ropp_le_cancel.
now rewrite Ropp_0.
rewrite K; unfold pred_pos.
rewrite Req_bool_false.
2: apply Rlt_not_eq, bpow_gt_0.
rewrite Ropp_0; ring.
now rewrite 2!Ropp_involutive.
Qed.

Theorem succ_eq_pos :
  forall x, (0 <= x)%R ->
  succ x = (x + ulp x)%R.
Proof using .
intros x Hx; unfold succ.
now rewrite Rle_bool_true.
Qed.

Theorem succ_opp :
  forall x, succ (-x) = (- pred x)%R.
Proof using .
intros x.
now apply sym_eq, Ropp_involutive.
Qed.

Theorem pred_opp :
  forall x, pred (-x) = (- succ x)%R.
Proof using .
intros x.
unfold pred.
now rewrite Ropp_involutive.
Qed.

Theorem pred_bpow :
  forall e, pred (bpow e) = (bpow e - bpow (fexp e))%R.
Proof using .
intros e.
rewrite pred_eq_pos by apply bpow_ge_0.
unfold pred_pos.
rewrite mag_bpow.
replace (e + 1 - 1)%Z with e by ring.
now rewrite Req_bool_true.
Qed.

Theorem id_m_ulp_ge_bpow :
  forall x e,  F x ->
  x <> ulp x ->
  (bpow e < x)%R ->
  (bpow e <= x - ulp x)%R.
Proof using .
intros x e Fx Hx' Hx.

assert (1 <= Ztrunc (scaled_mantissa beta fexp x))%Z.
assert (0 <  Ztrunc (scaled_mantissa beta fexp x))%Z.
apply gt_0_F2R with beta (cexp beta fexp x).
rewrite <- Fx.
apply Rle_lt_trans with (2:=Hx).
apply bpow_ge_0.
lia.
case (Zle_lt_or_eq _ _ H); intros Hm.

pattern x at 1 ; rewrite Fx.
rewrite ulp_neq_0.
unfold F2R.
simpl.
pattern (bpow (cexp beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_minus_distr_r.
rewrite <- minus_IZR.
apply bpow_le_F2R_m1.
easy.
now rewrite <- Fx.
apply Rgt_not_eq, Rlt_gt.
apply Rlt_trans with (2:=Hx), bpow_gt_0.

contradict Hx'.
pattern x at 1; rewrite Fx.
rewrite  <- Hm.
rewrite ulp_neq_0.
unfold F2R; simpl.
now rewrite Rmult_1_l.
apply Rgt_not_eq, Rlt_gt.
apply Rlt_trans with (2:=Hx), bpow_gt_0.
Qed.

Theorem id_p_ulp_le_bpow :
  forall x e, (0 < x)%R -> F x ->
  (x < bpow e)%R ->
  (x + ulp x <= bpow e)%R.
Proof using .
intros x e Zx Fx Hx.
pattern x at 1 ; rewrite Fx.
rewrite ulp_neq_0.
unfold F2R.
simpl.
pattern (bpow (cexp beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
rewrite <- plus_IZR.
apply F2R_p1_le_bpow.
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
now rewrite <- Fx.
now apply Rgt_not_eq.
Qed.

Lemma generic_format_pred_aux1:
  forall x, (0 < x)%R -> F x ->
  x <> bpow (mag beta x - 1) ->
  F (x - ulp x).
Proof using .
intros x Zx Fx Hx.
destruct (mag beta x) as (ex, Ex).
simpl in Hx.
specialize (Ex (Rgt_not_eq _ _ Zx)).
assert (Ex' : (bpow (ex - 1) < x < bpow ex)%R).
rewrite Rabs_pos_eq in Ex.
destruct Ex as (H,H'); destruct H; split; trivial.
contradict Hx; easy.
now apply Rlt_le.
unfold generic_format, scaled_mantissa, cexp.
rewrite mag_unique with beta (x - ulp x)%R ex.
pattern x at 1 3 ; rewrite Fx.
rewrite ulp_neq_0.
unfold scaled_mantissa.
rewrite cexp_fexp with (1 := Ex).
unfold F2R.
simpl.
rewrite Rmult_minus_distr_r.
rewrite Rmult_assoc.
rewrite <- bpow_plus, Zplus_opp_r, Rmult_1_r.
change (bpow 0) with 1%R.
rewrite <- minus_IZR.
rewrite Ztrunc_IZR.
rewrite minus_IZR.
rewrite Rmult_minus_distr_r.
now rewrite Rmult_1_l.
now apply Rgt_not_eq.
rewrite Rabs_pos_eq.
split.
apply id_m_ulp_ge_bpow; trivial.
rewrite ulp_neq_0.
intro H.
assert (ex-1 < cexp beta fexp x  < ex)%Z.
split ; apply (lt_bpow beta) ; rewrite <- H ; easy.
clear -H0.
lia.
now apply Rgt_not_eq.
apply Ex'.
apply Rle_lt_trans with (2 := proj2 Ex').
pattern x at 3 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
rewrite <-Ropp_0.
apply Ropp_le_contravar.
apply ulp_ge_0.
apply Rle_0_minus.
pattern x at 2; rewrite Fx.
rewrite ulp_neq_0.
unfold F2R; simpl.
pattern (bpow (cexp beta fexp x)) at 1; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le.
assert (0 <  Ztrunc (scaled_mantissa beta fexp x))%Z.
apply gt_0_F2R with beta (cexp beta fexp x).
rewrite <- Fx.
apply Rle_lt_trans with (2:=proj1 Ex').
apply bpow_ge_0.
lia.
now apply Rgt_not_eq.
Qed.

Lemma generic_format_pred_aux2 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x = bpow (e - 1) ->
  F (x - bpow (fexp (e - 1))).
Proof using valid_exp.
intros x Zx Fx e Hx.
pose (f:=(x - bpow (fexp (e - 1)))%R).
fold f.
assert (He:(fexp (e-1) <= e-1)%Z).
apply generic_format_bpow_inv with beta; trivial.
rewrite <- Hx; assumption.
case (Zle_lt_or_eq _ _ He); clear He; intros He.
assert (f = F2R (Float beta (Zpower beta (e-1-(fexp (e-1))) -1) (fexp (e-1))))%R.
unfold f; rewrite Hx.
unfold F2R; simpl.
rewrite minus_IZR, IZR_Zpower.
rewrite Rmult_minus_distr_r, Rmult_1_l.
rewrite <- bpow_plus.
now replace (e - 1 - fexp (e - 1) + fexp (e - 1))%Z with (e-1)%Z by ring.
lia.
rewrite H.
apply generic_format_F2R.
intros _.
apply Zeq_le.
apply cexp_fexp.
rewrite <- H.
unfold f; rewrite Hx.
rewrite Rabs_right.
split.
apply Rplus_le_reg_l with (bpow (fexp (e-1))).
ring_simplify.
apply Rle_trans with (bpow (e - 2) + bpow (e - 2))%R.
apply Rplus_le_compat ; apply bpow_le ; lia.
apply Rle_trans with (2*bpow (e - 2))%R;[right; ring|idtac].
apply Rle_trans with (bpow 1*bpow (e - 2))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace (bpow 1) with (IZR beta).
apply IZR_le.
apply <- Zle_is_le_bool.
now destruct beta.
simpl.
unfold Zpower_pos; simpl.
now rewrite Zmult_1_r.
rewrite <- bpow_plus.
replace (1+(e-2))%Z with (e-1)%Z by ring.
now right.
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
apply Rle_ge; apply Rle_0_minus.
apply bpow_le.
lia.
replace f with 0%R.
apply generic_format_0.
unfold f.
rewrite Hx, He.
ring.
Qed.

Lemma generic_format_succ_aux1 :
  forall x, (0 < x)%R -> F x ->
  F (x + ulp x).
Proof using valid_exp.
intros x Zx Fx.
destruct (mag beta x) as (ex, Ex).
specialize (Ex (Rgt_not_eq _ _ Zx)).
assert (Ex' := Ex).
rewrite Rabs_pos_eq in Ex'.
destruct (id_p_ulp_le_bpow x ex) ; try easy.
unfold generic_format, scaled_mantissa, cexp.
rewrite mag_unique with beta (x + ulp x)%R ex.
pattern x at 1 3 ; rewrite Fx.
rewrite ulp_neq_0.
unfold scaled_mantissa.
rewrite cexp_fexp with (1 := Ex).
unfold F2R.
simpl.
rewrite Rmult_plus_distr_r.
rewrite Rmult_assoc.
rewrite <- bpow_plus, Zplus_opp_r, Rmult_1_r.
change (bpow 0) with 1%R.
rewrite <- plus_IZR.
rewrite Ztrunc_IZR.
rewrite plus_IZR.
rewrite Rmult_plus_distr_r.
now rewrite Rmult_1_l.
now apply Rgt_not_eq.
rewrite Rabs_pos_eq.
split.
apply Rle_trans with (1 := proj1 Ex').
pattern x at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
apply ulp_ge_0.
exact H.
apply Rplus_le_le_0_compat.
now apply Rlt_le.
apply ulp_ge_0.
rewrite H.
apply generic_format_bpow.
apply valid_exp.
destruct (Zle_or_lt ex (fexp ex)) ; trivial.
elim Rlt_not_le with (1 := Zx).
rewrite Fx.
replace (Ztrunc (scaled_mantissa beta fexp x)) with Z0.
rewrite F2R_0.
apply Rle_refl.
unfold scaled_mantissa.
rewrite cexp_fexp with (1 := Ex).
destruct (mantissa_small_pos beta fexp x ex) ; trivial.
rewrite Ztrunc_floor.
apply sym_eq.
apply Zfloor_imp.
split.
now apply Rlt_le.
exact H2.
now apply Rlt_le.
now apply Rlt_le.
Qed.

Lemma generic_format_pred_pos :
  forall x, F x -> (0 < x)%R ->
  F (pred_pos x).
Proof using valid_exp.
intros x Fx Zx.
unfold pred_pos; case Req_bool_spec; intros H.
now apply generic_format_pred_aux2.
now apply generic_format_pred_aux1.
Qed.

Theorem generic_format_succ :
  forall x, F x ->
  F (succ x).
Proof using valid_exp.
intros x Fx.
unfold succ; case Rle_bool_spec; intros Zx.
destruct Zx as [Zx|Zx].
now apply generic_format_succ_aux1.
rewrite <- Zx, Rplus_0_l.
apply generic_format_ulp_0.
apply generic_format_opp.
apply generic_format_pred_pos.
now apply generic_format_opp.
now apply Ropp_0_gt_lt_contravar.
Qed.

Theorem generic_format_pred :
  forall x, F x ->
  F (pred x).
Proof using valid_exp.
intros x Fx.
unfold pred.
apply generic_format_opp.
apply generic_format_succ.
now apply generic_format_opp.
Qed.

Lemma pred_pos_lt_id :
  forall x, (x <> 0)%R ->
  (pred_pos x < x)%R.
Proof using .
intros x Zx.
unfold pred_pos.
case Req_bool_spec; intros H.

rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.

rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
rewrite ulp_neq_0; trivial.
apply bpow_gt_0.
Qed.

Theorem succ_gt_id :
  forall x, (x <> 0)%R ->
  (x < succ x)%R.
Proof using .
intros x Zx; unfold succ.
case Rle_bool_spec; intros Hx.
pattern x at 1; rewrite <- (Rplus_0_r x).
apply Rplus_lt_compat_l.
rewrite ulp_neq_0; trivial.
apply bpow_gt_0.
pattern x at 1; rewrite <- (Ropp_involutive x).
apply Ropp_lt_contravar.
apply pred_pos_lt_id.
auto with real.
Qed.

Theorem pred_lt_id :
  forall x,  (x <> 0)%R ->
  (pred x < x)%R.
Proof using .
intros x Zx; unfold pred.
pattern x at 2; rewrite <- (Ropp_involutive x).
apply Ropp_lt_contravar.
apply succ_gt_id.
auto with real.
Qed.

Theorem succ_ge_id :
  forall x, (x <= succ x)%R.
Proof using .
intros x; case (Req_dec x 0).
intros V; rewrite V.
unfold succ; rewrite Rle_bool_true;[idtac|now right].
rewrite Rplus_0_l; apply ulp_ge_0.
intros; left; now apply succ_gt_id.
Qed.

Theorem pred_le_id :
  forall x, (pred x <= x)%R.
Proof using .
intros x; unfold pred.
pattern x at 2; rewrite <- (Ropp_involutive x).
apply Ropp_le_contravar.
apply succ_ge_id.
Qed.

Lemma pred_pos_ge_0 :
  forall x,
  (0 < x)%R -> F x -> (0 <= pred_pos x)%R.
Proof using valid_exp.
intros x Zx Fx.
unfold pred_pos.
case Req_bool_spec; intros H.

apply Rle_0_minus.
rewrite H.
apply bpow_le.
destruct (mag beta x) as (ex,Ex) ; simpl.
rewrite mag_bpow.
ring_simplify (ex - 1 + 1 - 1)%Z.
apply generic_format_bpow_inv with beta; trivial.
simpl in H.
rewrite <- H; assumption.
apply Rle_0_minus.
now apply ulp_le_id.
Qed.

Theorem pred_ge_0 :
  forall x,
  (0 < x)%R -> F x -> (0 <= pred x)%R.
Proof using valid_exp.
intros x Zx Fx.
rewrite pred_eq_pos.
now apply pred_pos_ge_0.
now left.
Qed.

Lemma pred_pos_plus_ulp_aux1 :
  forall x, (0 < x)%R -> F x ->
  x <> bpow (mag beta x - 1) ->
  ((x - ulp x) + ulp (x-ulp x) = x)%R.
Proof using .
intros x Zx Fx Hx.
replace (ulp (x - ulp x)) with (ulp x).
ring.
assert (H : x <> 0%R) by now apply Rgt_not_eq.
assert (H' : x <> bpow (cexp beta fexp x)).
unfold cexp ; intros M.
case_eq (mag beta x); intros ex Hex T.
assert (Lex:(mag_val beta x (mag beta x) = ex)%Z).
rewrite T; reflexivity.
rewrite Lex in *.
clear T; simpl in *; specialize (Hex H).
rewrite Rabs_pos_eq in Hex by now apply Rlt_le.
assert (ex - 1 < fexp ex < ex)%Z.
  split ; apply (lt_bpow beta) ; rewrite <- M by easy.
  lra.
  apply Hex.
lia.
rewrite 2!ulp_neq_0 by lra.
apply f_equal.
unfold cexp ; apply f_equal.
case_eq (mag beta x); intros ex Hex T.
assert (Lex:(mag_val beta x (mag beta x) = ex)%Z).
rewrite T; reflexivity.
rewrite Lex in *; simpl in *; clear T.
specialize (Hex H).
apply sym_eq, mag_unique.
rewrite Rabs_right.
rewrite Rabs_right in Hex.
2: apply Rle_ge; apply Rlt_le; easy.
split.
destruct Hex as ([H1|H1],H2).
apply Rle_trans with (x-ulp x)%R.
apply id_m_ulp_ge_bpow; trivial.
rewrite ulp_neq_0; trivial.
rewrite ulp_neq_0; trivial.
right; unfold cexp; now rewrite Lex.
lra.
apply Rle_lt_trans with (2:=proj2 Hex).
rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply bpow_ge_0.
apply Rle_ge.
apply Rle_0_minus.
rewrite Fx.
unfold F2R, cexp; simpl.
rewrite Lex.
pattern (bpow (fexp ex)) at 1; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le, (Zlt_le_succ 0).
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
Qed.

Lemma pred_pos_plus_ulp_aux2 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x =  bpow (e - 1) ->
  (x - bpow (fexp (e-1)) <> 0)%R ->
  ((x - bpow (fexp (e-1))) + ulp (x - bpow (fexp (e-1))) = x)%R.
Proof using valid_exp.
intros x Zx Fx e Hxe Zp.
replace (ulp (x - bpow (fexp (e - 1)))) with (bpow (fexp (e - 1))).
ring.
assert (He:(fexp (e-1) <= e-1)%Z).
apply generic_format_bpow_inv with beta; trivial.
rewrite <- Hxe; assumption.
case (Zle_lt_or_eq _ _ He); clear He; intros He.

rewrite ulp_neq_0; trivial.
apply f_equal.
unfold cexp ; apply f_equal.
apply sym_eq.
apply mag_unique.
rewrite Rabs_right.
split.
apply Rplus_le_reg_l with (bpow (fexp (e-1))).
ring_simplify.
apply Rle_trans with (bpow (e - 2) + bpow (e - 2))%R.
apply Rplus_le_compat; apply bpow_le; lia.
apply Rle_trans with (2*bpow (e - 2))%R;[right; ring|idtac].
apply Rle_trans with (bpow 1*bpow (e - 2))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace (bpow 1) with (IZR beta).
apply IZR_le.
apply <- Zle_is_le_bool.
now destruct beta.
simpl.
unfold Zpower_pos; simpl.
now rewrite Zmult_1_r.
rewrite <- bpow_plus.
replace (1+(e-2))%Z with (e-1)%Z by ring.
now right.
rewrite <- Rplus_0_r, Hxe.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
apply Rle_ge; apply Rle_0_minus.
rewrite Hxe.
apply bpow_le.
lia.

contradict Zp.
rewrite Hxe, He; ring.
Qed.

Lemma pred_pos_plus_ulp_aux3 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x =  bpow (e - 1) ->
  (x - bpow (fexp (e-1)) = 0)%R ->
  (ulp 0 = x)%R.
Proof using valid_exp.
intros x Hx Fx e H1 H2.
assert (H3:(x = bpow (fexp (e - 1)))).
now apply Rminus_diag_uniq.
assert (H4: (fexp (e-1) = e-1)%Z).
apply bpow_inj with beta.
now rewrite <- H1.
unfold ulp; rewrite Req_bool_true; trivial.
case negligible_exp_spec.
intros K.
specialize (K (e-1)%Z).
contradict K; lia.
intros n Hn.
rewrite H3; apply f_equal.
case (Zle_or_lt n (e-1)); intros H6.
apply valid_exp; lia.
apply sym_eq, valid_exp; lia.
Qed.

Lemma pred_pos_plus_ulp :
  forall x, (0 < x)%R -> F x ->
  (pred_pos x + ulp (pred_pos x) = x)%R.
Proof using valid_exp.
intros x Zx Fx.
unfold pred_pos.
case Req_bool_spec; intros H.
case (Req_EM_T (x - bpow (fexp (mag_val beta x (mag beta x) -1))) 0); intros H1.
rewrite H1, Rplus_0_l.
now apply pred_pos_plus_ulp_aux3.
now apply pred_pos_plus_ulp_aux2.
now apply pred_pos_plus_ulp_aux1.
Qed.

Theorem pred_plus_ulp :
  forall x, (0 < x)%R -> F x ->
  (pred x + ulp (pred x))%R = x.
Proof using valid_exp.
intros x Hx Fx.
rewrite pred_eq_pos.
now apply pred_pos_plus_ulp.
now apply Rlt_le.
Qed.

Theorem mag_plus_eps :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  mag beta (x + eps) = mag beta x :> Z.
Proof using .
intros x Zx Fx eps Heps.
destruct (mag beta x) as (ex, He).
simpl.
specialize (He (Rgt_not_eq _ _ Zx)).
apply mag_unique.
rewrite Rabs_pos_eq.
rewrite Rabs_pos_eq in He.
split.
apply Rle_trans with (1 := proj1 He).
pattern x at 1 ; rewrite <- Rplus_0_r.
now apply Rplus_le_compat_l.
apply Rlt_le_trans with (x + ulp x)%R.
now apply Rplus_lt_compat_l.
pattern x at 1 ; rewrite Fx.
rewrite ulp_neq_0.
unfold F2R.
simpl.
pattern (bpow (cexp beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
rewrite <- plus_IZR.
apply F2R_p1_le_bpow.
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
now rewrite <- Fx.
now apply Rgt_not_eq.
now apply Rlt_le.
apply Rplus_le_le_0_compat.
now apply Rlt_le.
apply Heps.
Qed.

Theorem round_DN_plus_eps_pos :
  forall x, (0 <= x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  round beta fexp Zfloor (x + eps) = x.
Proof using valid_exp.
intros x Zx Fx eps Heps.
destruct Zx as [Zx|Zx].

pattern x at 2 ; rewrite Fx.
unfold round.
unfold scaled_mantissa.
simpl.
unfold cexp at 1 2.
rewrite mag_plus_eps ; trivial.
apply (f_equal (fun m => F2R (Float beta m _))).
rewrite Ztrunc_floor.
apply Zfloor_imp.
split.
apply (Rle_trans _ _ _ (Zfloor_lb _)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
pattern x at 1 ; rewrite <- Rplus_0_r.
now apply Rplus_le_compat_l.
apply Rlt_le_trans with ((x + ulp x) * bpow (- cexp beta fexp x))%R.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
now apply Rplus_lt_compat_l.
rewrite Rmult_plus_distr_r.
rewrite plus_IZR.
apply Rplus_le_compat.
pattern x at 1 3 ; rewrite Fx.
unfold F2R.
simpl.
rewrite Rmult_assoc.
rewrite <- bpow_plus.
rewrite Zplus_opp_r.
rewrite Rmult_1_r.
rewrite Zfloor_IZR.
apply Rle_refl.
rewrite ulp_neq_0.
2: now apply Rgt_not_eq.
rewrite <- bpow_plus.
rewrite Zplus_opp_r.
apply Rle_refl.
apply Rmult_le_pos.
now apply Rlt_le.
apply bpow_ge_0.

rewrite <- Zx, Rplus_0_l; rewrite <- Zx in Heps.
case (proj1 Heps); intros P.
unfold round, scaled_mantissa, cexp.
revert Heps; unfold ulp.
rewrite Req_bool_true; trivial.
case negligible_exp_spec.
intros _ (H1,H2).
exfalso ; lra.
intros n Hn H.
assert (fexp (mag beta eps) = fexp n).
apply valid_exp; try assumption.
cut (mag beta eps-1 < fexp n)%Z.
lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (2:=proj2 H).
destruct (mag beta eps) as (e,He).
simpl; rewrite Rabs_pos_eq in He.
now apply He, Rgt_not_eq.
now left.
replace (Zfloor (eps * bpow (- fexp (mag beta eps)))) with 0%Z.
unfold F2R; simpl; ring.
apply sym_eq, Zfloor_imp.
split.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
apply Rmult_lt_reg_r with (bpow (fexp n)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus.
rewrite H0; ring_simplify (-fexp n + fexp n)%Z.
simpl; rewrite Rmult_1_l, Rmult_1_r.
apply H.
rewrite <- P, round_0; trivial.
apply valid_rnd_DN.
Qed.

Theorem round_UP_plus_eps_pos :
  forall x, (0 <= x)%R -> F x ->
  forall eps, (0 < eps <= ulp x)%R ->
  round beta fexp Zceil (x + eps) = (x + ulp x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x Zx Fx eps.
case Zx; intros Zx1.

intros (Heps1,[Heps2|Heps2]).
assert (Heps: (0 <= eps < ulp x)%R).
split.
now apply Rlt_le.
exact Heps2.
assert (Hd := round_DN_plus_eps_pos x Zx Fx eps Heps).
rewrite round_UP_DN_ulp.
rewrite Hd.
rewrite 2!ulp_neq_0.
unfold cexp.
now rewrite mag_plus_eps.
now apply Rgt_not_eq.
now apply Rgt_not_eq, Rplus_lt_0_compat.
intros Fs.
rewrite round_generic in Hd...
apply Rgt_not_eq with (2 := Hd).
pattern x at 2 ; rewrite <- Rplus_0_r.
now apply Rplus_lt_compat_l.
rewrite Heps2.
apply round_generic...
now apply generic_format_succ_aux1.

rewrite <- Zx1, 2!Rplus_0_l.
intros Heps.
case (proj2 Heps).
unfold round, scaled_mantissa, cexp.
unfold ulp.
rewrite Req_bool_true; trivial.
case negligible_exp_spec.
lra.
intros n Hn H.
assert (fexp (mag beta eps) = fexp n).
apply valid_exp; try assumption.
cut (mag beta eps-1 < fexp n)%Z.
lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (2:=H).
destruct (mag beta eps) as (e,He).
simpl; rewrite Rabs_pos_eq in He.
now apply He, Rgt_not_eq.
now left.
replace (Zceil (eps * bpow (- fexp (mag beta eps)))) with 1%Z.
unfold F2R; simpl; rewrite H0; ring.
apply sym_eq, Zceil_imp.
split.
simpl; apply Rmult_lt_0_compat.
apply Heps.
apply bpow_gt_0.
apply Rmult_le_reg_r with (bpow (fexp n)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus.
rewrite H0; ring_simplify (-fexp n + fexp n)%Z.
simpl; rewrite Rmult_1_l, Rmult_1_r.
now left.
intros P; rewrite P.
apply round_generic...
apply generic_format_ulp_0.
Qed.

Theorem round_UP_pred_plus_eps_pos :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 < eps <= ulp (pred x) )%R ->
  round beta fexp Zceil (pred x + eps) = x.
Proof using valid_exp.
intros x Hx Fx eps Heps.
rewrite round_UP_plus_eps_pos; trivial.
rewrite pred_eq_pos.
apply pred_pos_plus_ulp; trivial.
now left.
now apply pred_ge_0.
apply generic_format_pred; trivial.
Qed.

Theorem round_DN_minus_eps_pos :
  forall x,  (0 < x)%R -> F x ->
  forall eps, (0 < eps <= ulp (pred x))%R ->
  round beta fexp Zfloor (x - eps) = pred x.
Proof using valid_exp.
intros x Hpx Fx eps.
rewrite pred_eq_pos;[intros Heps|now left].
replace (x-eps)%R with (pred_pos x + (ulp (pred_pos x)-eps))%R.
2: pattern x at 3; rewrite <- (pred_pos_plus_ulp x); trivial.
2: ring.
rewrite round_DN_plus_eps_pos; trivial.
now apply pred_pos_ge_0.
now apply generic_format_pred_pos.
split.
apply Rle_0_minus.
now apply Heps.
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
now apply Heps.
Qed.

Theorem round_DN_plus_eps:
  forall x, F x ->
  forall eps, (0 <= eps < if (Rle_bool 0 x) then (ulp x)
                                     else (ulp (pred (-x))))%R ->
  round beta fexp Zfloor (x + eps) = x.
Proof using valid_exp.
intros x Fx eps Heps.
case (Rle_or_lt 0 x); intros Zx.
apply round_DN_plus_eps_pos; try assumption.
split; try apply Heps.
rewrite Rle_bool_true in Heps; trivial.
now apply Heps.

rewrite Rle_bool_false in Heps; trivial.
rewrite <- (Ropp_involutive (x+eps)).
pattern x at 2; rewrite <- (Ropp_involutive x).
rewrite round_DN_opp.
apply f_equal.
replace (-(x+eps))%R with (pred (-x) + (ulp (pred (-x)) - eps))%R.
rewrite round_UP_pred_plus_eps_pos; try reflexivity.
now apply Ropp_0_gt_lt_contravar.
now apply generic_format_opp.
split.
apply Rplus_lt_reg_l with eps; ring_simplify.
apply Heps.
apply Rplus_le_reg_l with (eps-ulp (pred (- x)))%R; ring_simplify.
apply Heps.
unfold pred.
rewrite Ropp_involutive.
unfold succ; rewrite Rle_bool_false; try assumption.
rewrite Ropp_involutive; unfold Rminus.
rewrite <- Rplus_assoc, pred_pos_plus_ulp.
ring.
now apply Ropp_0_gt_lt_contravar.
now apply generic_format_opp.
Qed.

Theorem round_UP_plus_eps :
  forall x, F x ->
  forall eps, (0 < eps <= if (Rle_bool 0 x) then (ulp x)
                                     else (ulp (pred (-x))))%R ->
  round beta fexp Zceil (x + eps) = (succ x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x Fx eps Heps.
case (Rle_or_lt 0 x); intros Zx.
rewrite succ_eq_pos; try assumption.
rewrite Rle_bool_true in Heps; trivial.
apply round_UP_plus_eps_pos; assumption.

rewrite Rle_bool_false in Heps; trivial.
rewrite <- (Ropp_involutive (x+eps)).
rewrite <- (Ropp_involutive (succ x)).
rewrite round_UP_opp.
apply f_equal.
replace (-(x+eps))%R with (-succ x + (-eps + ulp (pred (-x))))%R.
apply round_DN_plus_eps_pos.
rewrite <- pred_opp.
apply pred_ge_0.
now apply Ropp_0_gt_lt_contravar.
now apply generic_format_opp.
now apply generic_format_opp, generic_format_succ.
split.
apply Rplus_le_reg_l with eps; ring_simplify.
apply Heps.
unfold pred; rewrite Ropp_involutive.
apply Rplus_lt_reg_l with (eps-ulp (- succ x))%R; ring_simplify.
apply Heps.
unfold succ; rewrite Rle_bool_false; try assumption.
apply trans_eq with (-x +-eps)%R;[idtac|ring].
pattern (-x)%R at 3; rewrite <- (pred_pos_plus_ulp (-x)).
rewrite pred_eq_pos.
ring.
left; now apply Ropp_0_gt_lt_contravar.
now apply Ropp_0_gt_lt_contravar.
now apply generic_format_opp.
Qed.

Lemma le_pred_pos_lt :
  forall x y,
  F x -> F y ->
  (0 <= x < y)%R ->
  (x <= pred_pos y)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x y Fx Fy H.
case (proj1 H); intros V.
assert (Zy:(0 < y)%R).
apply Rle_lt_trans with (1:=proj1 H).
apply H.

assert (Zp: (0 < pred y)%R).
assert (Zp:(0 <= pred y)%R).
apply pred_ge_0 ; trivial.
destruct Zp; trivial.
generalize H0.
rewrite pred_eq_pos;[idtac|now left].
unfold pred_pos.
destruct (mag beta y) as (ey,Hey); simpl.
case Req_bool_spec; intros Hy2.

intros Hy3.
assert (ey-1 = fexp (ey -1))%Z.
apply bpow_inj with beta.
rewrite <- Hy2, <- Rplus_0_l, Hy3.
ring.
assert (Zx: (x <> 0)%R).
now apply Rgt_not_eq.
destruct (mag beta x) as (ex,Hex).
specialize (Hex Zx).
assert (ex <= ey)%Z.
apply bpow_lt_bpow with beta.
apply Rle_lt_trans with (1:=proj1 Hex).
apply Rlt_trans with (Rabs y).
rewrite 2!Rabs_right.
apply H.
now apply Rgt_ge.
now apply Rgt_ge.
apply Hey.
now apply Rgt_not_eq.
case (Zle_lt_or_eq _ _ H2); intros Hexy.
assert (fexp ex = fexp (ey-1))%Z.
apply valid_exp.
lia.
rewrite <- H1.
lia.
absurd (0 < Ztrunc (scaled_mantissa beta fexp x) < 1)%Z.
lia.
split.
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
apply lt_IZR.
apply Rmult_lt_reg_r with (bpow (cexp beta fexp x)).
apply bpow_gt_0.
replace (IZR (Ztrunc (scaled_mantissa beta fexp x)) *
  bpow (cexp beta fexp x))%R with x.
rewrite Rmult_1_l.
unfold cexp.
rewrite mag_unique with beta x ex.
rewrite H3,<-H1, <- Hy2.
apply H.
exact Hex.
absurd (y <= x)%R.
now apply Rlt_not_le.
rewrite Rabs_right in Hex.
apply Rle_trans with (2:=proj1 Hex).
rewrite Hexy, Hy2.
now apply Rle_refl.
now apply Rgt_ge.

intros Hy3.
assert (y = bpow (fexp ey))%R.
apply Rminus_diag_uniq.
rewrite Hy3.
rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
unfold cexp.
rewrite (mag_unique beta y ey); trivial.
apply Hey.
now apply Rgt_not_eq.
contradict Hy2.
rewrite H1.
apply f_equal.
apply Zplus_reg_l with 1%Z.
ring_simplify.
apply trans_eq with (mag beta y).
apply sym_eq; apply mag_unique.
rewrite H1, Rabs_right.
split.
apply bpow_le.
lia.
apply bpow_lt.
lia.
apply Rle_ge; apply bpow_ge_0.
apply mag_unique.
apply Hey.
now apply Rgt_not_eq.

case (Rle_or_lt (ulp (pred_pos y)) (y-x)); intros H1.

apply Rplus_le_reg_r with (-x + ulp (pred_pos y))%R.
ring_simplify (x+(-x+ulp (pred_pos y)))%R.
apply Rle_trans with (1:=H1).
rewrite <- (pred_pos_plus_ulp y) at 1; trivial.
apply Req_le; ring.

replace x with (y-(y-x))%R by ring.
rewrite <- pred_eq_pos;[idtac|now left].
rewrite <- round_DN_minus_eps_pos with (eps:=(y-x)%R); try easy.
ring_simplify (y-(y-x))%R.
apply Req_le.
apply sym_eq.
apply round_generic...
split; trivial.
now apply Rlt_Rminus.
rewrite pred_eq_pos;[idtac|now left].
now apply Rlt_le.
rewrite <- V; apply pred_pos_ge_0; trivial.
apply Rle_lt_trans with (1:=proj1 H); apply H.
Qed.

Lemma succ_le_lt_aux:
  forall x y,
  F x -> F y ->
  (0 <= x)%R -> (x < y)%R ->
  (succ x <= y)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x y Hx Hy Zx H.
rewrite succ_eq_pos; trivial.
case (Rle_or_lt (ulp x) (y-x)); intros H1.
apply Rplus_le_reg_r with (-x)%R.
now ring_simplify (x+ulp x + -x)%R.
replace y with (x+(y-x))%R by ring.
absurd (x < y)%R.
2: apply H.
apply Rle_not_lt; apply Req_le.
rewrite <- round_DN_plus_eps_pos with (eps:=(y-x)%R); try easy.
ring_simplify (x+(y-x))%R.
apply sym_eq.
apply round_generic...
split; trivial.
apply Rlt_le; now apply Rlt_Rminus.
Qed.

Theorem succ_le_lt:
  forall x y,
  F x -> F y ->
  (x < y)%R ->
  (succ x <= y)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x y Fx Fy H.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
now apply succ_le_lt_aux.
unfold succ; rewrite Rle_bool_false; try assumption.
case (Rle_or_lt y 0); intros Hy.
rewrite <- (Ropp_involutive y).
apply Ropp_le_contravar.
apply le_pred_pos_lt.
now apply generic_format_opp.
now apply generic_format_opp.
split.
rewrite <- Ropp_0; now apply Ropp_le_contravar.
now apply Ropp_lt_contravar.
apply Rle_trans with (-0)%R.
apply Ropp_le_contravar.
apply pred_pos_ge_0.
rewrite <- Ropp_0; now apply Ropp_lt_contravar.
now apply generic_format_opp.
rewrite Ropp_0; now left.
Qed.

Theorem pred_ge_gt :
  forall x y,
  F x -> F y ->
  (x < y)%R ->
  (x <= pred y)%R.
Proof using valid_exp.
intros x y Fx Fy Hxy.
rewrite <- (Ropp_involutive x).
unfold pred; apply Ropp_le_contravar.
apply succ_le_lt.
now apply generic_format_opp.
now apply generic_format_opp.
now apply Ropp_lt_contravar.
Qed.

Theorem succ_gt_ge :
  forall x y,
  (y <> 0)%R ->
  (x <= y)%R ->
  (x < succ y)%R.
Proof using .
intros x y Zy Hxy.
apply Rle_lt_trans with (1 := Hxy).
now apply succ_gt_id.
Qed.

Theorem pred_lt_le :
  forall x y,
  (x <> 0)%R ->
  (x <= y)%R ->
  (pred x < y)%R.
Proof using .
intros x y Zy Hxy.
apply Rlt_le_trans with (2 := Hxy).
now apply pred_lt_id.
Qed.

Lemma succ_pred_pos :
  forall x, F x -> (0 < x)%R -> succ (pred x) = x.
Proof using valid_exp.
intros x Fx Hx.
rewrite pred_eq_pos by now left.
rewrite succ_eq_pos by now apply pred_pos_ge_0.
now apply pred_pos_plus_ulp.
Qed.

Theorem pred_ulp_0 :
  pred (ulp 0) = 0%R.
Proof using valid_exp.
rewrite pred_eq_pos.
2: apply ulp_ge_0.
unfold ulp; rewrite Req_bool_true; trivial.
case negligible_exp_spec'.

intros [H1 _]; rewrite H1.
unfold pred_pos; rewrite Req_bool_false.
2: apply Rlt_not_eq, bpow_gt_0.
unfold ulp; rewrite Req_bool_true; trivial.
rewrite H1; ring.

intros (n,(H1,H2)); rewrite H1.
unfold pred_pos.
rewrite mag_bpow.
replace (fexp n + 1 - 1)%Z with (fexp n) by ring.
rewrite Req_bool_true; trivial.
apply Rminus_diag_eq, f_equal.
apply sym_eq, valid_exp; lia.
Qed.

Theorem succ_0 :
  succ 0 = ulp 0.
Proof using .
unfold succ.
rewrite Rle_bool_true.
apply Rplus_0_l.
apply Rle_refl.
Qed.

Theorem pred_0 :
  pred 0 = Ropp (ulp 0).
Proof using .
rewrite <- succ_0.
rewrite <- Ropp_0 at 1.
apply pred_opp.
Qed.

Lemma pred_succ_pos :
  forall x, F x -> (0 < x)%R ->
  pred (succ x) = x.
Proof using valid_exp.
intros x Fx Hx.
apply Rle_antisym.
-
 apply Rnot_lt_le.
  intros H.
  apply succ_le_lt with (1 := Fx) in H.
  revert H.
  apply Rlt_not_le.
  apply pred_lt_id.
  apply Rgt_not_eq.
  apply Rlt_le_trans with (1 := Hx).
  apply succ_ge_id.
  now apply generic_format_pred, generic_format_succ.
-
 apply pred_ge_gt with (1 := Fx).
  now apply generic_format_succ.
  apply succ_gt_id.
  now apply Rgt_not_eq.
Qed.

Theorem succ_pred :
  forall x, F x ->
  succ (pred x) = x.
Proof using valid_exp.
intros x Fx.
destruct (Rle_or_lt 0 x) as [[Hx|Hx]|Hx].
now apply succ_pred_pos.
rewrite <- Hx.
rewrite pred_0, succ_opp, pred_ulp_0.
apply Ropp_0.
unfold pred.
rewrite succ_opp, pred_succ_pos.
apply Ropp_involutive.
now apply generic_format_opp.
now apply Ropp_0_gt_lt_contravar.
Qed.

Theorem pred_succ :
  forall x, F x ->
  pred (succ x) = x.
Proof using valid_exp.
intros x Fx.
rewrite <- (Ropp_involutive x).
rewrite succ_opp, pred_opp.
apply f_equal, succ_pred.
now apply generic_format_opp.
Qed.

Theorem round_UP_pred_plus_eps :
  forall x, F x ->
  forall eps, (0 < eps <= if Rle_bool x 0 then ulp x
                          else ulp (pred x))%R ->
  round beta fexp Zceil (pred x + eps) = x.
Proof using valid_exp.
intros x Fx eps Heps.
rewrite round_UP_plus_eps.
now apply succ_pred.
now apply generic_format_pred.
unfold pred at 4.
rewrite Ropp_involutive, pred_succ.
rewrite ulp_opp.
generalize Heps; case (Rle_bool_spec x 0); intros H1 H2.
rewrite Rle_bool_false; trivial.
case H1; intros H1'.
apply Rlt_le_trans with (2:=H1).
apply pred_lt_id.
now apply Rlt_not_eq.
rewrite H1'; unfold pred, succ.
rewrite Ropp_0; rewrite Rle_bool_true;[idtac|now right].
rewrite Rplus_0_l.
rewrite <- Ropp_0; apply Ropp_lt_contravar.
apply Rlt_le_trans with (1:=proj1 H2).
apply Rle_trans with (1:=proj2 H2).
rewrite Ropp_0, H1'.
now right.
rewrite Rle_bool_true; trivial.
now apply pred_ge_0.
now apply generic_format_opp.
Qed.

Theorem round_DN_minus_eps:
  forall x,  F x ->
  forall eps, (0 < eps <= if (Rle_bool x 0) then (ulp x)
                                     else (ulp (pred x)))%R ->
  round beta fexp Zfloor (x - eps) = pred x.
Proof using valid_exp.
intros x Fx eps Heps.
replace (x-eps)%R with (-(-x+eps))%R by ring.
rewrite round_DN_opp.
unfold pred; apply f_equal.
pattern (-x)%R at 1; rewrite <- (pred_succ (-x)).
apply round_UP_pred_plus_eps.
now apply generic_format_succ, generic_format_opp.
rewrite pred_succ.
rewrite ulp_opp.
generalize Heps; case (Rle_bool_spec x 0); intros H1 H2.
rewrite Rle_bool_false; trivial.
case H1; intros H1'.
apply Rlt_le_trans with (-x)%R.
now apply Ropp_0_gt_lt_contravar.
apply succ_ge_id.
rewrite H1', Ropp_0, succ_eq_pos;[idtac|now right].
rewrite Rplus_0_l.
apply Rlt_le_trans with (1:=proj1 H2).
rewrite H1' in H2; apply H2.
rewrite Rle_bool_true.
now rewrite succ_opp, ulp_opp.
rewrite succ_opp.
rewrite <- Ropp_0; apply Ropp_le_contravar.
now apply pred_ge_0.
now apply generic_format_opp.
now apply generic_format_opp.
Qed.

Theorem error_lt_ulp :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < ulp x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros rnd Zrnd x Zx.
destruct (generic_format_EM beta fexp x) as [Hx|Hx].

rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
rewrite ulp_neq_0; trivial.
apply bpow_gt_0.

destruct (round_DN_or_UP beta fexp rnd x) as [H|H] ; rewrite H ; clear H.

rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rplus_lt_reg_l with (round beta fexp Zfloor x).
rewrite <- round_UP_DN_ulp with (1 := Hx).
ring_simplify.
assert (Hu: (x <= round beta fexp Zceil x)%R).
apply round_UP_pt...
destruct Hu as [Hu|Hu].
exact Hu.
elim Hx.
rewrite Hu.
apply generic_format_round...
apply Rle_minus.
apply round_DN_pt...

rewrite Rabs_pos_eq.
rewrite round_UP_DN_ulp with (1 := Hx).
apply Rplus_lt_reg_r with (x - ulp x)%R.
ring_simplify.
assert (Hd: (round beta fexp Zfloor x <= x)%R).
apply round_DN_pt...
destruct Hd as [Hd|Hd].
exact Hd.
elim Hx.
rewrite <- Hd.
apply generic_format_round...
apply Rle_0_minus.
apply round_UP_pt...
Qed.

Theorem error_le_ulp :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (Rabs (round beta fexp rnd x - x) <= ulp x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros  rnd Zrnd x.
case (Req_dec x 0).
intros Zx; rewrite Zx, round_0...
unfold Rminus; rewrite Rplus_0_l, Ropp_0, Rabs_R0.
apply ulp_ge_0.
intros Zx; left.
now apply error_lt_ulp.
Qed.

Theorem error_le_half_ulp :
  forall choice x,
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * ulp x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice x.
destruct (generic_format_EM beta fexp x) as [Hx|Hx].

rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply ulp_ge_0.

set (d := round beta fexp Zfloor x).
destruct (round_N_pt beta fexp choice x) as (Hr1, Hr2).
destruct (Rle_or_lt (x - d) (d + ulp x - x)) as [H|H].

apply Rle_trans with (Rabs (d - x)).
apply Hr2.
apply (round_DN_pt beta fexp x).
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rmult_le_reg_r with 2%R.
now apply IZR_lt.
apply Rplus_le_reg_r with (d - x)%R.
ring_simplify.
apply Rle_trans with (1 := H).
right.
field.
apply Rle_minus.
apply (round_DN_pt beta fexp x).

assert (Hu: (d + ulp x)%R = round beta fexp Zceil x).
unfold d.
now rewrite <- round_UP_DN_ulp.
apply Rle_trans with (Rabs (d + ulp x - x)).
apply Hr2.
rewrite Hu.
apply (round_UP_pt beta fexp x).
rewrite Rabs_pos_eq.
apply Rmult_le_reg_r with 2%R.
now apply IZR_lt.
apply Rplus_le_reg_r with (- (d + ulp x - x))%R.
ring_simplify.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
right.
field.
apply Rle_0_minus.
rewrite Hu.
apply (round_UP_pt beta fexp x).
Qed.

Theorem ulp_DN :
  forall x, (0 <= x)%R ->
  ulp (round beta fexp Zfloor x) = ulp x.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x [Hx|Hx].
-
 rewrite (ulp_neq_0 x) by now apply Rgt_not_eq.
  destruct (round_ge_generic beta fexp Zfloor 0 x) as [Hd|Hd].
    apply generic_format_0.
    now apply Rlt_le.
  +
 rewrite ulp_neq_0 by now apply Rgt_not_eq.
    now rewrite cexp_DN with (2 := Hd).
  +
 rewrite <- Hd.
    unfold cexp.
    destruct (mag beta x) as [e He].
    simpl.
    specialize (He (Rgt_not_eq _ _ Hx)).
    apply sym_eq in Hd.
    assert (H := exp_small_round_0 _ _ _ _ _ He Hd).
    unfold ulp.
    rewrite Req_bool_true by easy.
    destruct negligible_exp_spec as [H0|k Hk].
    now elim Zlt_not_le with (1 := H0 e).
    now apply f_equal, fexp_negligible_exp_eq.
-
 rewrite <- Hx, round_0...
Qed.

Theorem round_neq_0_negligible_exp :
  negligible_exp = None -> forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R -> (round beta fexp rnd x <> 0)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros H rndn Hrnd x Hx K.
case negligible_exp_spec'.
intros (_,Hn).
destruct (mag beta x) as (e,He).
absurd (fexp e < e)%Z.
apply Zle_not_lt.
apply exp_small_round_0 with beta rndn x...
apply (Hn e).
intros (n,(H1,_)).
rewrite H in H1; discriminate.
Qed.

Theorem error_lt_ulp_round :
  forall { Hm : Monotone_exp fexp } rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < ulp (round beta fexp rnd x))%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros Hm.

cut (forall rnd : R -> Z, Valid_rnd rnd -> forall x : R, (0 < x)%R  ->
    (Rabs (round beta fexp rnd x - x) < ulp (round beta fexp rnd x))%R).
intros M rnd Hrnd x Zx.
case (Rle_or_lt 0 x).
intros H; destruct H.
now apply M.
contradict H; now apply sym_not_eq.
intros H.
rewrite <- (Ropp_involutive x).
rewrite round_opp, ulp_opp.
replace (- round beta fexp (Zrnd_opp rnd) (- x) - - - x)%R with
    (-(round beta fexp (Zrnd_opp rnd) (- x) - (-x)))%R by ring.
rewrite Rabs_Ropp.
apply M.
now apply valid_rnd_opp.
now apply Ropp_0_gt_lt_contravar.

intros rnd Hrnd x Hx.
apply Rlt_le_trans with (ulp x).
apply error_lt_ulp...
now apply Rgt_not_eq.
rewrite <- ulp_DN; trivial.
apply ulp_le_pos.
apply round_ge_generic...
apply generic_format_0.
now apply Rlt_le.
case (round_DN_or_UP beta fexp rnd x); intros V; rewrite V.
apply Rle_refl.
apply Rle_trans with x.
apply round_DN_pt...
apply round_UP_pt...
now apply Rlt_le.
Qed.

Lemma error_le_ulp_round :
  forall { Hm : Monotone_exp fexp } rnd { Zrnd : Valid_rnd rnd } x,
  (Rabs (round beta fexp rnd x - x) <= ulp (round beta fexp rnd x))%R.
Proof using valid_exp.
intros Mexp rnd Vrnd x.
destruct (Req_dec x 0) as [Zx|Nzx].
{
 rewrite Zx, round_0; [|exact Vrnd].
  unfold Rminus; rewrite Ropp_0, Rplus_0_l, Rabs_R0; apply ulp_ge_0.
}
now apply Rlt_le, error_lt_ulp_round.
Qed.

Theorem error_le_half_ulp_round :
  forall { Hm : Monotone_exp fexp },
  forall choice x,
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * ulp (round beta fexp (Znearest choice) x))%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros Hm choice x.
case (Req_dec (round beta fexp (Znearest choice) x) 0); intros Hfx.

case (Req_dec x 0); intros Hx.
apply Rle_trans with (1:=error_le_half_ulp _ _).
rewrite Hx, round_0...
right; ring.
generalize (error_le_half_ulp choice x).
rewrite Hfx.
unfold Rminus; rewrite Rplus_0_l, Rabs_Ropp.
intros N.
unfold ulp; rewrite Req_bool_true; trivial.
case negligible_exp_spec'.
intros (H1,H2).
contradict Hfx.
apply round_neq_0_negligible_exp...
intros (n,(H1,Hn)); rewrite H1.
apply Rle_trans with (1:=N).
right; apply f_equal.
rewrite ulp_neq_0; trivial.
apply f_equal.
unfold cexp.
apply valid_exp; trivial.
cut (mag beta x -1 < fexp n)%Z.
lia.
apply lt_bpow with beta.
destruct (mag beta x) as (e,He).
simpl.
apply Rle_lt_trans with (Rabs x).
now apply He.
apply Rle_lt_trans with (Rabs (round beta fexp (Znearest choice) x - x)).
right; rewrite Hfx; unfold Rminus; rewrite Rplus_0_l.
apply sym_eq, Rabs_Ropp.
apply Rlt_le_trans with (ulp 0).
rewrite <- Hfx.
apply error_lt_ulp_round...
unfold ulp; rewrite Req_bool_true, H1; trivial.
now right.

case (round_DN_or_UP beta fexp (Znearest choice) x); intros Hx.

destruct (Rle_or_lt 0 x) as [H|H].
rewrite Hx at 2.
rewrite ulp_DN by easy.
apply error_le_half_ulp.
apply Rle_trans with (1:=error_le_half_ulp _ _).
apply Rmult_le_compat_l.
apply Rlt_le, pos_half_prf.
apply ulp_le.
rewrite Rabs_left1 by now apply Rlt_le.
rewrite Hx.
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply round_DN_pt...
apply round_le_generic...
apply generic_format_0.
now apply Rlt_le.

destruct (Rle_or_lt 0 x) as [H|H].
apply Rle_trans with (1:=error_le_half_ulp _ _).
apply Rmult_le_compat_l.
apply Rlt_le, pos_half_prf.
apply ulp_le_pos; trivial.
rewrite Hx; apply (round_UP_pt beta fexp x).
rewrite Hx at 2; rewrite <- (ulp_opp (round beta fexp Zceil x)).
rewrite <- round_DN_opp.
rewrite ulp_DN; trivial.
pattern x at 1 2; rewrite <- Ropp_involutive.
rewrite round_N_opp.
unfold Rminus.
rewrite <- Ropp_plus_distr, Rabs_Ropp.
apply error_le_half_ulp.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
Qed.

Theorem pred_le :
  forall x y, F x -> F y -> (x <= y)%R ->
  (pred x <= pred y)%R.
Proof using valid_exp.
intros x y Fx Fy [Hxy| ->].
2: apply Rle_refl.
apply pred_ge_gt with (2 := Fy).
now apply generic_format_pred.
apply Rle_lt_trans with (2 := Hxy).
apply pred_le_id.
Qed.

Theorem succ_le :
  forall x y, F x -> F y -> (x <= y)%R ->
  (succ x <= succ y)%R.
Proof using valid_exp.
intros x y Fx Fy Hxy.
apply Ropp_le_cancel.
rewrite <- 2!pred_opp.
apply pred_le.
now apply generic_format_opp.
now apply generic_format_opp.
now apply Ropp_le_contravar.
Qed.

Theorem pred_le_inv: forall x y, F x -> F y
   -> (pred x <= pred y)%R -> (x <= y)%R.
Proof using valid_exp.
intros x y Fx Fy Hxy.
rewrite <- (succ_pred x), <- (succ_pred y); try assumption.
apply succ_le; trivial; now apply generic_format_pred.
Qed.

Theorem succ_le_inv: forall x y, F x -> F y
   -> (succ x <= succ y)%R -> (x <= y)%R.
Proof using valid_exp.
intros x y Fx Fy Hxy.
rewrite <- (pred_succ x), <- (pred_succ y); try assumption.
apply pred_le; trivial; now apply generic_format_succ.
Qed.

Theorem pred_lt :
  forall x y, F x -> F y -> (x < y)%R ->
  (pred x < pred y)%R.
Proof using valid_exp.
intros x y Fx Fy Hxy.
apply Rnot_le_lt.
intros H.
apply Rgt_not_le with (1 := Hxy).
now apply pred_le_inv.
Qed.

Theorem succ_lt :
  forall x y, F x -> F y -> (x < y)%R ->
  (succ x < succ y)%R.
Proof using valid_exp.
intros x y Fx Fy Hxy.
apply Rnot_le_lt.
intros H.
apply Rgt_not_le with (1 := Hxy).
now apply succ_le_inv.
Qed.

Lemma succ_le_plus_ulp :
  forall { Hm : Monotone_exp fexp } x,
  (succ x <= x + ulp x)%R.
Proof using .
intros Mexp x.
destruct (Rle_or_lt 0 x) as [Px|Nx]; [now right; apply succ_eq_pos|].
replace (_ + _)%R with (- (-x - ulp x))%R by ring.
unfold succ; rewrite (Rle_bool_false _ _ Nx), <-ulp_opp.
apply Ropp_le_contravar; unfold pred_pos.
destruct (Req_dec (-x) (bpow (mag beta (-x) - 1))) as [Hx|Hx].
{
 rewrite (Req_bool_true _ _ Hx).
   apply (Rplus_le_reg_r x); ring_simplify; apply Ropp_le_contravar.
   unfold ulp; rewrite Req_bool_false; [|lra].
   apply bpow_le, Mexp; lia.
}
 now rewrite (Req_bool_false _ _ Hx); right.
Qed.

Lemma generic_format_plus_ulp :
  forall { Hm : Monotone_exp fexp } x,
  generic_format beta fexp x ->
  generic_format beta fexp (x + ulp x).
Proof using valid_exp.
intros Mexp x Fx.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{
 now rewrite <-(succ_eq_pos _ Px); apply generic_format_succ.
}
apply generic_format_opp in Fx.
replace (_ + _)%R with (- (-x - ulp x))%R by ring.
apply generic_format_opp; rewrite <-ulp_opp.
destruct (Req_dec (-x) (bpow (mag beta (-x) - 1))) as [Hx|Hx].
{
 unfold ulp; rewrite Req_bool_false; [|lra].
  rewrite Hx at 1.
  unfold cexp.
  set (e := mag _ _).
  assert (Hfe : (fexp e < e)%Z).
  {
 now apply mag_generic_gt; [|lra|].
}
  replace (e - 1)%Z with (e - 1 - fexp e + fexp e)%Z by ring.
  rewrite bpow_plus.
  set (m := bpow (_ - _)).
  replace (_ - _)%R with ((m - 1) * bpow (fexp e))%R; [|unfold m; ring].
  case_eq (e - 1 - fexp e)%Z.
  {
 intro He; unfold m; rewrite He; simpl; ring_simplify (1 - 1)%R.
    rewrite Rmult_0_l; apply generic_format_0.
}
  {
 intros p Hp; unfold m; rewrite Hp; simpl.
    pose (f := {| Defs.Fnum := (Z.pow_pos beta p - 1)%Z;
                  Defs.Fexp := fexp e |} : Defs.float beta).
    apply (generic_format_F2R' _ _ _ f); [|intro Hm'; unfold f; simpl].
    {
 now unfold Defs.F2R; simpl; rewrite minus_IZR.
}
    unfold cexp.
    replace (IZR _) with (bpow (Z.pos p)); [|now simpl].
    rewrite <-Hp.
    assert (He : (1 <= e - 1 - fexp e)%Z); [lia|].
    set (e' := mag _ (_ * _)).
    assert (H : (e' = e - 1 :> Z)%Z); [|rewrite H; apply Mexp; lia].
    unfold e'; apply mag_unique.
    rewrite Rabs_mult, (Rabs_pos_eq (bpow _)); [|apply bpow_ge_0].
    rewrite Rabs_pos_eq;
      [|apply (Rplus_le_reg_r 1); ring_simplify;
        change 1%R with (bpow 0); apply bpow_le; lia].
    assert (beta_pos : (0 < IZR beta)%R).
    {
 apply (Rlt_le_trans _ 2); [lra|].
      apply IZR_le, Z.leb_le, radix_prop.
}
    split.
    {
 replace (e - 1 - 1)%Z with (e - 1 - fexp e + -1  + fexp e)%Z by ring.
      rewrite bpow_plus.
      apply Rmult_le_compat_r; [apply bpow_ge_0|].
      rewrite bpow_plus; simpl; unfold Z.pow_pos; simpl.
      rewrite Zmult_1_r.
      apply (Rmult_le_reg_r _ _ _ beta_pos).
      rewrite Rmult_assoc, Rinv_l; [|lra]; rewrite Rmult_1_r.
      apply (Rplus_le_reg_r (IZR beta)); ring_simplify.
      apply (Rle_trans _ (2 * bpow (e - 1 - fexp e))).
      {
 change 2%R with (1 + 1)%R; rewrite Rmult_plus_distr_r, Rmult_1_l.
        apply Rplus_le_compat_l.
        rewrite <-bpow_1; apply bpow_le; lia.
}
      rewrite Rmult_comm; apply Rmult_le_compat_l; [apply bpow_ge_0|].
      apply IZR_le, Z.leb_le, radix_prop.
}
    apply (Rmult_lt_reg_r (bpow (- fexp e))); [apply bpow_gt_0|].
    rewrite Rmult_assoc, <-!bpow_plus.
    replace (fexp e + - fexp e)%Z with 0%Z by ring; simpl.
    rewrite Rmult_1_r; unfold Zminus; lra.
}
  intros p Hp; exfalso; lia.
}
replace (_ - _)%R with (pred_pos (-x)).
{
 now apply generic_format_pred_pos; [|lra].
}
now unfold pred_pos; rewrite Req_bool_false.
Qed.

Theorem round_DN_ge_UP_gt :
  forall x y, F y ->
  (y < round beta fexp Zceil x -> y <= round beta fexp Zfloor x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x y Fy Hlt.
apply round_DN_pt...
apply Rnot_lt_le.
contradict Hlt.
apply RIneq.Rle_not_lt.
apply round_UP_pt...
now apply Rlt_le.
Qed.

Theorem round_UP_le_DN_lt :
  forall x y, F y ->
  (round beta fexp Zfloor x < y -> round beta fexp Zceil x <= y)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x y Fy Hlt.
apply round_UP_pt...
apply Rnot_lt_le.
contradict Hlt.
apply RIneq.Rle_not_lt.
apply round_DN_pt...
now apply Rlt_le.
Qed.

Theorem pred_UP_le_DN :
  forall x, (pred (round beta fexp Zceil x) <= round beta fexp Zfloor x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x.
destruct (generic_format_EM beta fexp x) as [Fx|Fx].
rewrite !round_generic...
apply pred_le_id.
case (Req_dec (round beta fexp Zceil x) 0); intros Zx.
rewrite Zx; unfold pred; rewrite Ropp_0.
unfold succ; rewrite Rle_bool_true;[idtac|now right].
rewrite Rplus_0_l; unfold ulp; rewrite Req_bool_true; trivial.
case negligible_exp_spec'.
intros (H1,H2).
contradict Zx; apply round_neq_0_negligible_exp...
intros L; apply Fx; rewrite L; apply generic_format_0.
intros (n,(H1,Hn)); rewrite H1.
case (Rle_or_lt (- bpow (fexp n)) (round beta fexp Zfloor x)); trivial; intros K.
absurd (round beta fexp Zceil x <= - bpow (fexp n))%R.
apply Rlt_not_le.
rewrite Zx, <- Ropp_0.
apply Ropp_lt_contravar, bpow_gt_0.
apply round_UP_le_DN_lt; try assumption.
apply generic_format_opp, generic_format_bpow.
now apply valid_exp.
assert (let u := round beta fexp Zceil x in pred u < u)%R as Hup.
now apply pred_lt_id.
apply round_DN_ge_UP_gt...
apply generic_format_pred...
now apply round_UP_pt.
Qed.

Theorem UP_le_succ_DN :
  forall x, (round beta fexp Zceil x <= succ (round beta fexp Zfloor x))%R.
Proof using valid_exp.
intros x.
rewrite <- (Ropp_involutive x).
rewrite round_DN_opp, round_UP_opp, succ_opp.
apply Ropp_le_contravar.
apply pred_UP_le_DN.
Qed.

Theorem pred_UP_eq_DN :
  forall x,  ~ F x ->
  (pred (round beta fexp Zceil x) = round beta fexp Zfloor x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x Fx.
apply Rle_antisym.
now apply pred_UP_le_DN.
apply pred_ge_gt; try apply generic_format_round...
pose proof round_DN_UP_lt _ _ _ Fx as HE.
now apply Rlt_trans with (1 := proj1 HE) (2 := proj2 HE).
Qed.

Theorem succ_DN_eq_UP :
  forall x,  ~ F x ->
  (succ (round beta fexp Zfloor x) = round beta fexp Zceil x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x Fx.
rewrite <- pred_UP_eq_DN; trivial.
rewrite succ_pred; trivial.
apply generic_format_round...
Qed.

Theorem round_DN_eq :
  forall x d, F d -> (d <= x < succ d)%R ->
  round beta fexp Zfloor x = d.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x d Fd (Hxd1,Hxd2).
generalize (round_DN_pt beta fexp x); intros (T1,(T2,T3)).
apply sym_eq, Rle_antisym.
now apply T3.
destruct (generic_format_EM beta fexp x) as [Fx|NFx].
rewrite round_generic...
apply succ_le_inv; try assumption.
apply succ_le_lt; try assumption.
apply generic_format_succ...
apply succ_le_inv; try assumption.
rewrite succ_DN_eq_UP; trivial.
apply round_UP_pt...
apply generic_format_succ...
now left.
Qed.

Theorem round_UP_eq :
  forall x u, F u -> (pred u < x <= u)%R ->
  round beta fexp Zceil x = u.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x u Fu Hux.
rewrite <- (Ropp_involutive (round beta fexp Zceil x)).
rewrite <- round_DN_opp.
rewrite <- (Ropp_involutive u).
apply f_equal.
apply round_DN_eq; try assumption.
now apply generic_format_opp.
split;[now apply Ropp_le_contravar|idtac].
rewrite succ_opp.
now apply Ropp_lt_contravar.
Qed.

Lemma ulp_ulp_0 : forall {H : Exp_not_FTZ fexp},
  ulp (ulp 0) = ulp 0.
Proof using valid_exp.
intros H; case (negligible_exp_spec').
intros (K1,K2).
replace (ulp 0) with 0%R at 1; try easy.
apply sym_eq; unfold ulp; rewrite Req_bool_true; try easy.
now rewrite K1.
intros (n,(Hn1,Hn2)).
apply Rle_antisym.
replace (ulp 0) with (bpow (fexp n)).
rewrite ulp_bpow.
apply bpow_le.
now apply valid_exp.
unfold ulp; rewrite Req_bool_true; try easy.
rewrite Hn1; easy.
now apply ulp_ge_ulp_0.
Qed.

Lemma ulp_succ_pos :
  forall x, F x -> (0 < x)%R ->
  ulp (succ x) = ulp x \/ succ x = bpow (mag beta x).
Proof using .
Proof with auto with typeclass_instances.
intros x Fx Hx.
generalize (Rlt_le _ _ Hx); intros Hx'.
rewrite succ_eq_pos;[idtac|now left].
destruct (mag beta x) as (e,He); simpl.
rewrite Rabs_pos_eq in He; try easy.
specialize (He (Rgt_not_eq _ _ Hx)).
assert (H:(x+ulp x <= bpow e)%R).
apply id_p_ulp_le_bpow; try assumption.
apply He.
destruct H;[left|now right].
rewrite ulp_neq_0 at 1.
2: apply Rgt_not_eq, Rgt_lt, Rlt_le_trans with x...
2: rewrite <- (Rplus_0_r x) at 1; apply Rplus_le_compat_l.
2: apply ulp_ge_0.
rewrite ulp_neq_0 at 2.
2: now apply Rgt_not_eq.
f_equal; unfold cexp; f_equal.
apply trans_eq with e.
apply mag_unique_pos; split; try assumption.
apply Rle_trans with (1:=proj1 He).
rewrite <- (Rplus_0_r x) at 1; apply Rplus_le_compat_l.
apply ulp_ge_0.
now apply sym_eq, mag_unique_pos.
Qed.

Theorem ulp_pred_pos :
  forall x, F x -> (0 < pred x)%R ->
  ulp (pred x) = ulp x \/ x = bpow (mag beta x - 1).
Proof using valid_exp.
intros x Fx Hx.
assert (Hx': (0 < x)%R).
  apply Rlt_le_trans with (1 := Hx).
  apply pred_le_id.
assert (Zx : x <> 0%R).
  now apply Rgt_not_eq.
rewrite (ulp_neq_0 x) by easy.
unfold cexp.
destruct (mag beta x) as [e He].
simpl.
assert (bpow (e - 1) <= x < bpow e)%R.
  rewrite <- (Rabs_pos_eq x) by now apply Rlt_le.
  now apply He.
destruct (proj1 H) as [H1|H1].
2: now right.
left.
apply pred_ge_gt with (2 := Fx) in H1.
rewrite ulp_neq_0 by now apply Rgt_not_eq.
apply (f_equal (fun e => bpow (fexp e))).
apply mag_unique_pos.
apply (conj H1).
apply Rle_lt_trans with (2 := proj2 H).
apply pred_le_id.
apply generic_format_bpow.
apply Z.lt_le_pred.
replace (_ + 1)%Z with e by ring.
rewrite <- (mag_unique_pos _ _ _ H).
now apply mag_generic_gt.
Qed.

Lemma ulp_round_pos :
  forall { Not_FTZ_ : Exp_not_FTZ fexp},
   forall rnd { Zrnd : Valid_rnd rnd } x,
  (0 < x)%R -> ulp (round beta fexp rnd x) = ulp x
     \/ round beta fexp rnd x = bpow (mag beta x).
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros Not_FTZ_ rnd Zrnd x Hx.
case (generic_format_EM beta fexp x); intros Fx.
rewrite round_generic...
case (round_DN_or_UP beta fexp rnd x); intros Hr; rewrite Hr.
left.
apply ulp_DN; now left...
assert (M:(0 <= round beta fexp Zfloor x)%R).
apply round_ge_generic...
apply generic_format_0...
apply Rlt_le...
destruct M as [M|M].
rewrite <- (succ_DN_eq_UP x)...
case (ulp_succ_pos (round beta fexp Zfloor x)); try intros Y.
apply generic_format_round...
assumption.
rewrite ulp_DN in Y...
now apply Rlt_le.
right; rewrite Y.
apply f_equal, mag_DN...
left; rewrite <- (succ_DN_eq_UP x)...
rewrite <- M, succ_0.
rewrite ulp_ulp_0...
case (negligible_exp_spec').
intros (K1,K2).
absurd (x = 0)%R.
now apply Rgt_not_eq.
apply eq_0_round_0_negligible_exp with Zfloor...
intros (n,(Hn1,Hn2)).
replace (ulp 0) with (bpow (fexp n)).
2: unfold ulp; rewrite Req_bool_true; try easy.
2: now rewrite Hn1.
rewrite ulp_neq_0.
2: apply Rgt_not_eq...
unfold cexp; f_equal.
destruct (mag beta x) as (e,He); simpl.
apply sym_eq, valid_exp...
assert (e <= fexp e)%Z.
apply exp_small_round_0_pos with beta Zfloor x...
rewrite <- (Rabs_pos_eq x).
apply He, Rgt_not_eq...
apply Rlt_le...
replace (fexp n) with (fexp e); try assumption.
now apply fexp_negligible_exp_eq.
Qed.

Theorem ulp_round : forall { Not_FTZ_ : Exp_not_FTZ fexp},
   forall rnd { Zrnd : Valid_rnd rnd } x,
     ulp (round beta fexp rnd x) = ulp x
         \/ Rabs (round beta fexp rnd x) = bpow (mag beta x).
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros Not_FTZ_ rnd Zrnd x.
case (Rtotal_order x 0); intros Zx.
case (ulp_round_pos (Zrnd_opp rnd) (-x)).
now apply Ropp_0_gt_lt_contravar.
rewrite ulp_opp, <- ulp_opp.
rewrite <- round_opp, Ropp_involutive.
intros Y;now left.
rewrite mag_opp.
intros Y; right.
rewrite <- (Ropp_involutive x) at 1.
rewrite round_opp, Y.
rewrite Rabs_Ropp, Rabs_right...
apply Rle_ge, bpow_ge_0.
destruct Zx as [Zx|Zx].
left; rewrite Zx; rewrite round_0...
rewrite Rabs_right.
apply ulp_round_pos...
apply Rle_ge, round_ge_generic...
apply generic_format_0...
now apply Rlt_le.
Qed.

Lemma succ_round_ge_id :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <= succ (round beta fexp rnd x))%R.
Proof using valid_exp.
intros rnd Vrnd x.
apply (Rle_trans _ (round beta fexp Raux.Zceil x)).
{
 now apply round_UP_pt.
}
destruct (round_DN_or_UP beta fexp rnd x) as [Hr|Hr]; rewrite Hr.
{
 now apply UP_le_succ_DN.
}
apply succ_ge_id.
Qed.

Lemma pred_round_le_id :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (pred (round beta fexp rnd x) <= x)%R.
Proof using valid_exp.
intros rnd Vrnd x.
apply (Rle_trans _ (round beta fexp Raux.Zfloor x)).
2: now apply round_DN_pt.
destruct (round_DN_or_UP beta fexp rnd x) as [Hr|Hr]; rewrite Hr.
2: now apply pred_UP_le_DN.
apply pred_le_id.
Qed.

Theorem round_N_le_midp: forall choice u v,
  F u -> (v < (u + succ u)/2)%R
      -> (round beta fexp (Znearest choice)  v <= u)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice u v Fu H.

assert (V: ((succ u = 0 /\ u = 0) \/ u < succ u)%R).
specialize (succ_ge_id u); intros P; destruct P as [P|P].
now right.
case (Req_dec u 0); intros Zu.
left; split; trivial.
now rewrite <- P.
right; now apply succ_gt_id.

destruct V as [(V1,V2)|V].
rewrite V2; apply round_le_generic...
apply generic_format_0.
left; apply Rlt_le_trans with (1:=H).
rewrite V1,V2; right; field.

assert (T: (u < (u + succ u) / 2 < succ u)%R) by lra.
destruct T as (T1,T2).
apply Rnd_N_pt_monotone with F v ((u + succ u) / 2)%R...
apply round_N_pt...
apply Rnd_N_pt_DN with (succ u)%R.
pattern u at 3; replace u with (round beta fexp Zfloor ((u + succ u) / 2)).
apply round_DN_pt...
apply round_DN_eq; trivial.
split; try left; assumption.
pattern (succ u) at 2; replace (succ u) with (round beta fexp Zceil ((u + succ u) / 2)).
apply round_UP_pt...
apply round_UP_eq; trivial.
apply generic_format_succ...
rewrite pred_succ; trivial.
split; try left; assumption.
right; field.
Qed.

Theorem round_N_ge_midp: forall choice u v,
 F u ->  ((u + pred u)/2 < v)%R
      -> (u <= round beta fexp (Znearest choice)  v)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice u v Fu H.
rewrite <- (Ropp_involutive v).
rewrite round_N_opp.
rewrite <- (Ropp_involutive u).
apply Ropp_le_contravar.
apply round_N_le_midp.
now apply generic_format_opp.
apply Ropp_lt_cancel.
rewrite Ropp_involutive.
apply Rle_lt_trans with (2:=H).
unfold pred.
right; field.
Qed.

Lemma round_N_ge_ge_midp : forall choice u v,
       F u ->
       (u <= round beta fexp (Znearest choice) v)%R ->
       ((u + pred u) / 2 <= v)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice u v Hu H2.
assert (K: ((u=0)%R /\ negligible_exp = None) \/ (pred u < u)%R).
case (Req_dec u 0); intros Zu.
case_eq (negligible_exp).
intros n Hn; right.
rewrite Zu, pred_0.
unfold ulp; rewrite Req_bool_true, Hn; try easy.
rewrite <- Ropp_0.
apply Ropp_lt_contravar, bpow_gt_0.
intros _; left; split; easy.
right.
apply pred_lt_id...

case K.
intros (K1,K2).

rewrite K1, pred_0.
unfold ulp; rewrite Req_bool_true, K2; try easy.
replace ((0+-0)/2)%R with 0%R by field.
case (Rle_or_lt 0 v); try easy.
intros H3; contradict H2.
rewrite K1; apply Rlt_not_le.
assert (H4: (round beta fexp (Znearest choice) v <= 0)%R).
apply round_le_generic...
apply generic_format_0...
now left.
case H4; try easy.
intros H5.
absurd (v=0)%R; try auto with real.
apply eq_0_round_0_negligible_exp with (Znearest choice)...

intros K1.
case (Rle_or_lt ((u + pred u) / 2) v); try easy.
intros H3.
absurd (u <= round beta fexp (Znearest choice) v)%R; try easy.
apply Rlt_not_le.
apply Rle_lt_trans with (2:=K1).
apply round_N_le_midp...
apply generic_format_pred...
rewrite succ_pred...
apply Rlt_le_trans with (1:=H3).
right; f_equal; ring.
Qed.

Lemma round_N_le_le_midp : forall choice u v,
       F u ->
       (round beta fexp (Znearest choice) v <= u)%R ->
       (v <= (u + succ u) / 2)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice u v Hu H2.
apply Ropp_le_cancel.
apply Rle_trans with (((-u)+pred (-u))/2)%R.
rewrite pred_opp; right; field.
apply round_N_ge_ge_midp with
   (choice := fun t:Z => negb (choice (- (t + 1))%Z))...
apply generic_format_opp...
rewrite <- (Ropp_involutive (round _ _ _ _)).
rewrite <- round_N_opp, Ropp_involutive.
apply Ropp_le_contravar; easy.
Qed.

Lemma round_N_eq_DN: forall choice x,
       let d:=round beta fexp Zfloor x in
       let u:=round beta fexp Zceil x in
      (x<(d+u)/2)%R ->
     round beta fexp (Znearest choice) x = d.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice x d u H.
apply Rle_antisym.
destruct (generic_format_EM beta fexp x) as [Fx|Fx].
rewrite round_generic...
apply round_DN_pt; trivial; now right.
apply round_N_le_midp.
apply round_DN_pt...
apply Rlt_le_trans with (1:=H).
right; apply f_equal2; trivial; apply f_equal.
now apply sym_eq, succ_DN_eq_UP.
apply round_ge_generic; try apply round_DN_pt...
Qed.

Lemma round_N_eq_DN_pt: forall choice x d u,
      Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
      (x<(d+u)/2)%R ->
     round beta fexp (Znearest choice) x = d.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice x d u Hd Hu H.
assert (H0:(d = round beta fexp Zfloor x)%R).
apply Rnd_DN_pt_unique with (1:=Hd).
apply round_DN_pt...
rewrite H0.
apply round_N_eq_DN.
rewrite <- H0.
rewrite Rnd_UP_pt_unique with F x (round beta fexp Zceil x) u; try assumption.
apply round_UP_pt...
Qed.

Lemma round_N_eq_UP: forall choice x,
      let d:=round beta fexp Zfloor x in
      let u:=round beta fexp Zceil x in
     ((d+u)/2 < x)%R ->
     round beta fexp (Znearest choice) x = u.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice x d u H.
apply Rle_antisym.
apply round_le_generic; try apply round_UP_pt...
destruct (generic_format_EM beta fexp x) as [Fx|Fx].
rewrite round_generic...
apply round_UP_pt; trivial; now right.
apply round_N_ge_midp.
apply round_UP_pt...
apply Rle_lt_trans with (2:=H).
right; apply f_equal2; trivial; rewrite Rplus_comm; apply f_equal2; trivial.
now apply pred_UP_eq_DN.
Qed.

Lemma round_N_eq_UP_pt: forall choice x d u,
      Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
      ((d+u)/2 < x)%R ->
     round beta fexp (Znearest choice) x = u.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros choice x d u Hd Hu H.
assert (H0:(u = round beta fexp Zceil x)%R).
apply Rnd_UP_pt_unique with (1:=Hu).
apply round_UP_pt...
rewrite H0.
apply round_N_eq_UP.
rewrite <- H0.
rewrite Rnd_DN_pt_unique with F x (round beta fexp Zfloor x) d; try assumption.
apply round_DN_pt...
Qed.

Lemma round_N_plus_ulp_ge :
  forall { Hm : Monotone_exp fexp } choice1 choice2 x,
  let rx := round beta fexp (Znearest choice2) x in
  (x <= round beta fexp (Znearest choice1) (rx + ulp rx))%R.
Proof using valid_exp.
intros Hm choice1 choice2 x.
simpl.
set (rx := round _ _ _ x).
assert (Vrnd1 : Valid_rnd (Znearest choice1)) by now apply valid_rnd_N.
assert (Vrnd2 : Valid_rnd (Znearest choice2)) by now apply valid_rnd_N.
apply (Rle_trans _ (succ rx)); [now apply succ_round_ge_id|].
rewrite round_generic; [now apply succ_le_plus_ulp|now simpl|].
now apply generic_format_plus_ulp, generic_format_round.
Qed.

Lemma round_N_eq_ties: forall c1 c2 x,
   (x - round beta fexp Zfloor x <> round beta fexp Zceil x - x)%R ->
   (round beta fexp (Znearest c1) x = round beta fexp (Znearest c2) x)%R.
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros c1 c2 x.
pose (d:=round beta fexp Zfloor x); pose (u:=round beta fexp Zceil x); fold d; fold u; intros H.
case (Rle_or_lt ((d+u)/2) x); intros L.
2:rewrite 2!round_N_eq_DN...
destruct L as [L|L].
rewrite 2!round_N_eq_UP...
contradict H; rewrite <- L; field.
Qed.

End Fcore_ulp.

End Ulp.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Ulp.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_Round_NE.
Module Export Flocq.
Module Export Core.
Module Export Round_NE.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Float_prop Flocq.Core.Ulp.

Notation ZnearestE := (Znearest (fun x => negb (Z.even x))).

Section Fcore_rnd_NE.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Context { valid_exp : Valid_exp fexp }.

Notation format := (generic_format beta fexp).
Notation canonical := (canonical beta fexp).

Definition NE_prop (_ : R) f :=
  exists g : float beta, f = F2R g /\ canonical g /\ Z.even (Fnum g) = true.

Definition Rnd_NE_pt :=
  Rnd_NG_pt format NE_prop.

Definition DN_UP_parity_pos_prop :=
  forall x xd xu,
  (0 < x)%R ->
  ~ format x ->
  canonical xd ->
  canonical xu ->
  F2R xd = round beta fexp Zfloor x ->
  F2R xu = round beta fexp Zceil x ->
  Z.even (Fnum xu) = negb (Z.even (Fnum xd)).

Definition DN_UP_parity_prop :=
  forall x xd xu,
  ~ format x ->
  canonical xd ->
  canonical xu ->
  F2R xd = round beta fexp Zfloor x ->
  F2R xu = round beta fexp Zceil x ->
  Z.even (Fnum xu) = negb (Z.even (Fnum xd)).

Lemma DN_UP_parity_aux :
  DN_UP_parity_pos_prop ->
  DN_UP_parity_prop.
Proof using .
intros Hpos x xd xu Hfx Hd Hu Hxd Hxu.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].

exact (Hpos x xd xu Hx Hfx Hd Hu Hxd Hxu).
elim Hfx.
rewrite <- Hx.
apply generic_format_0.

assert (Hx': (0 < -x)%R).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive, Ropp_0.
destruct xd as (md, ed).
destruct xu as (mu, eu).
simpl.
rewrite <- (Bool.negb_involutive (Z.even mu)).
apply f_equal.
apply sym_eq.
rewrite <- (Z.even_opp mu), <- (Z.even_opp md).
change (Z.even (Fnum (Float beta (-md) ed)) = negb (Z.even (Fnum (Float beta (-mu) eu)))).
apply (Hpos (-x)%R _ _ Hx').
intros H.
apply Hfx.
rewrite <- Ropp_involutive.
now apply generic_format_opp.
now apply canonical_opp.
now apply canonical_opp.
rewrite round_DN_opp, F2R_Zopp.
now apply f_equal.
rewrite round_UP_opp, F2R_Zopp.
now apply f_equal.
Qed.

Class Exists_NE :=
  exists_NE : Z.even beta = false \/ forall e,
  ((fexp e < e)%Z -> (fexp (e + 1) < e)%Z) /\ ((e <= fexp e)%Z -> fexp (fexp e + 1) = fexp e).

Context { exists_NE_ : Exists_NE }.

Theorem DN_UP_parity_generic_pos :
  DN_UP_parity_pos_prop.
Proof using exists_NE_ valid_exp.
Proof with auto with typeclass_instances.
intros x xd xu H0x Hfx Hd Hu Hxd Hxu.
destruct (mag beta x) as (ex, Hexa).
specialize (Hexa (Rgt_not_eq _ _ H0x)).
generalize Hexa.
intros Hex.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ H0x)) in Hex.
destruct (Zle_or_lt ex (fexp ex)) as [Hxe|Hxe].

assert (Hd3 : Fnum xd = Z0).
apply eq_0_F2R with beta (Fexp xd).
change (F2R xd = R0).
rewrite Hxd.
apply round_DN_small_pos with (1 := Hex) (2 := Hxe).
assert (Hu3 : xu = Float beta (1 * Zpower beta (fexp ex - fexp (fexp ex + 1))) (fexp (fexp ex + 1))).
apply canonical_unique with (1 := Hu).
apply (f_equal fexp).
rewrite <- F2R_change_exp.
now rewrite F2R_bpow, mag_bpow.
now apply valid_exp.
rewrite <- F2R_change_exp.
rewrite F2R_bpow.
apply sym_eq.
rewrite Hxu.
apply sym_eq.
apply round_UP_small_pos with (1 := Hex) (2 := Hxe).
now apply valid_exp.
rewrite Hd3, Hu3.
rewrite Zmult_1_l.
simpl.
destruct exists_NE_ as [H|H].
apply Zeven_Zpower_odd with (2 := H).
apply Zle_minus_le_0.
now apply valid_exp.
rewrite (proj2 (H ex)).
now rewrite Zminus_diag.
exact Hxe.

assert (Hd4: (bpow (ex - 1) <= Rabs (F2R xd) < bpow ex)%R).
rewrite Rabs_pos_eq.
rewrite Hxd.
split.
apply (round_DN_pt beta fexp x).
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
lia.
apply Hex.
apply Rle_lt_trans with (2 := proj2 Hex).
apply (round_DN_pt beta fexp x).
rewrite Hxd.
apply (round_DN_pt beta fexp x).
apply generic_format_0.
now apply Rlt_le.
assert (Hxe2 : (fexp (ex + 1) <= ex)%Z) by now apply valid_exp.
assert (Hud: (F2R xu = F2R xd + ulp beta fexp x)%R).
rewrite Hxu, Hxd.
now apply round_UP_DN_ulp.
destruct (total_order_T (bpow ex) (F2R xu)) as [[Hu2|Hu2]|Hu2].

elim (Rlt_not_le _ _ Hu2).
rewrite Hxu.
apply round_bounded_large_pos...

assert (Hu3: xu = Float beta (1 * Zpower beta (ex - fexp (ex + 1))) (fexp (ex + 1))).
apply canonical_unique with (1 := Hu).
apply (f_equal fexp).
rewrite <- F2R_change_exp.
now rewrite F2R_bpow, mag_bpow.
now apply valid_exp.
rewrite <- Hu2.
apply sym_eq.
rewrite <- F2R_change_exp.
apply F2R_bpow.
exact Hxe2.
assert (Hd3: xd = Float beta (Zpower beta (ex - fexp ex) - 1) (fexp ex)).
assert (H: F2R xd = F2R (Float beta (Zpower beta (ex - fexp ex) - 1) (fexp ex))).
unfold F2R.
simpl.
rewrite minus_IZR.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite IZR_Zpower, <- bpow_plus.
ring_simplify (ex - fexp ex + fexp ex)%Z.
rewrite Hu2, Hud.
rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
unfold cexp.
rewrite mag_unique with beta x ex.
unfold F2R.
simpl.
ring.
rewrite Rabs_pos_eq.
exact Hex.
now apply Rlt_le.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
apply canonical_unique with (1 := Hd) (3 := H).
apply (f_equal fexp).
rewrite <- H.
apply sym_eq.
now apply mag_unique.
rewrite Hd3, Hu3.
unfold Fnum.
rewrite Z.even_mul.
simpl.
unfold Zminus at 2.
rewrite Z.even_add.
rewrite eqb_sym.
simpl.
fold (negb (Z.even (beta ^ (ex - fexp ex)))).
rewrite Bool.negb_involutive.
rewrite (Z.even_pow beta (ex - fexp ex)) by lia.
destruct exists_NE_.
rewrite H.
apply Zeven_Zpower_odd with (2 := H).
now apply Zle_minus_le_0.
apply Z.even_pow.
specialize (H ex).
lia.

revert Hud.
rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
unfold F2R.
rewrite Hd, Hu.
unfold cexp.
rewrite mag_unique with beta (F2R xu) ex.
rewrite mag_unique with (1 := Hd4).
rewrite mag_unique with (1 := Hexa).
intros H.
replace (Fnum xu) with (Fnum xd + 1)%Z.
rewrite Z.even_add.
now apply eqb_sym.
apply sym_eq.
apply eq_IZR.
rewrite plus_IZR.
apply Rmult_eq_reg_r with (bpow (fexp ex)).
rewrite H.
simpl.
ring.
apply Rgt_not_eq.
apply bpow_gt_0.
rewrite Rabs_pos_eq.
split.
apply Rle_trans with (1 := proj1 Hex).
rewrite Hxu.
apply (round_UP_pt beta fexp x).
exact Hu2.
apply Rlt_le.
apply Rlt_le_trans with (1 := H0x).
rewrite Hxu.
apply (round_UP_pt beta fexp x).
Qed.

Theorem DN_UP_parity_generic :
  DN_UP_parity_prop.
Proof using exists_NE_ valid_exp.
apply DN_UP_parity_aux.
apply DN_UP_parity_generic_pos.
Qed.

Theorem Rnd_NE_pt_total :
  round_pred_total Rnd_NE_pt.
Proof using exists_NE_ valid_exp.
apply satisfies_any_imp_NG.
now apply generic_format_satisfies_any.
intros x d u Hf Hd Hu.
generalize (proj1 Hd).
unfold generic_format.
set (ed := cexp beta fexp d).
set (md := Ztrunc (scaled_mantissa beta fexp d)).
intros Hd1.
case_eq (Z.even md) ; [ intros He | intros Ho ].
right.
exists (Float beta md ed).
unfold Generic_fmt.canonical.
rewrite <- Hd1.
now repeat split.
left.
generalize (proj1 Hu).
unfold generic_format.
set (eu := cexp beta fexp u).
set (mu := Ztrunc (scaled_mantissa beta fexp u)).
intros Hu1.
rewrite Hu1.
eexists ; repeat split.
unfold Generic_fmt.canonical.
now rewrite <- Hu1.
rewrite (DN_UP_parity_generic x (Float beta md ed) (Float beta mu eu)).
simpl.
now rewrite Ho.
exact Hf.
unfold Generic_fmt.canonical.
now rewrite <- Hd1.
unfold Generic_fmt.canonical.
now rewrite <- Hu1.
rewrite <- Hd1.
apply Rnd_DN_pt_unique with (1 := Hd).
now apply round_DN_pt.
rewrite <- Hu1.
apply Rnd_UP_pt_unique with (1 := Hu).
now apply round_UP_pt.
Qed.

Theorem Rnd_NE_pt_monotone :
  round_pred_monotone Rnd_NE_pt.
Proof using exists_NE_ valid_exp.
apply Rnd_NG_pt_monotone.
intros x d u Hd Hdn Hu Hun (cd, (Hd1, Hd2)) (cu, (Hu1, Hu2)).
destruct (Req_dec x d) as [Hx|Hx].
rewrite <- Hx.
apply sym_eq.
apply Rnd_UP_pt_idempotent with (1 := Hu).
rewrite Hx.
apply Hd.
rewrite (DN_UP_parity_aux DN_UP_parity_generic_pos x cd cu) in Hu2 ; try easy.
now rewrite (proj2 Hd2) in Hu2.
intros Hf.
apply Hx.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
rewrite <- Hd1.
apply Rnd_DN_pt_unique with (1 := Hd).
now apply round_DN_pt.
rewrite <- Hu1.
apply Rnd_UP_pt_unique with (1 := Hu).
now apply round_UP_pt.
Qed.

Theorem Rnd_NE_pt_round :
  round_pred Rnd_NE_pt.
Proof using exists_NE_ valid_exp.
split.
apply Rnd_NE_pt_total.
apply Rnd_NE_pt_monotone.
Qed.

Lemma round_NE_pt_pos :
  forall x,
  (0 < x)%R ->
  Rnd_NE_pt x (round beta fexp ZnearestE x).
Proof using exists_NE_ valid_exp.
Proof with auto with typeclass_instances.
intros x Hx.
split.
now apply round_N_pt.
unfold NE_prop.
set (mx := scaled_mantissa beta fexp x).
set (xr := round beta fexp ZnearestE x).
destruct (Req_dec (mx - IZR (Zfloor mx)) (/2)) as [Hm|Hm].

left.
exists (Float beta (Ztrunc (scaled_mantissa beta fexp xr)) (cexp beta fexp xr)).
split.
apply round_N_pt...
split.
unfold Generic_fmt.canonical.
simpl.
apply f_equal.
apply round_N_pt...
simpl.
unfold xr, round, Znearest.
fold mx.
rewrite Hm.
rewrite Rcompare_Eq.
2: apply refl_equal.
case_eq (Z.even (Zfloor mx)) ; intros Hmx.

change (Z.even (Ztrunc (scaled_mantissa beta fexp (round beta fexp Zfloor x))) = true).
destruct (Rle_or_lt (round beta fexp Zfloor x) 0) as [Hr|Hr].
rewrite (Rle_antisym _ _ Hr).
unfold scaled_mantissa.
rewrite Rmult_0_l.
now rewrite Ztrunc_IZR.
rewrite <- (round_0 beta fexp Zfloor).
apply round_le...
now apply Rlt_le.
rewrite scaled_mantissa_DN...
now rewrite Ztrunc_IZR.

change (Z.even (Ztrunc (scaled_mantissa beta fexp (round beta fexp Zceil x))) = true).
destruct (mag beta x) as (ex, Hex).
specialize (Hex (Rgt_not_eq _ _ Hx)).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hx)) in Hex.
destruct (Z_lt_le_dec (fexp ex) ex) as [He|He].

assert (Hu := round_bounded_large_pos _ _ Zceil _ _ He Hex).
assert (Hfc: Zceil mx = (Zfloor mx + 1)%Z).
apply Zceil_floor_neq.
intros H.
rewrite H in Hm.
unfold Rminus in Hm.
rewrite Rplus_opp_r in Hm.
elim (Rlt_irrefl 0).
rewrite Hm at 2.
apply Rinv_0_lt_compat.
now apply IZR_lt.
destruct (proj2 Hu) as [Hu'|Hu'].

unfold scaled_mantissa.
rewrite cexp_fexp_pos with (1 := conj (proj1 Hu) Hu').
unfold round, F2R.
simpl.
rewrite cexp_fexp_pos with (1 := Hex).
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
rewrite Ztrunc_IZR.
fold mx.
rewrite Hfc.
now rewrite Z.even_add, Hmx.

rewrite Hu'.
unfold scaled_mantissa, cexp.
rewrite mag_bpow.
rewrite <- bpow_plus, <- IZR_Zpower.
rewrite Ztrunc_IZR.
case_eq (Z.even beta) ; intros Hr.
destruct exists_NE_ as [Hs|Hs].
now rewrite Hs in Hr.
destruct (Hs ex) as (H,_).
rewrite Z.even_pow.
exact Hr.
lia.
assert (Z.even (Zfloor mx) = true).
2: now rewrite H in Hmx.
replace (Zfloor mx) with (Zceil mx + -1)%Z by lia.
rewrite Z.even_add.
apply eqb_true.
unfold mx.
replace (Zceil (scaled_mantissa beta fexp x)) with (Zpower beta (ex - fexp ex)).
rewrite Zeven_Zpower_odd with (2 := Hr).
easy.
lia.
apply eq_IZR.
rewrite IZR_Zpower by lia.
apply Rmult_eq_reg_r with (bpow (fexp ex)).
unfold Zminus.
rewrite bpow_plus.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_l, Rmult_1_r.
pattern (fexp ex) ; rewrite <- cexp_fexp_pos with (1 := Hex).
now apply sym_eq.
apply Rgt_not_eq.
apply bpow_gt_0.
generalize (proj1 (valid_exp ex) He).
lia.

assert (Z.even (Zfloor mx) = true).
2: now rewrite H in Hmx.
unfold mx, scaled_mantissa.
rewrite cexp_fexp_pos with (1 := Hex).
now rewrite mantissa_DN_small_pos.

right.
intros g Hg.
destruct (Req_dec x g) as [Hxg|Hxg].
rewrite <- Hxg.
apply sym_eq.
apply round_generic...
rewrite Hxg.
apply Hg.
set (d := round beta fexp Zfloor x).
set (u := round beta fexp Zceil x).
apply Rnd_N_pt_unique with (d := d) (u := u) (4 := Hg).
now apply round_DN_pt.
now apply round_UP_pt.
2: now apply round_N_pt.
rewrite <- (scaled_mantissa_mult_bpow beta fexp x).
unfold d, u, round, F2R.
simpl.
fold mx.
rewrite <- 2!Rmult_minus_distr_r.
intros H.
apply Rmult_eq_reg_r in H.
apply Hm.
apply Rcompare_Eq_inv.
rewrite Rcompare_floor_ceil_middle.
now apply Rcompare_Eq.
contradict Hxg.
apply sym_eq.
apply Rnd_N_pt_idempotent with (1 := Hg).
rewrite <- (scaled_mantissa_mult_bpow beta fexp x).
fold mx.
rewrite <- Hxg.
change (IZR (Zfloor mx) * bpow (cexp beta fexp x))%R with d.
now eapply round_DN_pt.
apply Rgt_not_eq.
apply bpow_gt_0.
Qed.

Theorem round_NE_opp :
  forall x,
  round beta fexp ZnearestE (-x) = (- round beta fexp ZnearestE x)%R.
Proof using .
intros x.
unfold round.
simpl.
rewrite scaled_mantissa_opp, cexp_opp.
rewrite Znearest_opp.
rewrite <- F2R_Zopp.
apply (f_equal (fun v => F2R (Float beta (-v) _))).
set (m := scaled_mantissa beta fexp x).
unfold Znearest.
case Rcompare ; trivial.
apply (f_equal (fun (b : bool) => if b then Zceil m else Zfloor m)).
rewrite Bool.negb_involutive.
rewrite Z.even_opp.
rewrite Z.even_add.
now rewrite eqb_sym.
Qed.

Lemma round_NE_abs:
  forall x : R,
  round beta fexp ZnearestE (Rabs x) = Rabs (round beta fexp ZnearestE x).
Proof using valid_exp.
Proof with auto with typeclass_instances.
intros x.
apply sym_eq.
unfold Rabs at 2.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite round_NE_opp.
apply Rabs_left1.
rewrite <- (round_0 beta fexp ZnearestE).
apply round_le...
now apply Rlt_le.
apply Rabs_pos_eq.
rewrite <- (round_0 beta fexp ZnearestE).
apply round_le...
now apply Rge_le.
Qed.

Theorem round_NE_pt :
  forall x,
  Rnd_NE_pt x (round beta fexp ZnearestE x).
Proof using exists_NE_ valid_exp.
Proof with auto with typeclass_instances.
intros x.
destruct (total_order_T x 0) as [[Hx|Hx]|Hx].
apply Rnd_NG_pt_opp_inv.
apply generic_format_opp.
unfold NE_prop.
intros _ f ((mg,eg),(H1,(H2,H3))).
exists (Float beta (- mg) eg).
repeat split.
rewrite H1.
now rewrite F2R_Zopp.
now apply canonical_opp.
simpl.
now rewrite Z.even_opp.
rewrite <- round_NE_opp.
apply round_NE_pt_pos.
now apply Ropp_0_gt_lt_contravar.
rewrite Hx, round_0...
apply Rnd_NG_pt_refl.
apply generic_format_0.
now apply round_NE_pt_pos.
Qed.

End Fcore_rnd_NE.

Notation rndNE := ZnearestE (only parsing).

End Round_NE.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Round_NE.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_FIX.
Module Export Flocq.
Module Export Core.
Module Export FIX.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Ulp Flocq.Core.Round_NE.

Section RND_FIX.

Variable beta : radix.

Notation bpow := (bpow beta).

Variable emin : Z.

Inductive FIX_format (x : R) : Prop :=
  FIX_spec (f : float beta) :
    x = F2R f -> (Fexp f = emin)%Z -> FIX_format x.

Definition FIX_exp (e : Z) := emin.

Global Instance FIX_exp_valid : Valid_exp FIX_exp.
Proof using .
intros k.
unfold FIX_exp.
split ; intros H.
now apply Zlt_le_weak.
split.
apply Z.le_refl.
now intros _ _.
Qed.

Theorem generic_format_FIX :
  forall x, FIX_format x -> generic_format beta FIX_exp x.
Proof using .
intros x [[xm xe] Hx1 Hx2].
rewrite Hx1.
now apply generic_format_canonical.
Qed.

Theorem FIX_format_generic :
  forall x, generic_format beta FIX_exp x -> FIX_format x.
Proof using .
intros x H.
rewrite H.
eexists ; repeat split.
Qed.

Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
Proof using .
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FIX_exp)).
intros x.
split.
apply FIX_format_generic.
apply generic_format_FIX.
Qed.

Global Instance FIX_exp_monotone : Monotone_exp FIX_exp.
Proof using .
intros ex ey H.
apply Z.le_refl.
Qed.

Theorem ulp_FIX :
  forall x, ulp beta FIX_exp x = bpow emin.
Proof using .
intros x; unfold ulp.
case Req_bool_spec; intros Zx.
case (negligible_exp_spec FIX_exp).
intros T; specialize (T (emin-1)%Z); contradict T.
unfold FIX_exp; lia.
intros n _; reflexivity.
reflexivity.
Qed.

Global Instance exists_NE_FIX :
      Exists_NE beta FIX_exp.
Proof using .
unfold Exists_NE, FIX_exp; simpl.
right; split; auto.
Qed.

End RND_FIX.

Theorem round_FIX_IZR :
  forall f x,
  round radix2 (FIX_exp 0) f x = IZR (f x).
Proof.
  intros f x.
unfold round, F2R.
simpl.
rewrite Rmult_1_r.
apply f_equal.
  apply f_equal.
unfold scaled_mantissa.
simpl.
apply Rmult_1_r.
Qed.

End FIX.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_FIX.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_FLX.
Module Export Flocq.
Module Export Core.
Module Export FLX.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Float_prop Flocq.Core.FIX Flocq.Core.Ulp Flocq.Core.Round_NE.

Section RND_FLX.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable prec : Z.

Class Prec_gt_0 :=
  prec_gt_0 : (0 < prec)%Z.

Context { prec_gt_0_ : Prec_gt_0 }.

Inductive FLX_format (x : R) : Prop :=
  FLX_spec (f : float beta) :
    x = F2R f -> (Z.abs (Fnum f) < Zpower beta prec)%Z -> FLX_format x.

Definition FLX_exp (e : Z) := (e - prec)%Z.

Global Instance FLX_exp_valid : Valid_exp FLX_exp.
Proof using prec_gt_0_.
intros k.
unfold FLX_exp.
generalize prec_gt_0.
repeat split ; intros ; lia.
Qed.

Theorem FIX_format_FLX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FLX_format x ->
  FIX_format beta (e - prec) x.
Proof using .
clear prec_gt_0_.
intros x e Hx [[xm xe] H1 H2].
rewrite H1, (F2R_prec_normalize beta xm xe e prec).
now eexists.
exact H2.
now rewrite <- H1.
Qed.

Theorem FLX_format_generic :
  forall x, generic_format beta FLX_exp x -> FLX_format x.
Proof using prec_gt_0_.
intros x H.
rewrite H.
eexists ; repeat split.
simpl.
apply lt_IZR.
rewrite abs_IZR.
rewrite <- scaled_mantissa_generic with (1 := H).
rewrite <- scaled_mantissa_abs.
apply Rmult_lt_reg_r with (bpow (cexp beta FLX_exp (Rabs x))).
apply bpow_gt_0.
rewrite scaled_mantissa_mult_bpow.
rewrite IZR_Zpower, <- bpow_plus.
2: now apply Zlt_le_weak.
unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta (Rabs x) - prec))%Z.
rewrite mag_abs.
destruct (Req_dec x 0) as [Hx|Hx].
rewrite Hx, Rabs_R0.
apply bpow_gt_0.
destruct (mag beta x) as (ex, Ex).
now apply Ex.
Qed.

Theorem generic_format_FLX :
  forall x, FLX_format x -> generic_format beta FLX_exp x.
Proof using .
clear prec_gt_0_.
intros x [[mx ex] H1 H2].
simpl in H2.
rewrite H1.
apply generic_format_F2R.
intros Zmx.
unfold cexp, FLX_exp.
rewrite mag_F2R with (1 := Zmx).
apply Zplus_le_reg_r with (prec - ex)%Z.
ring_simplify.
now apply mag_le_Zpower.
Qed.

Theorem FLX_format_satisfies_any :
  satisfies_any FLX_format.
Proof using prec_gt_0_.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp)).
intros x.
split.
apply FLX_format_generic.
apply generic_format_FLX.
Qed.

Theorem FLX_format_FIX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FIX_format beta (e - prec) x ->
  FLX_format x.
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
intros x e Hx Fx.
apply FLX_format_generic.
apply generic_format_FIX in Fx.
revert Fx.
apply generic_inclusion with (e := e)...
apply Z.le_refl.
Qed.

Inductive FLXN_format (x : R) : Prop :=
  FLXN_spec (f : float beta) :
    x = F2R f ->
    (x <> 0%R -> Zpower beta (prec - 1) <= Z.abs (Fnum f) < Zpower beta prec)%Z ->
    FLXN_format x.

Theorem generic_format_FLXN :
  forall x, FLXN_format x -> generic_format beta FLX_exp x.
Proof using .
intros x [[xm ex] H1 H2].
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx.
apply generic_format_0.
specialize (H2 Zx).
apply generic_format_FLX.
rewrite H1.
eexists ; repeat split.
apply H2.
Qed.

Theorem FLXN_format_generic :
  forall x, generic_format beta FLX_exp x -> FLXN_format x.
Proof using prec_gt_0_.
intros x Hx.
rewrite Hx.
simpl.
eexists.
easy.
rewrite <- Hx.
intros Zx.
simpl.
split.

apply le_IZR.
rewrite IZR_Zpower.
2: now apply Zlt_0_le_0_pred.
rewrite abs_IZR, <- scaled_mantissa_generic with (1 := Hx).
apply Rmult_le_reg_r with (bpow (cexp beta FLX_exp x)).
apply bpow_gt_0.
rewrite <- bpow_plus.
rewrite <- scaled_mantissa_abs.
rewrite <- cexp_abs.
rewrite scaled_mantissa_mult_bpow.
unfold cexp, FLX_exp.
rewrite mag_abs.
ring_simplify (prec - 1 + (mag beta x - prec))%Z.
destruct (mag beta x) as (ex,Ex).
now apply Ex.

apply lt_IZR.
rewrite IZR_Zpower.
2: now apply Zlt_le_weak.
rewrite abs_IZR, <- scaled_mantissa_generic with (1 := Hx).
apply Rmult_lt_reg_r with (bpow (cexp beta FLX_exp x)).
apply bpow_gt_0.
rewrite <- bpow_plus.
rewrite <- scaled_mantissa_abs.
rewrite <- cexp_abs.
rewrite scaled_mantissa_mult_bpow.
unfold cexp, FLX_exp.
rewrite mag_abs.
ring_simplify (prec + (mag beta x - prec))%Z.
destruct (mag beta x) as (ex,Ex).
now apply Ex.
Qed.

Theorem FLXN_format_satisfies_any :
  satisfies_any FLXN_format.
Proof using prec_gt_0_.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp)).
split ; intros H.
now apply FLXN_format_generic.
now apply generic_format_FLXN.
Qed.

Lemma negligible_exp_FLX :
   negligible_exp FLX_exp = None.
Proof using prec_gt_0_.
case (negligible_exp_spec FLX_exp).
intros _; reflexivity.
intros n H2; contradict H2.
unfold FLX_exp; unfold Prec_gt_0 in prec_gt_0_; lia.
Qed.

Theorem generic_format_FLX_1 :
  generic_format beta FLX_exp 1.
Proof using prec_gt_0_.
unfold generic_format, scaled_mantissa, cexp, F2R; simpl.
rewrite Rmult_1_l, (mag_unique beta 1 1).
{
 unfold FLX_exp.
  rewrite <- IZR_Zpower; [|unfold Prec_gt_0 in prec_gt_0_; lia].
  rewrite Ztrunc_IZR, IZR_Zpower; [|unfold Prec_gt_0 in prec_gt_0_; lia].
  rewrite <- bpow_plus.
  now replace (_ + _)%Z with Z0 by ring.
}
rewrite Rabs_R1; simpl; split; [now right|].
unfold Z.pow_pos; simpl; rewrite Zmult_1_r; apply IZR_lt.
assert (H := Zle_bool_imp_le _ _ (radix_prop beta)); lia.
Qed.

Theorem ulp_FLX_0: (ulp beta FLX_exp 0 = 0)%R.
Proof using prec_gt_0_.
unfold ulp; rewrite Req_bool_true; trivial.
rewrite negligible_exp_FLX; easy.
Qed.

Lemma ulp_FLX_1 : ulp beta FLX_exp 1 = bpow (-prec + 1).
Proof using .
unfold ulp, FLX_exp, cexp; rewrite Req_bool_false; [|apply R1_neq_R0].
rewrite mag_1; f_equal; ring.
Qed.

Lemma succ_FLX_1 : (succ beta FLX_exp 1 = 1 + bpow (-prec + 1))%R.
Proof using .
now unfold succ; rewrite Rle_bool_true; [|apply Rle_0_1]; rewrite ulp_FLX_1.
Qed.

Theorem eq_0_round_0_FLX :
   forall rnd {Vr: Valid_rnd rnd} x,
     round beta FLX_exp rnd x = 0%R -> x = 0%R.
Proof using prec_gt_0_.
intros rnd Hr x.
apply eq_0_round_0_negligible_exp; try assumption.
apply FLX_exp_valid.
apply negligible_exp_FLX.
Qed.

Theorem gt_0_round_gt_0_FLX :
   forall rnd {Vr: Valid_rnd rnd} x,
     (0 < x)%R -> (0 < round beta FLX_exp rnd x)%R.
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
intros rnd Hr x Hx.
assert (K: (0 <= round beta FLX_exp rnd x)%R).
rewrite <- (round_0 beta FLX_exp rnd).
apply round_le...
now apply Rlt_le.
destruct K; try easy.
absurd (x = 0)%R.
now apply Rgt_not_eq.
apply eq_0_round_0_FLX with rnd...
Qed.

Theorem ulp_FLX_le :
  forall x, (ulp beta FLX_exp x <= Rabs x * bpow (1-prec))%R.
Proof using prec_gt_0_.
intros x; case (Req_dec x 0); intros Hx.
rewrite Hx, ulp_FLX_0, Rabs_R0.
right; ring.
rewrite ulp_neq_0; try exact Hx.
unfold cexp, FLX_exp.
replace (mag beta x - prec)%Z with ((mag beta x - 1) + (1-prec))%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply bpow_mag_le.
Qed.

Theorem ulp_FLX_ge :
  forall x, (Rabs x * bpow (-prec) <= ulp beta FLX_exp x)%R.
Proof using prec_gt_0_.
intros x; case (Req_dec x 0); intros Hx.
rewrite Hx, ulp_FLX_0, Rabs_R0.
right; ring.
rewrite ulp_neq_0; try exact Hx.
unfold cexp, FLX_exp.
unfold Zminus; rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
left; now apply bpow_mag_gt.
Qed.

Lemma ulp_FLX_exact_shift :
  forall x e,
  (ulp beta FLX_exp (x * bpow e) = ulp beta FLX_exp x * bpow e)%R.
Proof using prec_gt_0_.
intros x e.
destruct (Req_dec x 0) as [Hx|Hx].
{
 unfold ulp.
  now rewrite !Req_bool_true, negligible_exp_FLX; rewrite ?Hx, ?Rmult_0_l.
}
unfold ulp; rewrite Req_bool_false;
  [|now intro H; apply Hx, (Rmult_eq_reg_r (bpow e));
    [rewrite Rmult_0_l|apply Rgt_not_eq, Rlt_gt, bpow_gt_0]].
rewrite (Req_bool_false _ _ Hx), <- bpow_plus; f_equal; unfold cexp, FLX_exp.
now rewrite mag_mult_bpow; [ring|].
Qed.

Lemma succ_FLX_exact_shift :
  forall x e,
  (succ beta FLX_exp (x * bpow e) = succ beta FLX_exp x * bpow e)%R.
Proof using prec_gt_0_.
intros x e.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{
 rewrite succ_eq_pos; [|now apply Rmult_le_pos, bpow_ge_0].
  rewrite (succ_eq_pos _ _ _ Px).
  now rewrite Rmult_plus_distr_r; f_equal; apply ulp_FLX_exact_shift.
}
unfold succ.
rewrite Rle_bool_false; [|assert (H := bpow_gt_0 beta e); nra].
rewrite Rle_bool_false; [|now simpl].
rewrite Ropp_mult_distr_l_reverse, <-Ropp_mult_distr_l_reverse; f_equal.
unfold pred_pos.
rewrite mag_mult_bpow; [|lra].
replace (_ - 1)%Z with (mag beta (- x) - 1 + e)%Z; [|ring]; rewrite bpow_plus.
unfold Req_bool; rewrite Rcompare_mult_r; [|now apply bpow_gt_0].
fold (Req_bool (-x) (bpow (mag beta (-x) - 1))); case Req_bool.
{
 unfold FLX_exp.
  replace (_ - _)%Z with (mag beta (- x) - 1 - prec + e)%Z; [|ring].
  rewrite bpow_plus; ring.
}
rewrite ulp_FLX_exact_shift; ring.
Qed.

Lemma pred_FLX_exact_shift :
  forall x e,
  (pred beta FLX_exp (x * bpow e) = pred beta FLX_exp x * bpow e)%R.
Proof using prec_gt_0_.
intros x e.
unfold pred.
rewrite Ropp_mult_distr_l, succ_FLX_exact_shift.
apply Ropp_mult_distr_l.
Qed.

Global Instance FLX_exp_monotone : Monotone_exp FLX_exp.
Proof using .
intros ex ey Hxy.
now apply Zplus_le_compat_r.
Qed.

Hypothesis NE_prop : Z.even beta = false \/ (1 < prec)%Z.

Global Instance exists_NE_FLX : Exists_NE beta FLX_exp.
Proof using NE_prop.
destruct NE_prop as [H|H].
now left.
right.
unfold FLX_exp.
split ; lia.
Qed.

End RND_FLX.

End FLX.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_FLX.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_FLT.
Module Export Flocq.
Module Export Core.
Module Export FLT.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Float_prop Flocq.Core.FLX Flocq.Core.FIX Flocq.Core.Ulp Flocq.Core.Round_NE.

Section RND_FLT.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable emin prec : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Inductive FLT_format (x : R) : Prop :=
  FLT_spec (f : float beta) :
    x = F2R f -> (Z.abs (Fnum f) < Zpower beta prec)%Z ->
    (emin <= Fexp f)%Z -> FLT_format x.

Definition FLT_exp e := Z.max (e - prec) emin.

Global Instance FLT_exp_valid : Valid_exp FLT_exp.
Proof using prec_gt_0_.
intros k.
unfold FLT_exp.
generalize (prec_gt_0 prec).
repeat split ;
  intros ; zify ; lia.
Qed.

Theorem generic_format_FLT :
  forall x, FLT_format x -> generic_format beta FLT_exp x.
Proof using .
clear prec_gt_0_.
intros x [[mx ex] H1 H2 H3].
simpl in H2, H3.
rewrite H1.
apply generic_format_F2R.
intros Zmx.
unfold cexp, FLT_exp.
rewrite mag_F2R with (1 := Zmx).
apply Z.max_lub with (2 := H3).
apply Zplus_le_reg_r with (prec - ex)%Z.
ring_simplify.
now apply mag_le_Zpower.
Qed.

Theorem FLT_format_generic :
  forall x, generic_format beta FLT_exp x -> FLT_format x.
Proof using prec_gt_0_.
intros x.
unfold generic_format.
set (ex := cexp beta FLT_exp x).
set (mx := Ztrunc (scaled_mantissa beta FLT_exp x)).
intros Hx.
rewrite Hx.
eexists ; repeat split ; simpl.
apply lt_IZR.
rewrite IZR_Zpower.
2: now apply Zlt_le_weak.
apply Rmult_lt_reg_r with (bpow ex).
apply bpow_gt_0.
rewrite <- bpow_plus.
change (F2R (Float beta (Z.abs mx) ex) < bpow (prec + ex))%R.
rewrite F2R_Zabs.
rewrite <- Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
unfold cexp in ex.
destruct (mag beta x) as (ex', He).
simpl in ex.
specialize (He Hx0).
apply Rlt_le_trans with (1 := proj2 He).
apply bpow_le.
cut (ex' - prec <= ex)%Z.
lia.
unfold ex, FLT_exp.
apply Z.le_max_l.
apply Z.le_max_r.
Qed.

Theorem generic_format_FLT_bpow :
  forall e, (emin <= e)%Z -> generic_format beta FLT_exp (bpow e).
Proof using prec_gt_0_.
intros e He.
apply generic_format_bpow; unfold FLT_exp.
apply Z.max_case; try assumption.
unfold Prec_gt_0 in prec_gt_0_; lia.
Qed.

Theorem FLT_format_bpow :
  forall e, (emin <= e)%Z -> FLT_format (bpow e).
Proof using prec_gt_0_.
intros e He.
apply FLT_format_generic.
now apply generic_format_FLT_bpow.
Qed.

Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
Proof using prec_gt_0_.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLT_exp)).
intros x.
split.
apply FLT_format_generic.
apply generic_format_FLT.
Qed.

Theorem cexp_FLT_FLX :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  cexp beta FLT_exp x = cexp beta (FLX_exp prec) x.
Proof using .
intros x Hx.
assert (Hx0: x <> 0%R).
intros H1; rewrite H1, Rabs_R0 in Hx.
contradict Hx; apply Rlt_not_le, bpow_gt_0.
unfold cexp.
apply Zmax_left.
destruct (mag beta x) as (ex, He).
unfold FLX_exp.
simpl.
specialize (He Hx0).
cut (emin + prec - 1 < ex)%Z.
lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := Hx).
apply He.
Qed.

Global Instance FLT_exp_monotone : Monotone_exp FLT_exp.
Proof using .
intros ex ey.
unfold FLT_exp.
zify ; lia.
Qed.

Global Instance exists_NE_FLT :
  (Z.even beta = false \/ (1 < prec)%Z) ->
  Exists_NE beta FLT_exp.
Proof using .
intros [H|H].
now left.
right.
intros e.
unfold FLT_exp.
destruct (Zmax_spec (e - prec) emin) as [(H1,H2)|(H1,H2)] ;
  rewrite H2 ; clear H2.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (e - prec + 1 - prec) emin).
lia.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (emin + 1 - prec) emin).
lia.
Qed.

Theorem generic_format_FLT_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  generic_format beta (FLX_exp prec) x ->
  generic_format beta FLT_exp x.
Proof using .
intros x Hx H.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0.
apply generic_format_0.
unfold generic_format, scaled_mantissa.
now rewrite cexp_FLT_FLX.
Qed.

Theorem generic_format_FLX_FLT :
  forall x : R,
  generic_format beta FLT_exp x -> generic_format beta (FLX_exp prec) x.
Proof using .
clear prec_gt_0_.
intros x Hx.
unfold generic_format in Hx; rewrite Hx.
apply generic_format_F2R.
intros _.
rewrite <- Hx.
unfold cexp, FLX_exp, FLT_exp.
apply Z.le_max_l.
Qed.

Theorem round_FLT_FLX : forall rnd x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FLT_exp rnd x = round beta (FLX_exp prec) rnd x.
Proof using .
intros rnd x Hx.
unfold round, scaled_mantissa.
rewrite cexp_FLT_FLX ; trivial.
Qed.

Theorem cexp_FLT_FIX :
  forall x, x <> 0%R ->
  (Rabs x < bpow (emin + prec))%R ->
  cexp beta FLT_exp x = cexp beta (FIX_exp emin) x.
Proof using .
intros x Hx0 Hx.
unfold cexp.
apply Zmax_right.
unfold FIX_exp.
destruct (mag beta x) as (ex, Hex).
simpl.
cut (ex - 1 < emin + prec)%Z.
lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := Hx).
now apply Hex.
Qed.

Theorem generic_format_FIX_FLT :
  forall x : R,
  generic_format beta FLT_exp x ->
  generic_format beta (FIX_exp emin) x.
Proof using .
clear prec_gt_0_.
intros x Hx.
rewrite Hx.
apply generic_format_F2R.
intros _.
rewrite <- Hx.
apply Z.le_max_r.
Qed.

Theorem generic_format_FLT_FIX :
  forall x : R,
  (Rabs x <= bpow (emin + prec))%R ->
  generic_format beta (FIX_exp emin) x ->
  generic_format beta FLT_exp x.
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
apply generic_inclusion_le...
intros e He.
unfold FIX_exp.
apply Z.max_lub.
lia.
apply Z.le_refl.
Qed.

Lemma negligible_exp_FLT :
  exists n, negligible_exp FLT_exp = Some n /\ (n <= emin)%Z.
Proof using prec_gt_0_.
case (negligible_exp_spec FLT_exp).
{
 intro H; exfalso; specialize (H emin); revert H.
  apply Zle_not_lt, Z.le_max_r.
}
intros n Hn; exists n; split; [now simpl|].
destruct (Z.max_spec (n - prec) emin) as [(Hm, Hm')|(Hm, Hm')].
{
 now revert Hn; unfold FLT_exp; rewrite Hm'.
}
revert Hn prec_gt_0_; unfold FLT_exp, Prec_gt_0; rewrite Hm'; lia.
Qed.

Theorem generic_format_FLT_1 :
  (emin <= 0)%Z ->
  generic_format beta FLT_exp 1.
Proof using prec_gt_0_.
intros Hemin.
now apply (generic_format_FLT_bpow 0).
Qed.

Theorem ulp_FLT_0 :
  ulp beta FLT_exp 0 = bpow emin.
Proof using prec_gt_0_.
unfold ulp.
rewrite Req_bool_true by easy.
case negligible_exp_spec.
-
 intros T.
  elim Zle_not_lt with (2 := T emin).
  apply Z.le_max_r.
-
 intros n Hn.
  apply f_equal.
  assert (H: FLT_exp emin = emin).
    apply Z.max_r.
    generalize (prec_gt_0 prec).
    clear ; lia.
  rewrite <- H.
  apply fexp_negligible_exp_eq.
  apply FLT_exp_valid.
  exact Hn.
  rewrite H.
  apply Z.le_refl.
Qed.

Theorem ulp_FLT_small :
  forall x, (Rabs x < bpow (emin + prec))%R ->
  ulp beta FLT_exp x = bpow emin.
Proof using prec_gt_0_.
intros x Hx.
destruct (Req_dec x 0%R) as [Zx|Zx].
{
 rewrite Zx.
  apply ulp_FLT_0.
}
rewrite ulp_neq_0 by easy.
apply f_equal.
apply Z.max_r.
destruct (mag beta x) as [e He].
simpl.
cut (e - 1 < emin + prec)%Z.
lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (2 := Hx).
now apply He.
Qed.

Theorem ulp_FLT_le :
  forall x, (bpow (emin + prec - 1) <= Rabs x)%R ->
  (ulp beta FLT_exp x <= Rabs x * bpow (1 - prec))%R.
Proof using .
intros x Hx.
assert (Zx : (x <> 0)%R).
  intros Z; contradict Hx; apply Rgt_not_le, Rlt_gt.
  rewrite Z, Rabs_R0; apply bpow_gt_0.
rewrite ulp_neq_0 with (1 := Zx).
unfold cexp, FLT_exp.
destruct (mag beta x) as (e,He).
apply Rle_trans with (bpow (e-1)*bpow (1-prec))%R.
rewrite <- bpow_plus.
right; apply f_equal.
replace (e - 1 + (1 - prec))%Z with (e - prec)%Z by ring.
apply Z.max_l; simpl.
cut (emin+prec-1 < e)%Z.
lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=Hx).
now apply He.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply He.
Qed.

Theorem ulp_FLT_gt :
  forall x, (Rabs x * bpow (-prec) < ulp beta FLT_exp x)%R.
Proof using prec_gt_0_.
intros x; case (Req_dec x 0); intros Hx.
rewrite Hx, ulp_FLT_small, Rabs_R0, Rmult_0_l; try apply bpow_gt_0.
rewrite Rabs_R0; apply bpow_gt_0.
rewrite ulp_neq_0; try exact Hx.
unfold cexp, FLT_exp.
apply Rlt_le_trans with (bpow (mag beta x)*bpow (-prec))%R.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
now apply bpow_mag_gt.
rewrite <- bpow_plus.
apply bpow_le.
apply Z.le_max_l.
Qed.

Lemma ulp_FLT_exact_shift :
  forall x e,
  (x <> 0)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (ulp beta FLT_exp (x * bpow e) = ulp beta FLT_exp x * bpow e)%R.
Proof using .
intros x e Nzx Hmx He.
unfold ulp; rewrite Req_bool_false;
  [|now intro H; apply Nzx, (Rmult_eq_reg_r (bpow e));
    [rewrite Rmult_0_l|apply Rgt_not_eq, Rlt_gt, bpow_gt_0]].
rewrite (Req_bool_false _ _ Nzx), <- bpow_plus; f_equal; unfold cexp, FLT_exp.
rewrite (mag_mult_bpow _ _ _ Nzx), !Z.max_l; lia.
Qed.

Lemma succ_FLT_exact_shift_pos :
  forall x e,
  (0 < x)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
Proof using .
intros x e Px Hmx He.
rewrite succ_eq_pos; [|now apply Rlt_le, Rmult_lt_0_compat, bpow_gt_0].
rewrite (succ_eq_pos _ _ _ (Rlt_le _ _ Px)).
now rewrite Rmult_plus_distr_r; f_equal; apply ulp_FLT_exact_shift; [lra| |].
Qed.

Lemma succ_FLT_exact_shift :
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
  (succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
Proof using .
intros x e Nzx Hmx He.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{
 now apply succ_FLT_exact_shift_pos; [lra|lia|lia].
}
unfold succ.
rewrite Rle_bool_false; [|assert (H := bpow_gt_0 beta e); nra].
rewrite Rle_bool_false; [|now simpl].
rewrite Ropp_mult_distr_l_reverse, <-Ropp_mult_distr_l_reverse; f_equal.
unfold pred_pos.
rewrite mag_mult_bpow; [|lra].
replace (_ - 1)%Z with (mag beta (- x) - 1 + e)%Z; [|ring]; rewrite bpow_plus.
unfold Req_bool; rewrite Rcompare_mult_r; [|now apply bpow_gt_0].
fold (Req_bool (-x) (bpow (mag beta (-x) - 1))); case Req_bool.
{
 rewrite mag_opp; unfold FLT_exp; do 2 (rewrite Z.max_l; [|lia]).
  replace (_ - _)%Z with (mag beta x - 1 - prec + e)%Z; [|ring].
  rewrite bpow_plus; ring.
}
rewrite ulp_FLT_exact_shift; [ring|lra| |]; rewrite mag_opp; lia.
Qed.

Lemma pred_FLT_exact_shift :
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
  (pred beta FLT_exp (x * bpow e) = pred beta FLT_exp x * bpow e)%R.
Proof using .
intros x e Nzx Hmx He.
unfold pred.
rewrite Ropp_mult_distr_l.
rewrite succ_FLT_exact_shift.
apply Ropp_mult_distr_l.
lra.
now rewrite mag_opp.
now rewrite mag_opp.
Qed.

Theorem ulp_FLT_pred_pos :
  forall x,
  generic_format beta FLT_exp x ->
  (0 <= x)%R ->
  ulp beta FLT_exp (pred beta FLT_exp x) = ulp beta FLT_exp x \/
  (x = bpow (mag beta x - 1) /\ ulp beta FLT_exp (pred beta FLT_exp x) = (ulp beta FLT_exp x / IZR beta)%R).
Proof using prec_gt_0_.
intros x Fx [Hx|Hx] ; cycle 1.
{
 rewrite <- Hx.
  rewrite pred_0.
  rewrite ulp_opp.
  left.
  apply ulp_ulp_0.
  apply FLT_exp_valid.
  typeclasses eauto.
}
assert (Hp: (0 <= pred beta FLT_exp x)%R).
{
 apply pred_ge_gt ; try easy.
  apply FLT_exp_valid.
  apply generic_format_0.
}
destruct (Rle_or_lt (bpow (emin + prec)) x) as [Hs|Hs].
-
 unfold ulp.
  rewrite Req_bool_false ; cycle 1.
  {
 intros Zp.
    apply Rle_not_lt with (1 := Hs).
    generalize (f_equal (succ beta FLT_exp) Zp).
    rewrite succ_pred.
    rewrite succ_0, ulp_FLT_0.
    intros H.
    rewrite H.
    apply bpow_lt.
    generalize (prec_gt_0 prec).
    lia.
    apply FLT_exp_valid.
    exact Fx.
}
  rewrite Req_bool_false by now apply Rgt_not_eq.
  unfold cexp.
  destruct (mag beta x) as [e He].
  simpl.
  specialize (He (Rgt_not_eq _ _ Hx)).
  rewrite Rabs_pos_eq in He by now apply Rlt_le.
  destruct (proj1 He) as [Hb|Hb].
  +
 left.
    apply (f_equal (fun v => bpow (FLT_exp v))).
    apply mag_unique.
    rewrite Rabs_pos_eq by easy.
    split.
    *
 apply pred_ge_gt ; try easy.
      apply FLT_exp_valid.
      apply generic_format_FLT_bpow.
      apply Z.lt_le_pred.
      apply lt_bpow with beta.
      apply Rle_lt_trans with (2 := proj2 He).
      apply Rle_trans with (2 := Hs).
      apply bpow_le.
      generalize (prec_gt_0 prec).
      lia.
    *
 apply pred_lt_le.
      now apply Rgt_not_eq.
      now apply Rlt_le.
  +
 right.
    split.
    easy.
    replace (FLT_exp _) with (FLT_exp e + -1)%Z.
    rewrite bpow_plus.
    now rewrite <- (Zmult_1_r beta).
    rewrite <- Hb.
    unfold FLT_exp at 1 2.
    replace (mag_val _ _ (mag _ _)) with (e - 1)%Z.
    rewrite <- Hb in Hs.
    apply le_bpow in Hs.
    zify ; lia.
    apply eq_sym, mag_unique.
    rewrite Hb.
    rewrite Rabs_pos_eq by easy.
    split ; cycle 1.
    {
 apply pred_lt_id.
      now apply Rgt_not_eq.
}
    apply pred_ge_gt.
    apply FLT_exp_valid.
    apply generic_format_FLT_bpow.
    cut (emin + 1 < e)%Z.
lia.
    apply lt_bpow with beta.
    apply Rle_lt_trans with (2 := proj2 He).
    apply Rle_trans with (2 := Hs).
    apply bpow_le.
    generalize (prec_gt_0 prec).
    lia.
    exact Fx.
    apply Rlt_le_trans with (2 := proj1 He).
    apply bpow_lt.
    apply Z.lt_pred_l.
-
 left.
  rewrite (ulp_FLT_small x).
  apply ulp_FLT_small.
  rewrite Rabs_pos_eq by easy.
  apply pred_lt_le.
  now apply Rgt_not_eq.
  now apply Rlt_le.
  rewrite Rabs_pos_eq by now apply Rlt_le.
  exact Hs.
Qed.

End RND_FLT.

End FLT.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_FLT.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_Core.
Module Export Flocq.
Module Export Core.
Module Export Core.

Export Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Digits Flocq.Core.Float_prop Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Round_NE Flocq.Core.FIX Flocq.Core.FLX Flocq.Core.FLT Flocq.Core.Ulp.

End Core.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Core.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Calc_DOT_Round.
Module Export Flocq.
Module Export Calc.
Module Export Round.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Core Flocq.Core.Digits Flocq.Core.Float_prop Flocq.Calc.Bracket.

Section Fcalc_round.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Section Fcalc_round_fexp.

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Notation format := (generic_format beta fexp).

Theorem cexp_inbetween_float :
  forall x m e l,
  (0 < x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x \/ e <= fexp (Zdigits beta m + e))%Z ->
  cexp beta fexp x = fexp (Zdigits beta m + e).
Proof using valid_exp.
intros x m e l Px Bx He.
unfold cexp.
apply inbetween_float_bounds in Bx.
assert (0 <= m)%Z as Hm.
{
 apply Zlt_succ_le.
  eapply gt_0_F2R.
  apply Rlt_trans with (1 := Px).
  apply Bx.
}
destruct (Zle_lt_or_eq _ _ Hm) as [Hm'|<-].
  now erewrite <- mag_F2R_bounds_Zdigits with (1 := Hm').
clear Hm.
assert (mag beta x <= e)%Z as Hx.
{
 apply mag_le_bpow.
  now apply Rgt_not_eq.
  rewrite Rabs_pos_eq.
  now rewrite <- F2R_bpow.
  now apply Rlt_le.
}
simpl in He |- *.
clear Bx.
destruct He as [He|He].
-
 apply eq_sym, valid_exp with (2 := He).
  now apply Z.le_trans with e.
-
 apply valid_exp with (1 := He).
  now apply Z.le_trans with e.
Qed.

Theorem cexp_inbetween_float_loc_Exact :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x \/ l = loc_Exact <->
   e <= fexp (Zdigits beta m + e) \/ l = loc_Exact)%Z.
Proof using valid_exp.
intros x m e l Px Bx.
destruct Px as [Px|Px].
-
 split ; (intros [H|H] ; [left|now right]).
  rewrite <- cexp_inbetween_float with (1 := Px) (2 := Bx).
  exact H.
  now left.
  rewrite cexp_inbetween_float with (1 := Px) (2 := Bx).
  exact H.
  now right.
-
 assert (H := Bx).
  destruct Bx as [|c Bx _].
  now split ; right.
  rewrite <- Px in Bx.
  destruct Bx as [Bx1 Bx2].
  apply lt_0_F2R in Bx1.
  apply gt_0_F2R in Bx2.
  lia.
Qed.

Theorem inbetween_float_round :
  forall rnd choice,
  ( forall x m l, inbetween_int m x l -> rnd x = choice m l ) ->
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof using .
intros rnd choice Hc x m l e Hl.
unfold round, F2R.
simpl.
apply (f_equal (fun m => (IZR m * bpow e)%R)).
apply Hc.
apply inbetween_mult_reg with (bpow e).
apply bpow_gt_0.
now rewrite scaled_mantissa_mult_bpow.
Qed.

Definition cond_incr (b : bool) m := if b then (m + 1)%Z else m.

Lemma le_cond_incr_le :
  forall b m, (m <= cond_incr b m <= m + 1)%Z.
Proof using .
unfold cond_incr; intros b; case b; lia.
Qed.

Theorem inbetween_float_round_sign :
  forall rnd choice,
  ( forall x m l, inbetween_int m (Rabs x) l ->
    rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l) ) ->
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp rnd x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l)) e).
Proof using .
intros rnd choice Hc x m l e Hx.
apply (f_equal (fun m => (IZR m * bpow e)%R)).
simpl.
replace (Rlt_bool x 0) with (Rlt_bool (scaled_mantissa beta fexp x) 0).

apply Hc.
apply inbetween_mult_reg with (bpow e).
apply bpow_gt_0.
rewrite <- (Rabs_right (bpow e)) at 3.
rewrite <- Rabs_mult.
now rewrite scaled_mantissa_mult_bpow.
apply Rle_ge.
apply bpow_ge_0.

destruct (Rlt_bool_spec x 0) as [Zx|Zx] ; simpl.
apply Rlt_bool_true.
rewrite <- (Rmult_0_l (bpow (-e))).
apply Rmult_lt_compat_r with (2 := Zx).
apply bpow_gt_0.
apply Rlt_bool_false.
apply Rmult_le_pos with (1 := Zx).
apply bpow_ge_0.
Qed.

Theorem inbetween_int_DN :
  forall x m l,
  inbetween_int m x l ->
  Zfloor x = m.
Proof using .
intros x m l Hl.
refine (Zfloor_imp m _ _).
apply inbetween_bounds with (2 := Hl).
apply IZR_lt.
apply Zlt_succ.
Qed.

Theorem inbetween_float_DN :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Zfloor x = F2R (Float beta m e).
Proof using .
apply inbetween_float_round with (choice := fun m l => m).
exact inbetween_int_DN.
Qed.

Definition round_sign_DN s l :=
  match l with
  | loc_Exact => false
  | _ => s
  end.

Theorem inbetween_int_DN_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Zfloor x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_DN (Rlt_bool x 0) l) m).
Proof using .
intros x m l Hl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx] .

rewrite Rlt_bool_true with (1 := Zx).
inversion_clear Hl ; simpl.
rewrite <- (Ropp_involutive x).
rewrite H, <- opp_IZR.
apply Zfloor_IZR.
apply Zfloor_imp.
split.
apply Rlt_le.
rewrite opp_IZR.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
ring_simplify (- (m + 1) + 1)%Z.
rewrite opp_IZR.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.

rewrite Rlt_bool_false.
inversion_clear Hl ; simpl.
rewrite H.
apply Zfloor_IZR.
apply Zfloor_imp.
split.
now apply Rlt_le.
apply H.
now apply Rge_le.
Qed.

Theorem inbetween_float_DN_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Zfloor x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_DN (Rlt_bool x 0) l) m)) e).
Proof using .
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_sign_DN s l) m).
exact inbetween_int_DN_sign.
Qed.

Definition round_UP l :=
  match l with
  | loc_Exact => false
  | _ => true
  end.

Theorem inbetween_int_UP :
  forall x m l,
  inbetween_int m x l ->
  Zceil x = cond_incr (round_UP l) m.
Proof using .
intros x m l Hl.
assert (Hl': l = loc_Exact \/ (l <> loc_Exact /\ round_UP l = true)).
case l ; try (now left) ; now right ; split.
destruct Hl' as [Hl'|(Hl1, Hl2)].

rewrite Hl'.
destruct Hl ; try easy.
rewrite H.
exact (Zceil_IZR _).

rewrite Hl2.
simpl.
apply Zceil_imp.
ring_simplify (m + 1 - 1)%Z.
refine (let H := _ in conj (proj1 H) (Rlt_le _ _ (proj2 H))).
apply inbetween_bounds_not_Eq with (2 := Hl1) (1 := Hl).
Qed.

Theorem inbetween_float_UP :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Zceil x = F2R (Float beta (cond_incr (round_UP l) m) e).
Proof using .
apply inbetween_float_round with (choice := fun m l => cond_incr (round_UP l) m).
exact inbetween_int_UP.
Qed.

Definition round_sign_UP s l :=
  match l with
  | loc_Exact => false
  | _ => negb s
  end.

Theorem inbetween_int_UP_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Zceil x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_UP (Rlt_bool x 0) l) m).
Proof using .
intros x m l Hl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx] .

rewrite Rlt_bool_true with (1 := Zx).
simpl.
unfold Zceil.
apply f_equal.
inversion_clear Hl ; simpl.
rewrite H.
apply Zfloor_IZR.
apply Zfloor_imp.
split.
now apply Rlt_le.
apply H.

rewrite Rlt_bool_false.
simpl.
inversion_clear Hl ; simpl.
rewrite H.
apply Zceil_IZR.
apply Zceil_imp.
split.
change (m + 1 - 1)%Z with (Z.pred (Z.succ m)).
now rewrite <- Zpred_succ.
now apply Rlt_le.
now apply Rge_le.
Qed.

Theorem inbetween_float_UP_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Zceil x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_UP (Rlt_bool x 0) l) m)) e).
Proof using .
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_sign_UP s l) m).
exact inbetween_int_UP_sign.
Qed.

Definition round_ZR (s : bool) l :=
  match l with
  | loc_Exact => false
  | _ => s
  end.

Theorem inbetween_int_ZR :
  forall x m l,
  inbetween_int m x l ->
  Ztrunc x = cond_incr (round_ZR (Zlt_bool m 0) l) m.
Proof using .
Proof with auto with typeclass_instances.
intros x m l Hl.
inversion_clear Hl as [Hx|l' Hx Hl'].

rewrite Hx.
rewrite Zrnd_IZR...

unfold Ztrunc.
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
rewrite Zceil_floor_neq.
rewrite Hm.
unfold cond_incr.
simpl.
case Rlt_bool_spec ; intros Hx' ;
  case Zlt_bool_spec ; intros Hm' ; try apply refl_equal.
elim Rlt_not_le with (1 := Hx').
apply Rlt_le.
apply Rle_lt_trans with (2 := proj1 Hx).
now apply IZR_le.
elim Rle_not_lt with (1 := Hx').
apply Rlt_le_trans with (1 := proj2 Hx).
apply IZR_le.
now apply Zlt_le_succ.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

Theorem inbetween_float_ZR :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Ztrunc x = F2R (Float beta (cond_incr (round_ZR (Zlt_bool m 0) l) m) e).
Proof using .
apply inbetween_float_round with (choice := fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m).
exact inbetween_int_ZR.
Qed.

Theorem inbetween_int_ZR_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Ztrunc x = cond_Zopp (Rlt_bool x 0) m.
Proof using .
intros x m l Hl.
simpl.
unfold Ztrunc.
destruct (Rlt_le_dec x 0) as [Zx|Zx].

rewrite Rlt_bool_true with (1 := Zx).
simpl.
unfold Zceil.
apply f_equal.
apply Zfloor_imp.
rewrite <- Rabs_left with (1 := Zx).
apply inbetween_bounds with (2 := Hl).
apply IZR_lt.
apply Zlt_succ.

rewrite Rlt_bool_false with (1 := Zx).
simpl.
apply Zfloor_imp.
rewrite <- Rabs_pos_eq with (1 := Zx).
apply inbetween_bounds with (2 := Hl).
apply IZR_lt.
apply Zlt_succ.
Qed.

Theorem inbetween_float_ZR_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Ztrunc x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) m) e).
Proof using .
apply inbetween_float_round_sign with (choice := fun s m l => m).
exact inbetween_int_ZR_sign.
Qed.

Definition round_N (p : bool) l :=
  match l with
  | loc_Exact => false
  | loc_Inexact Lt => false
  | loc_Inexact Eq => p
  | loc_Inexact Gt => true
  end.

Theorem inbetween_int_N :
  forall choice x m l,
  inbetween_int m x l ->
  Znearest choice x = cond_incr (round_N (choice m) l) m.
Proof using .
Proof with auto with typeclass_instances.
intros choice x m l Hl.
inversion_clear Hl as [Hx|l' Hx Hl'].

rewrite Hx.
rewrite Zrnd_IZR...

unfold Znearest.
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (x - IZR m) (/2)) with l'.
now case l'.
rewrite <- Hl'.
rewrite plus_IZR.
rewrite <- (Rcompare_plus_r (- IZR m) x).
apply f_equal.
field.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

Theorem inbetween_int_N_sign :
  forall choice x m l,
  inbetween_int m (Rabs x) l ->
  Znearest choice x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (if Rlt_bool x 0 then negb (choice (-(m + 1))%Z) else choice m) l) m).
Proof using .
Proof with auto with typeclass_instances.
intros choice x m l Hl.
simpl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx].

rewrite Rlt_bool_true with (1 := Zx).
simpl.
rewrite <- (Ropp_involutive x).
rewrite Znearest_opp.
apply f_equal.
inversion_clear Hl as [Hx|l' Hx Hl'].
rewrite Hx.
apply Zrnd_IZR...
assert (Hm: Zfloor (-x) = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
unfold Znearest.
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (- x - IZR m) (/2)) with l'.
now case l'.
rewrite <- Hl'.
rewrite plus_IZR.
rewrite <- (Rcompare_plus_r (- IZR m) (-x)).
apply f_equal.
field.
rewrite Hm.
now apply Rlt_not_eq.

generalize (Rge_le _ _ Zx).
clear Zx.
intros Zx.
rewrite Rlt_bool_false with (1 := Zx).
simpl.
inversion_clear Hl as [Hx|l' Hx Hl'].
rewrite Hx.
apply Zrnd_IZR...
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
unfold Znearest.
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (x - IZR m) (/2)) with l'.
now case l'.
rewrite <- Hl'.
rewrite plus_IZR.
rewrite <- (Rcompare_plus_r (- IZR m) x).
apply f_equal.
field.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

Theorem inbetween_int_NE :
  forall x m l,
  inbetween_int m x l ->
  ZnearestE x = cond_incr (round_N (negb (Z.even m)) l) m.
Proof using .
intros x m l Hl.
now apply inbetween_int_N with (choice := fun x => negb (Z.even x)).
Qed.

Theorem inbetween_float_NE :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp ZnearestE x = F2R (Float beta (cond_incr (round_N (negb (Z.even m)) l) m) e).
Proof using .
apply inbetween_float_round with (choice := fun m l => cond_incr (round_N (negb (Z.even m)) l) m).
exact inbetween_int_NE.
Qed.

Theorem inbetween_int_NE_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  ZnearestE x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (negb (Z.even m)) l) m).
Proof using .
intros x m l Hl.
erewrite inbetween_int_N_sign with (choice := fun x => negb (Z.even x)).
2: eexact Hl.
apply f_equal.
case Rlt_bool.
rewrite Z.even_opp, Z.even_add.
now case (Z.even m).
apply refl_equal.
Qed.

Theorem inbetween_float_NE_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp ZnearestE x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (negb (Z.even m)) l) m)) e).
Proof using .
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_N (negb (Z.even m)) l) m).
exact inbetween_int_NE_sign.
Qed.

Theorem inbetween_int_NA :
  forall x m l,
  inbetween_int m x l ->
  ZnearestA x = cond_incr (round_N (Zle_bool 0 m) l) m.
Proof using .
intros x m l Hl.
now apply inbetween_int_N with (choice := fun x => Zle_bool 0 x).
Qed.

Theorem inbetween_float_NA :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp ZnearestA x = F2R (Float beta (cond_incr (round_N (Zle_bool 0 m) l) m) e).
Proof using .
apply inbetween_float_round with (choice := fun m l => cond_incr (round_N (Zle_bool 0 m) l) m).
exact inbetween_int_NA.
Qed.

Theorem inbetween_int_NA_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  ZnearestA x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N true l) m).
Proof using .
intros x m l Hl.
erewrite inbetween_int_N_sign with (choice := Zle_bool 0).
2: eexact Hl.
apply f_equal.
assert (Hm: (0 <= m)%Z).
apply Zlt_succ_le.
apply lt_IZR.
apply Rle_lt_trans with (Rabs x).
apply Rabs_pos.
refine (proj2 (inbetween_bounds _ _ _ _ _ Hl)).
apply IZR_lt.
apply Zlt_succ.
rewrite Zle_bool_true with (1 := Hm).
rewrite Zle_bool_false.
now case Rlt_bool.
lia.
Qed.

Theorem inbetween_float_NA_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp ZnearestA x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_N true l) m)) e).
Proof using .
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_N true l) m).
exact inbetween_int_NA_sign.
Qed.

Definition truncate_aux t k :=
  let '(m, e, l) := t in
  let p := Zpower beta k in
  (Z.div m p, (e + k)%Z, new_location p (Zmod m p) l).

Theorem truncate_aux_comp :
  forall t k1 k2,
  (0 < k1)%Z ->
  (0 < k2)%Z ->
  truncate_aux t (k1 + k2) = truncate_aux (truncate_aux t k1) k2.
Proof using .
intros ((m,e),l) k1 k2 Hk1 Hk2.
unfold truncate_aux.
destruct (inbetween_float_ex beta m e l) as (x,Hx).
assert (B1 := inbetween_float_new_location _ _ _ _ _ _ Hk1 Hx).
assert (Hk3: (0 < k1 + k2)%Z).
change Z0 with (0 + 0)%Z.
now apply Zplus_lt_compat.
assert (B3 := inbetween_float_new_location _ _ _ _ _ _ Hk3 Hx).
assert (B2 := inbetween_float_new_location _ _ _ _ _ _ Hk2 B1).
rewrite Zplus_assoc in B3.
destruct (inbetween_float_unique _ _ _ _ _ _ _ B2 B3).
now rewrite H, H0, Zplus_assoc.
Qed.

Definition truncate t :=
  let '(m, e, l) := t in
  let k := (fexp (Zdigits beta m + e) - e)%Z in
  if Zlt_bool 0 k then truncate_aux t k
  else t.

Theorem truncate_0 :
  forall e l,
  let '(m', e', l') := truncate (0, e, l)%Z in
  m' = Z0.
Proof using .
intros e l.
unfold truncate.
case Zlt_bool.
simpl.
apply Zdiv_0_l.
apply refl_equal.
Qed.

Theorem generic_format_truncate :
  forall m e l,
  (0 <= m)%Z ->
  let '(m', e', l') := truncate (m, e, l) in
  format (F2R (Float beta m' e')).
Proof using .
intros m e l Hm.
unfold truncate.
set (k := (fexp (Zdigits beta m + e) - e)%Z).
case Zlt_bool_spec ; intros Hk.

unfold truncate_aux.
apply generic_format_F2R.
intros Hd.
unfold cexp.
rewrite mag_F2R_Zdigits with (1 := Hd).
rewrite Zdigits_div_Zpower with (1 := Hm).
replace (Zdigits beta m - k + (e + k))%Z with (Zdigits beta m + e)%Z by ring.
unfold k.
ring_simplify.
apply Z.le_refl.
split.
now apply Zlt_le_weak.
apply Znot_gt_le.
contradict Hd.
apply Zdiv_small.
apply conj with (1 := Hm).
rewrite <- Z.abs_eq with (1 := Hm).
apply Zpower_gt_Zdigits.
apply Zlt_le_weak.
now apply Z.gt_lt.

destruct (Zle_lt_or_eq _ _ Hm) as [Hm'|Hm'].
apply generic_format_F2R.
unfold cexp.
rewrite mag_F2R_Zdigits.
2: now apply Zgt_not_eq.
unfold k in Hk.
clear -Hk.
lia.
rewrite <- Hm', F2R_0.
apply generic_format_0.
Qed.

Theorem truncate_correct_format :
  forall m e,
  m <> Z0 ->
  let x := F2R (Float beta m e) in
  generic_format beta fexp x ->
  (e <= fexp (Zdigits beta m + e))%Z ->
  let '(m', e', l') := truncate (m, e, loc_Exact) in
  x = F2R (Float beta m' e') /\ e' = cexp beta fexp x.
Proof using .
intros m e Hm x Fx He.
assert (Hc: cexp beta fexp x = fexp (Zdigits beta m + e)).
unfold cexp, x.
now rewrite mag_F2R_Zdigits.
unfold truncate.
rewrite <- Hc.
set (k := (cexp beta fexp x - e)%Z).
case Zlt_bool_spec ; intros Hk.

unfold truncate_aux.
rewrite Fx at 1.
assert (H: (e + k)%Z = cexp beta fexp x).
unfold k.
ring.
refine (conj _ H).
rewrite <- H.
apply F2R_eq.
replace (scaled_mantissa beta fexp x) with (IZR (Zfloor (scaled_mantissa beta fexp x))).
rewrite Ztrunc_IZR.
unfold scaled_mantissa.
rewrite <- H.
unfold x, F2R.
simpl.
rewrite Rmult_assoc, <- bpow_plus.
ring_simplify (e + - (e + k))%Z.
clear -Hm Hk.
destruct k as [|k|k] ; try easy.
simpl.
apply Zfloor_div.
intros H.
generalize (Zpower_pos_gt_0 beta k) (Zle_bool_imp_le _ _ (radix_prop beta)).
lia.
rewrite scaled_mantissa_generic with (1 := Fx).
now rewrite Zfloor_IZR.

split.
apply refl_equal.
unfold k in Hk.
lia.
Qed.

Theorem truncate_correct_partial' :
  forall x m e l,
  (0 < x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x)%Z ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\ e' = cexp beta fexp x.
Proof using valid_exp.
intros x m e l Hx H1 H2.
unfold truncate.
rewrite <- cexp_inbetween_float with (1 := Hx) (2 := H1) by now left.
generalize (Zlt_cases 0 (cexp beta fexp x - e)).
destruct Zlt_bool ; intros Hk.
-
 split.
  now apply inbetween_float_new_location.
  ring.
-
 apply (conj H1).
  lia.
Qed.

Theorem truncate_correct_partial :
  forall x m e l,
  (0 < x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\ e' = cexp beta fexp x.
Proof using valid_exp.
intros x m e l Hx H1 H2.
apply truncate_correct_partial' with (1 := Hx) (2 := H1).
rewrite cexp_inbetween_float with (1 := Hx) (2 := H1).
exact H2.
now right.
Qed.

Theorem truncate_correct' :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x)%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = cexp beta fexp x \/ (l' = loc_Exact /\ format x)).
Proof using valid_exp.
intros x m e l [Hx|Hx] H1 H2.
-
 destruct (Zle_or_lt e (fexp (Zdigits beta m + e))) as [H3|H3].
  +
 generalize (truncate_correct_partial x m e l Hx H1 H3).
    destruct (truncate (m, e, l)) as [[m' e'] l'].
    intros [H4 H5].
    apply (conj H4).
    now left.
  +
 destruct H2 as [H2|H2].
      generalize (truncate_correct_partial' x m e l Hx H1 H2).
      destruct (truncate (m, e, l)) as [[m' e'] l'].
      intros [H4 H5].
      apply (conj H4).
      now left.
    rewrite H2 in H1 |- *.
    simpl.
    generalize (Zlt_cases 0 (fexp (Zdigits beta m + e) - e)).
    destruct Zlt_bool.
      intros H.
      apply False_ind.
      lia.
    intros _.
    apply (conj H1).
    right.
    repeat split.
    inversion_clear H1.
    rewrite H.
    apply generic_format_F2R.
    intros Zm.
    unfold cexp.
    rewrite mag_F2R_Zdigits with (1 := Zm).
    now apply Zlt_le_weak.
-
 assert (Hm: m = 0%Z).
  cut (m <= 0 < m + 1)%Z.
lia.
  assert (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R as Hx'.
    apply inbetween_float_bounds with (1 := H1).
    rewrite <- Hx in Hx'.
    split.
    apply le_0_F2R with (1 := proj1 Hx').
    apply gt_0_F2R with (1 := proj2 Hx').
  rewrite Hm, <- Hx in H1 |- *.
  clear -H1.
  destruct H1 as [_ | l' [H _] _].
  +
 assert (exists e', truncate (Z0, e, loc_Exact) = (Z0, e', loc_Exact)).
      unfold truncate, truncate_aux.
      case Zlt_bool.
        rewrite Zdiv_0_l, Zmod_0_l.
        eexists.
        apply f_equal.
        unfold new_location.
        now case Z.even.
      now eexists.
    destruct H as [e' H].
    rewrite H.
    split.
      constructor.
      apply eq_sym, F2R_0.
      right.
      repeat split.
      apply generic_format_0.
  +
 rewrite F2R_0 in H.
    elim Rlt_irrefl with (1 := H).
Qed.

Theorem truncate_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = cexp beta fexp x \/ (l' = loc_Exact /\ format x)).
Proof using valid_exp.
intros x m e l Hx H1 H2.
apply truncate_correct' with (1 := Hx) (2 := H1).
now apply cexp_inbetween_float_loc_Exact with (2 := H1).
Qed.

Section round_dir.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Variable choice : Z -> location -> Z.
Hypothesis inbetween_int_valid :
  forall x m l,
  inbetween_int m x l ->
  rnd x = choice m l.

Theorem round_any_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e = cexp beta fexp x \/ (l = loc_Exact /\ format x)) ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof using inbetween_int_valid valid_rnd.
Proof with auto with typeclass_instances.
intros x m e l Hin [He|(Hl,Hf)].
rewrite He in Hin |- *.
apply inbetween_float_round with (2 := Hin).
exact inbetween_int_valid.
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl.
replace (choice m loc_Exact) with m.
rewrite <- H.
apply round_generic...
rewrite <- (Zrnd_IZR rnd m) at 1.
apply inbetween_int_valid.
now constructor.
Qed.

Theorem round_trunc_any_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (choice m' l') e').
Proof using inbetween_int_valid valid_exp valid_rnd.
intros x m e l Hx Hl He.
generalize (truncate_correct x m e l Hx Hl He).
destruct (truncate (m, e, l)) as ((m', e'), l').
intros (H1, H2).
now apply round_any_correct.
Qed.

Theorem round_trunc_any_correct' :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x)%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (choice m' l') e').
Proof using inbetween_int_valid valid_exp valid_rnd.
intros x m e l Hx Hl He.
generalize (truncate_correct' x m e l Hx Hl He).
destruct (truncate (m, e, l)) as [[m' e'] l'].
intros [H1 H2].
now apply round_any_correct.
Qed.

End round_dir.

Section round_dir_sign.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Variable choice : bool -> Z -> location -> Z.
Hypothesis inbetween_int_valid :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l).

Theorem round_sign_any_correct :
  forall x m e l,
  inbetween_float beta m e (Rabs x) l ->
  (e = cexp beta fexp x \/ (l = loc_Exact /\ format x)) ->
  round beta fexp rnd x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l)) e).
Proof using inbetween_int_valid valid_rnd.
Proof with auto with typeclass_instances.
intros x m e l Hin [He|(Hl,Hf)].
rewrite He in Hin |- *.
apply inbetween_float_round_sign with (2 := Hin).
exact inbetween_int_valid.
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl.
replace (choice (Rlt_bool x 0) m loc_Exact) with m.

unfold Rabs in H.
destruct (Rcase_abs x) as [Zx|Zx].
rewrite Rlt_bool_true with (1 := Zx).
simpl.
rewrite F2R_Zopp.
rewrite <- H, Ropp_involutive.
apply round_generic...
rewrite Rlt_bool_false.
simpl.
rewrite <- H.
now apply round_generic.
now apply Rge_le.

destruct (Rlt_bool_spec x 0) as [Zx|Zx].

apply Z.opp_inj.
change (- m = cond_Zopp true (choice true m loc_Exact))%Z.
rewrite <- (Zrnd_IZR rnd (-m)) at 1.
assert (IZR (-m) < 0)%R.
rewrite opp_IZR.
apply Ropp_lt_gt_0_contravar.
apply IZR_lt.
apply gt_0_F2R with beta e.
rewrite <- H.
apply Rabs_pos_lt.
now apply Rlt_not_eq.
rewrite <- Rlt_bool_true with (1 := H0).
apply inbetween_int_valid.
constructor.
rewrite Rabs_left with (1 := H0).
rewrite opp_IZR.
apply Ropp_involutive.

change (m = cond_Zopp false (choice false m loc_Exact))%Z.
rewrite <- (Zrnd_IZR rnd m) at 1.
assert (0 <= IZR m)%R.
apply IZR_le.
apply ge_0_F2R with beta e.
rewrite <- H.
apply Rabs_pos.
rewrite <- Rlt_bool_false with (1 := H0).
apply inbetween_int_valid.
constructor.
now apply Rabs_pos_eq.
Qed.

Theorem round_trunc_sign_any_correct' :
  forall x m e l,
  inbetween_float beta m e (Rabs x) l ->
  (e <= cexp beta fexp x)%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m' l')) e').
Proof using inbetween_int_valid valid_exp valid_rnd.
intros x m e l Hl He.
rewrite <- cexp_abs in He.
generalize (truncate_correct' (Rabs x) m e l (Rabs_pos _) Hl He).
destruct (truncate (m, e, l)) as [[m' e'] l'].
intros [H1 H2].
apply round_sign_any_correct.
exact H1.
destruct H2 as [H2|[H2 H3]].
left.
now rewrite <- cexp_abs.
right.
apply (conj H2).
now apply generic_format_abs_inv.
Qed.

Theorem round_trunc_sign_any_correct :
  forall x m e l,
  inbetween_float beta m e (Rabs x) l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m' l')) e').
Proof using inbetween_int_valid valid_exp valid_rnd.
intros x m e l Hl He.
apply round_trunc_sign_any_correct' with (1 := Hl).
rewrite <- cexp_abs.
apply cexp_inbetween_float_loc_Exact with (2 := Hl) (3 := He).
apply Rabs_pos.
Qed.

End round_dir_sign.

Definition round_DN_correct :=
  round_any_correct _ (fun m _ => m) inbetween_int_DN.

Definition round_trunc_DN_correct :=
  round_trunc_any_correct _ (fun m _ => m) inbetween_int_DN.

Definition round_trunc_DN_correct' :=
  round_trunc_any_correct' _ (fun m _ => m) inbetween_int_DN.

Definition round_sign_DN_correct :=
  round_sign_any_correct _ (fun s m l => cond_incr (round_sign_DN s l) m) inbetween_int_DN_sign.

Definition round_trunc_sign_DN_correct :=
  round_trunc_sign_any_correct _ (fun s m l => cond_incr (round_sign_DN s l) m) inbetween_int_DN_sign.

Definition round_trunc_sign_DN_correct' :=
  round_trunc_sign_any_correct' _ (fun s m l => cond_incr (round_sign_DN s l) m) inbetween_int_DN_sign.

Definition round_UP_correct :=
  round_any_correct _ (fun m l => cond_incr (round_UP l) m) inbetween_int_UP.

Definition round_trunc_UP_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_UP l) m) inbetween_int_UP.

Definition round_trunc_UP_correct' :=
  round_trunc_any_correct' _ (fun m l => cond_incr (round_UP l) m) inbetween_int_UP.

Definition round_sign_UP_correct :=
  round_sign_any_correct _ (fun s m l => cond_incr (round_sign_UP s l) m) inbetween_int_UP_sign.

Definition round_trunc_sign_UP_correct :=
  round_trunc_sign_any_correct _ (fun s m l => cond_incr (round_sign_UP s l) m) inbetween_int_UP_sign.

Definition round_trunc_sign_UP_correct' :=
  round_trunc_sign_any_correct' _ (fun s m l => cond_incr (round_sign_UP s l) m) inbetween_int_UP_sign.

Definition round_ZR_correct :=
  round_any_correct _ (fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m) inbetween_int_ZR.

Definition round_trunc_ZR_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m) inbetween_int_ZR.

Definition round_trunc_ZR_correct' :=
  round_trunc_any_correct' _ (fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m) inbetween_int_ZR.

Definition round_sign_ZR_correct :=
  round_sign_any_correct _ (fun s m l => m) inbetween_int_ZR_sign.

Definition round_trunc_sign_ZR_correct :=
  round_trunc_sign_any_correct _ (fun s m l => m) inbetween_int_ZR_sign.

Definition round_trunc_sign_ZR_correct' :=
  round_trunc_sign_any_correct' _ (fun s m l => m) inbetween_int_ZR_sign.

Definition round_NE_correct :=
  round_any_correct _ (fun m l => cond_incr (round_N (negb (Z.even m)) l) m) inbetween_int_NE.

Definition round_trunc_NE_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_N (negb (Z.even m)) l) m) inbetween_int_NE.

Definition round_trunc_NE_correct' :=
  round_trunc_any_correct' _ (fun m l => cond_incr (round_N (negb (Z.even m)) l) m) inbetween_int_NE.

Definition round_sign_NE_correct :=
  round_sign_any_correct _ (fun s m l => cond_incr (round_N (negb (Z.even m)) l) m) inbetween_int_NE_sign.

Definition round_trunc_sign_NE_correct :=
  round_trunc_sign_any_correct _ (fun s m l => cond_incr (round_N (negb (Z.even m)) l) m) inbetween_int_NE_sign.

Definition round_trunc_sign_NE_correct' :=
  round_trunc_sign_any_correct' _ (fun s m l => cond_incr (round_N (negb (Z.even m)) l) m) inbetween_int_NE_sign.

Definition round_NA_correct :=
  round_any_correct _ (fun m l => cond_incr (round_N (Zle_bool 0 m) l) m) inbetween_int_NA.

Definition round_trunc_NA_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_N (Zle_bool 0 m) l) m) inbetween_int_NA.

Definition round_trunc_NA_correct' :=
  round_trunc_any_correct' _ (fun m l => cond_incr (round_N (Zle_bool 0 m) l) m) inbetween_int_NA.

Definition round_sign_NA_correct :=
  round_sign_any_correct _ (fun s m l => cond_incr (round_N true l) m) inbetween_int_NA_sign.

Definition round_trunc_sign_NA_correct :=
  round_trunc_sign_any_correct _ (fun s m l => cond_incr (round_N true l) m) inbetween_int_NA_sign.

Definition round_trunc_sign_NA_correct' :=
  round_trunc_sign_any_correct' _ (fun s m l => cond_incr (round_N true l) m) inbetween_int_NA_sign.

End Fcalc_round_fexp.

Variable emin : Z.

Definition truncate_FIX t :=
  let '(m, e, l) := t in
  let k := (emin - e)%Z in
  if Zlt_bool 0 k then
    let p := Zpower beta k in
    (Z.div m p, (e + k)%Z, new_location p (Zmod m p) l)
  else t.

Theorem truncate_FIX_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e <= emin)%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate_FIX (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = cexp beta (FIX_exp emin) x \/ (l' = loc_Exact /\ generic_format beta (FIX_exp emin) x)).
Proof using .
intros x m e l H1 H2.
unfold truncate_FIX.
set (k := (emin - e)%Z).
set (p := Zpower beta k).
unfold cexp, FIX_exp.
generalize (Zlt_cases 0 k).
case (Zlt_bool 0 k) ; intros Hk.

split.
now apply inbetween_float_new_location.
clear H2.
left.
unfold k.
ring.

split.
exact H1.
unfold k in Hk.
destruct H2 as [H2|H2].
left.
lia.
right.
split.
exact H2.
rewrite H2 in H1.
inversion_clear H1.
rewrite H.
apply generic_format_F2R.
unfold cexp.
lia.
Qed.

End Fcalc_round.

End Round.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Round.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Core Flocq.Calc.Bracket Flocq.Calc.Operations Flocq.Calc.Round.

Section Plus.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Context { monotone_exp : Monotone_exp fexp }.

Definition Fplus_core m1 e1 m2 e2 e :=
  let k := (e - e2)%Z in
  let '(m2', _, l) :=
    if Zlt_bool 0 k then truncate_aux beta (m2, e2, loc_Exact) k
    else (m2 * Zpower beta (-k), e, loc_Exact)%Z in
  let m1' := (m1 * Zpower beta (e1 - e))%Z in
  (m1' + m2', l)%Z.

Theorem Fplus_core_correct :
  forall m1 e1 m2 e2 e,
  (e <= e1)%Z ->
  let '(m, l) := Fplus_core m1 e1 m2 e2 e in
  inbetween_float beta m e (F2R (Float beta m1 e1) + F2R (Float beta m2 e2)) l.
Proof using .
intros m1 e1 m2 e2 e He1.
unfold Fplus_core.
case Zlt_bool_spec ; intros He2.
-
 unfold truncate_aux.
  unfold inbetween_float, F2R.
simpl.
  rewrite 3!plus_IZR.
  rewrite Rplus_assoc.
  rewrite 2!Rmult_plus_distr_r.
  replace (IZR (m1 * Zpower beta (e1 - e)) * bpow e)%R with (IZR m1 * bpow e1)%R.
  2: {
    rewrite mult_IZR, IZR_Zpower by lia.
    rewrite Rmult_assoc, <- bpow_plus.
    apply (f_equal (fun v => IZR m1 * bpow v)%R).
    ring.
  }
  rewrite <- 3!(Rplus_comm _ (IZR m1 * bpow e1)).
  apply inbetween_plus_compat.
  set (k := (e - e2)%Z).
  rewrite <- (plus_IZR _ 1).
  replace e with (e2 + k)%Z by (unfold k ; ring).
  apply inbetween_float_new_location.
  exact He2.
  now constructor 1.
-
 constructor 1.
  unfold F2R.
simpl.
  rewrite plus_IZR, Rmult_plus_distr_r.
  rewrite 2!mult_IZR, 2!IZR_Zpower by lia.
  rewrite 2!Rmult_assoc, <- 2!bpow_plus.
  apply (f_equal2 (fun v w => IZR m1 * bpow v + IZR m2 * bpow w)%R) ; ring.
Qed.

Definition Fplus (f1 f2 : float beta) :=
  let (m1, e1) := f1 in
  let (m2, e2) := f2 in
  if Zeq_bool m1 0 then
    (m2, e2, loc_Exact)
  else if Zeq_bool m2 0 then
    (m1, e1, loc_Exact)
  else
  let p1 := (Zdigits beta m1 + e1)%Z in
  let p2 := (Zdigits beta m2 + e2)%Z in
  if Zle_bool 2 (Z.abs (p1 - p2)) then
    let e := Z.min (Z.max e1 e2) (fexp (Z.max p1 p2 - 1)) in
    let (m, l) :=
      if Zlt_bool e1 e then
        Fplus_core m2 e2 m1 e1 e
      else
        Fplus_core m1 e1 m2 e2 e in
    (m, e, l)
  else
    let (m, e) := Fplus f1 f2 in
    (m, e, loc_Exact).

Theorem Fplus_correct :
  forall x y,
  let '(m, e, l) := Fplus x y in
  (l = loc_Exact \/ e <= cexp beta fexp (F2R x + F2R y))%Z /\
  inbetween_float beta m e (F2R x + F2R y) l.
Proof using monotone_exp.
intros [m1 e1] [m2 e2].
unfold Fplus.
case Zeq_bool_spec ; intros Hm1.
{
 rewrite Hm1.
  split.
  now left.
  rewrite F2R_0, Rplus_0_l.
  now constructor 1.
}
case Zeq_bool_spec ; intros Hm2.
{
 rewrite Hm2.
  split.
  now left.
  rewrite F2R_0, Rplus_0_r.
  now constructor 1.
}
set (p1 := (Zdigits beta m1 + e1)%Z).
set (p2 := (Zdigits beta m2 + e2)%Z).
set (e := Z.min (Z.max e1 e2) (fexp (Z.max p1 p2 - 1))).
case Zle_bool_spec ; intros Hp ; cycle 1.
{
 rewrite <- F2R_plus.
  destruct Operations.Fplus as [m' e'].
  split.
  now left.
  now constructor 1.
}
set (z := (F2R _ + F2R _)%R).
assert (Hz: (e <= cexp beta fexp z)%Z).
{
 apply Z.le_trans with (fexp (Z.max p1 p2 - 1)).
  apply Z.le_min_r.
  unfold cexp.
  apply monotone_exp.
  unfold z.
  revert Hp.
  unfold p1, p2.
  rewrite <- 2!mag_F2R_Zdigits by easy.
  clear -Hm1 Hm2.
  destruct (Zle_or_lt (mag beta (F2R (Float beta m1 e1))) (mag beta (F2R (Float beta m2 e2)))) as [Hp'|Hp'].
  -
 rewrite Z.max_r by easy.
    rewrite Z.abs_neq by (clear -Hp'; lia).
    rewrite Rplus_comm.
    intros H.
    apply mag_plus_ge.
    now apply F2R_neq_0.
    clear -H ; lia.
  -
 rewrite Z.max_l, Z.abs_eq by (clear -Hp'; lia).
    intros H.
    apply mag_plus_ge.
    now apply F2R_neq_0.
    clear -H ; lia.
}
case Zlt_bool_spec ; intros He.
-
 assert (He': (e <= e2)%Z) by (clear -He ; lia).
  generalize (Fplus_core_correct m2 e2 m1 e1 e He').
  rewrite Rplus_comm.
  fold z.
  destruct Fplus_core as [m' l].
  refine (fun H => conj _ H).
  now right.
-
 assert (He': (e <= e1)%Z) by (clear -He ; lia).
  generalize (Fplus_core_correct m1 e1 m2 e2 e He').
  fold z.
  destruct Fplus_core as [m' l].
  refine (fun H => conj _ H).
  now right.
Qed.

End Plus.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Calc_DOT_Sqrt.
Module Export Flocq.
Module Export Calc.
Module Export Sqrt.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Digits Flocq.Core.Generic_fmt Flocq.Core.Float_prop Flocq.Calc.Bracket.

Set Implicit Arguments.
Set Strongly Strict Implicit.

Section Fcalc_sqrt.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Lemma mag_sqrt_F2R :
  forall m1 e1,
  (0 < m1)%Z ->
  mag beta (sqrt (F2R (Float beta m1 e1))) = Z.div2 (Zdigits beta m1 + e1 + 1) :> Z.
Proof using .
intros m1 e1 Hm1.
rewrite <- (mag_F2R_Zdigits beta m1 e1) by now apply Zgt_not_eq.
apply mag_sqrt.
now apply F2R_gt_0.
Qed.

Definition Fsqrt_core m1 e1 e :=
  let d1 := Zdigits beta m1 in
  let m1' := (m1 * Zpower beta (e1 - 2 * e))%Z in
  let (q, r) := Z.sqrtrem m1' in
  let l :=
    if Zeq_bool r 0 then loc_Exact
    else loc_Inexact (if Zle_bool r q then Lt else Gt) in
  (q, l).

Theorem Fsqrt_core_correct :
  forall m1 e1 e,
  (0 < m1)%Z ->
  (2 * e <= e1)%Z ->
  let '(m, l) := Fsqrt_core m1 e1 e in
  inbetween_float beta m e (sqrt (F2R (Float beta m1 e1))) l.
Proof using .
intros m1 e1 e Hm1 He.
unfold Fsqrt_core.
set (m' := Zmult _ _).
assert (0 <= m')%Z as Hm'.
{
 apply Z.mul_nonneg_nonneg.
  now apply Zlt_le_weak.
  apply Zpower_ge_0.
}
assert (sqrt (F2R (Float beta m1 e1)) = sqrt (IZR m') * bpow e)%R as Hf.
{
 rewrite <- (sqrt_Rsqr (bpow e)) by apply bpow_ge_0.
  rewrite <- sqrt_mult.
  unfold Rsqr, m'.
  rewrite mult_IZR, IZR_Zpower by lia.
  rewrite Rmult_assoc, <- 2!bpow_plus.
  now replace (_ + _)%Z with e1 by ring.
  now apply IZR_le.
  apply Rle_0_sqr.
}
generalize (Z.sqrtrem_spec m' Hm').
destruct Z.sqrtrem as [q r].
intros [Hq Hr].
rewrite Hf.
unfold inbetween_float, F2R.
simpl Fnum.
apply inbetween_mult_compat.
apply bpow_gt_0.
rewrite Hq.
case Zeq_bool_spec ; intros Hr'.

rewrite Hr', Zplus_0_r, mult_IZR.
fold (Rsqr (IZR q)).
rewrite sqrt_Rsqr.
now constructor.
apply IZR_le.
clear -Hr ; lia.

constructor.
split.

apply Rle_lt_trans with (sqrt (IZR (q * q))).
rewrite mult_IZR.
fold (Rsqr (IZR q)).
rewrite sqrt_Rsqr.
apply Rle_refl.
apply IZR_le.
clear -Hr ; lia.
apply sqrt_lt_1.
rewrite mult_IZR.
apply Rle_0_sqr.
rewrite <- Hq.
now apply IZR_le.
apply IZR_lt.
lia.
apply Rlt_le_trans with (sqrt (IZR ((q + 1) * (q + 1)))).
apply sqrt_lt_1.
rewrite <- Hq.
now apply IZR_le.
rewrite mult_IZR.
apply Rle_0_sqr.
apply IZR_lt.
ring_simplify.
lia.
rewrite mult_IZR.
fold (Rsqr (IZR (q + 1))).
rewrite sqrt_Rsqr.
apply Rle_refl.
apply IZR_le.
clear -Hr ; lia.

rewrite Rcompare_half_r.
generalize (Rcompare_sqr (2 * sqrt (IZR (q * q + r))) (IZR q + IZR (q + 1))).
rewrite 2!Rabs_pos_eq.
intros <-.
replace ((2 * sqrt (IZR (q * q + r))) * (2 * sqrt (IZR (q * q + r))))%R
  with (4 * Rsqr (sqrt (IZR (q * q + r))))%R by (unfold Rsqr ; ring).
rewrite Rsqr_sqrt.
rewrite <- plus_IZR, <- 2!mult_IZR.
rewrite Rcompare_IZR.
replace ((q + (q + 1)) * (q + (q + 1)))%Z with (4 * (q * q) + 4 * q + 1)%Z by ring.
generalize (Zle_cases r q).
case (Zle_bool r q) ; intros Hr''.
change (4 * (q * q + r) < 4 * (q * q) + 4 * q + 1)%Z.
lia.
change (4 * (q * q + r) > 4 * (q * q) + 4 * q + 1)%Z.
lia.
rewrite <- Hq.
now apply IZR_le.
rewrite <- plus_IZR.
apply IZR_le.
clear -Hr ; lia.
apply Rmult_le_pos.
now apply IZR_le.
apply sqrt_ge_0.
Qed.

Definition Fsqrt (x : float beta) :=
  let (m1, e1) := x in
  let e' := (Zdigits beta m1 + e1 + 1)%Z in
  let e := Z.min (fexp (Z.div2 e')) (Z.div2 e1) in
  let '(m, l) := Fsqrt_core m1 e1 e in
  (m, e, l).

Theorem Fsqrt_correct :
  forall x,
  (0 < F2R x)%R ->
  let '(m, e, l) := Fsqrt x in
  (e <= cexp beta fexp (sqrt (F2R x)))%Z /\
  inbetween_float beta m e (sqrt (F2R x)) l.
Proof using .
intros [m1 e1] Hm1.
apply gt_0_F2R in Hm1.
unfold Fsqrt.
set (e := Z.min _ _).
assert (2 * e <= e1)%Z as He.
{
 assert (e <= Z.div2 e1)%Z by apply Z.le_min_r.
  rewrite (Zdiv2_odd_eqn e1).
  destruct Z.odd ; lia.
}
generalize (Fsqrt_core_correct m1 e1 e Hm1 He).
destruct Fsqrt_core as [m l].
apply conj.
apply Z.le_trans with (1 := Z.le_min_l _ _).
unfold cexp.
rewrite (mag_sqrt_F2R m1 e1 Hm1).
apply Z.le_refl.
Qed.

End Fcalc_sqrt.

End Sqrt.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Sqrt.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Core_DOT_FTZ.
Module Export Flocq.
Module Export Core.
Module Export FTZ.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Float_prop Flocq.Core.Ulp Flocq.Core.FLX.

Section RND_FTZ.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable emin prec : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Inductive FTZ_format (x : R) : Prop :=
  FTZ_spec (f : float beta) :
    x = F2R f ->
    (x <> 0%R -> Zpower beta (prec - 1) <= Z.abs (Fnum f) < Zpower beta prec)%Z ->
    (emin <= Fexp f)%Z ->
    FTZ_format x.

Definition FTZ_exp e := if Zlt_bool (e - prec) emin then (emin + prec - 1)%Z else (e - prec)%Z.

Global Instance FTZ_exp_valid : Valid_exp FTZ_exp.
Proof using prec_gt_0_.
intros k.
unfold FTZ_exp.
generalize (Zlt_cases (k - prec) emin).
case (Zlt_bool (k - prec) emin) ; intros H1.
split ; intros H2.
lia.
split.
generalize (Zlt_cases (emin + prec + 1 - prec) emin).
case (Zlt_bool (emin + prec + 1 - prec) emin) ; intros H3.
lia.
generalize (Zlt_cases (emin + prec - 1 + 1 - prec) emin).
generalize (prec_gt_0 prec).
case (Zlt_bool (emin + prec - 1 + 1 - prec) emin) ; lia.
intros l H3.
generalize (Zlt_cases (l - prec) emin).
case (Zlt_bool (l - prec) emin) ; lia.
split ; intros H2.
generalize (Zlt_cases (k + 1 - prec) emin).
case (Zlt_bool (k + 1 - prec) emin) ; lia.
generalize (prec_gt_0 prec).
split ; intros ; lia.
Qed.

Theorem FLXN_format_FTZ :
  forall x, FTZ_format x -> FLXN_format beta prec x.
Proof using .
intros x [[xm xe] Hx1 Hx2 Hx3].
eexists.
exact Hx1.
exact Hx2.
Qed.

Theorem generic_format_FTZ :
  forall x, FTZ_format x -> generic_format beta FTZ_exp x.
Proof using .
intros x Hx.
cut (generic_format beta (FLX_exp prec) x).
apply generic_inclusion_mag.
intros Zx.
destruct Hx as [[xm xe] Hx1 Hx2 Hx3].
simpl in Hx2, Hx3.
specialize (Hx2 Zx).
assert (Zxm: xm <> Z0).
contradict Zx.
rewrite Hx1, Zx.
apply F2R_0.
unfold FTZ_exp, FLX_exp.
rewrite Zlt_bool_false.
apply Z.le_refl.
rewrite Hx1, mag_F2R with (1 := Zxm).
cut (prec - 1 < mag beta (IZR xm))%Z.
clear -Hx3 ; lia.
apply mag_gt_Zpower with (1 := Zxm).
apply Hx2.
apply generic_format_FLXN.
now apply FLXN_format_FTZ.
Qed.

Theorem FTZ_format_generic :
  forall x, generic_format beta FTZ_exp x -> FTZ_format x.
Proof using prec_gt_0_.
intros x Hx.
destruct (Req_dec x 0) as [->|Hx3].
exists (Float beta 0 emin).
apply sym_eq, F2R_0.
intros H.
now elim H.
apply Z.le_refl.
unfold generic_format, scaled_mantissa, cexp, FTZ_exp in Hx.
destruct (mag beta x) as (ex, Hx4).
simpl in Hx.
specialize (Hx4 Hx3).
generalize (Zlt_cases (ex - prec) emin) Hx.
clear Hx.
case (Zlt_bool (ex - prec) emin) ; intros Hx5 Hx2.
elim Rlt_not_ge with (1 := proj2 Hx4).
apply Rle_ge.
rewrite Hx2, <- F2R_Zabs.
rewrite <- (Rmult_1_l (bpow ex)).
unfold F2R.
simpl.
apply Rmult_le_compat.
now apply IZR_le.
apply bpow_ge_0.
apply IZR_le.
apply (Zlt_le_succ 0).
apply lt_IZR.
apply Rmult_lt_reg_r with (bpow (emin + prec - 1)).
apply bpow_gt_0.
rewrite Rmult_0_l.
change (0 < F2R (Float beta (Z.abs (Ztrunc (x * bpow (- (emin + prec - 1))))) (emin + prec - 1)))%R.
rewrite F2R_Zabs, <- Hx2.
now apply Rabs_pos_lt.
apply bpow_le.
lia.
rewrite Hx2.
eexists ; repeat split ; simpl.
apply le_IZR.
rewrite IZR_Zpower.
apply Rmult_le_reg_r with (bpow (ex - prec)).
apply bpow_gt_0.
rewrite <- bpow_plus.
replace (prec - 1 + (ex - prec))%Z with (ex - 1)%Z by ring.
change (bpow (ex - 1) <= F2R (Float beta (Z.abs (Ztrunc (x * bpow (- (ex - prec))))) (ex - prec)))%R.
rewrite F2R_Zabs, <- Hx2.
apply Hx4.
apply Zle_minus_le_0.
now apply (Zlt_le_succ 0).
apply lt_IZR.
rewrite IZR_Zpower.
apply Rmult_lt_reg_r with (bpow (ex - prec)).
apply bpow_gt_0.
rewrite <- bpow_plus.
replace (prec + (ex - prec))%Z with ex by ring.
change (F2R (Float beta (Z.abs (Ztrunc (x * bpow (- (ex - prec))))) (ex - prec)) < bpow ex)%R.
rewrite F2R_Zabs, <- Hx2.
apply Hx4.
now apply Zlt_le_weak.
now apply Z.ge_le.
Qed.

Theorem FTZ_format_satisfies_any :
  satisfies_any FTZ_format.
Proof using prec_gt_0_.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FTZ_exp)).
intros x.
split.
apply FTZ_format_generic.
apply generic_format_FTZ.
Qed.

Theorem FTZ_format_FLXN :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  FLXN_format beta prec x -> FTZ_format x.
Proof using prec_gt_0_.
intros x Hx Fx.
apply FTZ_format_generic.
apply generic_format_FLXN in Fx.
revert Hx Fx.
apply generic_inclusion_ge.
intros e He.
unfold FTZ_exp.
rewrite Zlt_bool_false.
apply Z.le_refl.
lia.
Qed.

Theorem ulp_FTZ_0 :
  ulp beta FTZ_exp 0 = bpow (emin+prec-1).
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
unfold ulp; rewrite Req_bool_true; trivial.
case (negligible_exp_spec FTZ_exp).
intros T; specialize (T (emin-1)%Z); contradict T.
apply Zle_not_lt; unfold FTZ_exp; unfold Prec_gt_0 in prec_gt_0_.
rewrite Zlt_bool_true; lia.
assert (V:(FTZ_exp (emin+prec-1) = emin+prec-1)%Z).
unfold FTZ_exp; rewrite Zlt_bool_true; lia.
intros n H2; rewrite <-V.
apply f_equal, fexp_negligible_exp_eq...
lia.
Qed.

Section FTZ_round.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Definition Zrnd_FTZ x :=
  if Rle_bool 1 (Rabs x) then rnd x else Z0.

Global Instance valid_rnd_FTZ : Valid_rnd Zrnd_FTZ.
Proof using valid_rnd.
Proof with auto with typeclass_instances.
split.

intros x y Hxy.
unfold Zrnd_FTZ.
case Rle_bool_spec ; intros Hx ;
  case Rle_bool_spec ; intros Hy.
4: easy.

now apply Zrnd_le.
rewrite <- (Zrnd_IZR rnd 0).
apply Zrnd_le...
apply Rle_trans with (-1)%R.
2: now apply IZR_le.
destruct (Rabs_ge_inv _ _ Hx) as [Hx1|Hx1].
exact Hx1.
elim Rle_not_lt with (1 := Hx1).
apply Rle_lt_trans with (2 := Hy).
apply Rle_trans with (1 := Hxy).
apply RRle_abs.

rewrite <- (Zrnd_IZR rnd 0).
apply Zrnd_le...
apply Rle_trans with 1%R.
now apply IZR_le.
destruct (Rabs_ge_inv _ _ Hy) as [Hy1|Hy1].
elim Rle_not_lt with (1 := Hy1).
apply Rlt_le_trans with (2 := Hxy).
apply (Rabs_def2 _ _ Hx).
exact Hy1.

intros n.
unfold Zrnd_FTZ.
rewrite Zrnd_IZR...
case Rle_bool_spec.
easy.
rewrite <- abs_IZR.
intros H.
generalize (lt_IZR _ 1 H).
clear.
now case n ; trivial ; simpl ; intros [p|p|].
Qed.

Theorem round_FTZ_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FTZ_exp Zrnd_FTZ x = round beta (FLX_exp prec) rnd x.
Proof using prec_gt_0_.
intros x Hx.
unfold round, scaled_mantissa, cexp.
destruct (mag beta x) as (ex, He).
simpl.
assert (Hx0: x <> 0%R).
intros Hx0.
apply Rle_not_lt with (1 := Hx).
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
specialize (He Hx0).
assert (He': (emin + prec <= ex)%Z).
apply (bpow_lt_bpow beta).
apply Rle_lt_trans with (1 := Hx).
apply He.
replace (FTZ_exp ex) with (FLX_exp prec ex).
unfold Zrnd_FTZ.
rewrite Rle_bool_true.
apply refl_equal.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow (- FLX_exp prec ex))).
change 1%R with (bpow 0).
rewrite <- (Zplus_opp_r (FLX_exp prec ex)).
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (2 := proj1 He).
apply bpow_le.
unfold FLX_exp.
generalize (prec_gt_0 prec).
clear -He' ; lia.
apply bpow_ge_0.
unfold FLX_exp, FTZ_exp.
rewrite Zlt_bool_false.
apply refl_equal.
clear -He' ; lia.
Qed.

Theorem round_FTZ_small :
  forall x : R,
  (Rabs x < bpow (emin + prec - 1))%R ->
  round beta FTZ_exp Zrnd_FTZ x = 0%R.
Proof using valid_rnd.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0.
apply round_0...
unfold round, scaled_mantissa, cexp.
destruct (mag beta x) as (ex, He).
simpl.
specialize (He Hx0).
unfold Zrnd_FTZ.
rewrite Rle_bool_false.
apply F2R_0.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow (- FTZ_exp ex))).
change 1%R with (bpow 0).
rewrite <- (Zplus_opp_r (FTZ_exp ex)).
rewrite bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Rlt_le_trans with (1 := Hx).
apply bpow_le.
unfold FTZ_exp.
generalize (Zlt_cases (ex - prec) emin).
case Zlt_bool.
intros _.
apply Z.le_refl.
intros He'.
elim Rlt_not_le with (1 := Hx).
apply Rle_trans with (2 := proj1 He).
apply bpow_le.
lia.
apply bpow_ge_0.
Qed.

End FTZ_round.

End RND_FTZ.

End FTZ.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_FTZ.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_Prop_DOT_Relative.
Module Export Flocq.
Module Export AVOID_RESERVED_Prop.
Module Export Relative.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Core.

Section Fprop_relative.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Section Fprop_relative_generic.

Variable fexp : Z -> Z.
Context { prop_exp : Valid_exp fexp }.

Section relative_error_conversion.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma relative_error_lt_conversion :
  forall x b, (0 < b)%R ->
  (x <> 0 -> Rabs (round beta fexp rnd x - x) < b * Rabs x)%R ->
  exists eps,
  (Rabs eps < b)%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof using valid_rnd.
Proof with auto with typeclass_instances.
intros x b Hb0 Hxb.
destruct (Req_dec x 0) as [Hx0|Hx0].

exists 0%R.
split.
now rewrite Rabs_R0.
rewrite Hx0, Rmult_0_l.
apply round_0...

specialize (Hxb Hx0).
exists ((round beta fexp rnd x - x) / x)%R.
split.
2: now field.
unfold Rdiv.
rewrite Rabs_mult.
apply Rmult_lt_reg_r with (Rabs x).
now apply Rabs_pos_lt.
rewrite Rmult_assoc, <- Rabs_mult.
rewrite Rinv_l with (1 := Hx0).
now rewrite Rabs_R1, Rmult_1_r.
Qed.

Lemma relative_error_le_conversion :
  forall x b, (0 <= b)%R ->
  (Rabs (round beta fexp rnd x - x) <= b * Rabs x)%R ->
  exists eps,
  (Rabs eps <= b)%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof using valid_rnd.
Proof with auto with typeclass_instances.
intros x b Hb0 Hxb.
destruct (Req_dec x 0) as [Hx0|Hx0].

exists 0%R.
split.
now rewrite Rabs_R0.
rewrite Hx0, Rmult_0_l.
apply round_0...

exists ((round beta fexp rnd x - x) / x)%R.
split.
2: now field.
unfold Rdiv.
rewrite Rabs_mult.
apply Rmult_le_reg_r with (Rabs x).
now apply Rabs_pos_lt.
rewrite Rmult_assoc, <- Rabs_mult.
rewrite Rinv_l with (1 := Hx0).
now rewrite Rabs_R1, Rmult_1_r.
Qed.

Lemma relative_error_le_conversion_inv :
  forall x b,
  (exists eps,
   (Rabs eps <= b)%R /\ round beta fexp rnd x = (x * (1 + eps))%R) ->
  (Rabs (round beta fexp rnd x - x) <= b * Rabs x)%R.
Proof using .
Proof with auto with typeclass_instances.
intros x b (eps, (Beps, Heps)).
assert (Pb : (0 <= b)%R); [now revert Beps; apply Rle_trans, Rabs_pos|].
rewrite Heps; replace (_ - _)%R with (eps * x)%R; [|ring].
now rewrite Rabs_mult; apply Rmult_le_compat_r; [apply Rabs_pos|].
Qed.

Lemma relative_error_le_conversion_round_inv :
  forall x b,
  (exists eps,
   (Rabs eps <= b)%R /\ x = (round beta fexp rnd x * (1 + eps))%R) ->
  (Rabs (round beta fexp rnd x - x) <= b * Rabs (round beta fexp rnd x))%R.
Proof using .
Proof with auto with typeclass_instances.
intros x b.
set (rx := round _ _ _ _).
intros (eps, (Beps, Heps)).
assert (Pb : (0 <= b)%R); [now revert Beps; apply Rle_trans, Rabs_pos|].
rewrite Heps; replace (_ - _)%R with (- (eps * rx))%R; [|ring].
now rewrite Rabs_Ropp, Rabs_mult; apply Rmult_le_compat_r; [apply Rabs_pos|].
Qed.

End relative_error_conversion.

Variable emin p : Z.
Hypothesis Hmin : forall k, (emin < k)%Z -> (p <= k - fexp k)%Z.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem relative_error :
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs x)%R.
Proof using Hmin prop_exp valid_rnd.
Proof with auto with typeclass_instances.
intros x Hx.
assert (Hx': (x <> 0)%R).
intros T; contradict Hx; rewrite T, Rabs_R0.
apply Rlt_not_le, bpow_gt_0.
apply Rlt_le_trans with (ulp beta fexp x)%R.
now apply error_lt_ulp...
rewrite ulp_neq_0; trivial.
unfold cexp.
destruct (mag beta x) as (ex, He).
simpl.
specialize (He Hx').
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_plus.
apply bpow_le.
assert (emin < ex)%Z.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
generalize (Hmin ex).
lia.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

Theorem relative_error_ex :
  forall x,
  (bpow emin <= Rabs x)%R ->
  exists eps,
  (Rabs eps < bpow (-p + 1))%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof using Hmin prop_exp valid_rnd.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_lt_conversion...
apply bpow_gt_0.
intros _.
now apply relative_error.
Qed.

Theorem relative_error_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs x)%R.
Proof using Hmin prop_exp valid_rnd.
intros m x Hx.
apply relative_error.
unfold x.
rewrite <- F2R_Zabs.
apply bpow_le_F2R.
apply lt_F2R with beta emin.
rewrite F2R_0, F2R_Zabs.
now apply Rabs_pos_lt.
Qed.

Theorem relative_error_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps < bpow (-p + 1))%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof using Hmin prop_exp valid_rnd.
Proof with auto with typeclass_instances.
intros m x.
apply relative_error_lt_conversion...
apply bpow_gt_0.
now apply relative_error_F2R_emin.
Qed.

Theorem relative_error_round :
  (0 < p)%Z ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs (round beta fexp rnd x))%R.
Proof using Hmin prop_exp valid_rnd.
Proof with auto with typeclass_instances.
intros Hp x Hx.
assert (Hx': (x <> 0)%R).
intros T; contradict Hx; rewrite T, Rabs_R0.
apply Rlt_not_le, bpow_gt_0.
apply Rlt_le_trans with (ulp beta fexp x)%R.
now apply error_lt_ulp.
rewrite ulp_neq_0; trivial.
unfold cexp.
destruct (mag beta x) as (ex, He).
simpl.
specialize (He Hx').
assert (He': (emin < ex)%Z).
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_plus.
apply bpow_le.
generalize (Hmin ex).
lia.
apply Rmult_le_compat_l.
apply bpow_ge_0.
generalize He.
apply round_abs_abs...
clear rnd valid_rnd x Hx Hx' He.
intros rnd valid_rnd x _ Hx.
rewrite <- (round_generic beta fexp rnd (bpow (ex - 1))).
now apply round_le.
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
generalize (Hmin ex).
lia.
Qed.

Theorem relative_error_round_F2R_emin :
  (0 < p)%Z ->
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs (round beta fexp rnd x))%R.
Proof using Hmin prop_exp valid_rnd.
intros Hp m x Hx.
apply relative_error_round.
exact Hp.
unfold x.
rewrite <- F2R_Zabs.
apply bpow_le_F2R.
apply lt_F2R with beta emin.
rewrite F2R_0, F2R_Zabs.
now apply Rabs_pos_lt.
Qed.

Variable choice : Z -> bool.

Theorem relative_error_N :
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs x)%R.
Proof using Hmin prop_exp.
intros x Hx.
apply Rle_trans with (/2 * ulp beta fexp x)%R.
now apply error_le_half_ulp.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
assert (Hx': (x <> 0)%R).
intros H.
apply Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
rewrite ulp_neq_0; trivial.
unfold cexp.
destruct (mag beta x) as (ex, He).
simpl.
specialize (He Hx').
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_plus.
apply bpow_le.
assert (emin < ex)%Z.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
generalize (Hmin ex).
lia.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

Theorem relative_error_N_ex :
  forall x,
  (bpow emin <= Rabs x)%R ->
  exists eps,
  (Rabs eps <= /2 * bpow (-p + 1))%R /\ round beta fexp (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hmin prop_exp.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_le_conversion...
apply Rlt_le.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply bpow_gt_0.
now apply relative_error_N.
Qed.

Theorem relative_error_N_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs x)%R.
Proof using Hmin prop_exp.
Proof with auto with typeclass_instances.
intros m x.
destruct (Req_dec x 0) as [Hx|Hx].

rewrite Hx, round_0...
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.

apply relative_error_N.
unfold x.
rewrite <- F2R_Zabs.
apply bpow_le_F2R.
apply lt_F2R with beta emin.
rewrite F2R_0, F2R_Zabs.
now apply Rabs_pos_lt.
Qed.

Theorem relative_error_N_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps <= /2 * bpow (-p + 1))%R /\ round beta fexp (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hmin prop_exp.
Proof with auto with typeclass_instances.
intros m x.
apply relative_error_le_conversion...
apply Rlt_le.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply bpow_gt_0.
now apply relative_error_N_F2R_emin.
Qed.

Theorem relative_error_N_round :
  (0 < p)%Z ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs (round beta fexp (Znearest choice) x))%R.
Proof using Hmin prop_exp.
Proof with auto with typeclass_instances.
intros Hp x Hx.
apply Rle_trans with (/2 * ulp beta fexp x)%R.
now apply error_le_half_ulp.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
assert (Hx': (x <> 0)%R).
intros H.
apply Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
rewrite ulp_neq_0; trivial.
unfold cexp.
destruct (mag beta x) as (ex, He).
simpl.
specialize (He Hx').
assert (He': (emin < ex)%Z).
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_plus.
apply bpow_le.
generalize (Hmin ex).
lia.
apply Rmult_le_compat_l.
apply bpow_ge_0.
generalize He.
apply round_abs_abs...
clear rnd valid_rnd x Hx Hx' He.
intros rnd valid_rnd x _ Hx.
rewrite <- (round_generic beta fexp rnd (bpow (ex - 1))).
now apply round_le.
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
generalize (Hmin ex).
lia.
Qed.

Theorem relative_error_N_round_F2R_emin :
  (0 < p)%Z ->
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs (round beta fexp (Znearest choice) x))%R.
Proof using Hmin prop_exp.
Proof with auto with typeclass_instances.
intros Hp m x.
destruct (Req_dec x 0) as [Hx|Hx].

rewrite Hx, round_0...
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.

apply relative_error_N_round with (1 := Hp).
unfold x.
rewrite <- F2R_Zabs.
apply bpow_le_F2R.
apply lt_F2R with beta emin.
rewrite F2R_0, F2R_Zabs.
now apply Rabs_pos_lt.
Qed.

End Fprop_relative_generic.

Section Fprop_relative_FLX.

Variable prec : Z.
Variable Hp : Z.lt 0 prec.

Lemma relative_error_FLX_aux :
  forall k, (prec <= k - FLX_exp prec k)%Z.
Proof using .
intros k.
unfold FLX_exp.
lia.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem relative_error_FLX :
  forall x,
  (x <> 0)%R ->
  (Rabs (round beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof using Hp valid_rnd.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (mag beta x) as (ex, He).
specialize (He Hx).
apply relative_error with (ex - 1)%Z...
intros k _.
apply relative_error_FLX_aux.
apply He.
Qed.

Theorem relative_error_FLX_ex :
  forall x,
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLX_exp prec) rnd x = (x * (1 + eps))%R.
Proof using Hp valid_rnd.
Proof with auto with typeclass_instances.
intros x.
apply relative_error_lt_conversion...
apply bpow_gt_0.
now apply relative_error_FLX.
Qed.

Theorem relative_error_FLX_round :
  forall x,
  (x <> 0)%R ->
  (Rabs (round beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs (round beta (FLX_exp prec) rnd x))%R.
Proof using Hp valid_rnd.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (mag beta x) as (ex, He).
specialize (He Hx).
apply relative_error_round with (ex - 1)%Z...
intros k _.
apply relative_error_FLX_aux.
apply He.
Qed.

Variable choice : Z -> bool.

Theorem relative_error_N_FLX :
  forall x,
  (Rabs (round beta (FLX_exp prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros x.
destruct (Req_dec x 0) as [Hx|Hx].

rewrite Hx, round_0...
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.

destruct (mag beta x) as (ex, He).
specialize (He Hx).
apply relative_error_N with (ex - 1)%Z...
intros k _.
apply relative_error_FLX_aux.
apply He.
Qed.

Definition u_ro := (/2 * bpow (-prec + 1))%R.

Lemma u_ro_pos : (0 <= u_ro)%R.
Proof using .
apply Rmult_le_pos; [lra|apply bpow_ge_0].
Qed.

Lemma u_ro_lt_1 : (u_ro < 1)%R.
Proof using Hp.
unfold u_ro; apply (Rmult_lt_reg_l 2); [lra|].
rewrite <-Rmult_assoc, Rinv_r, Rmult_1_l, Rmult_1_r; [|lra].
apply (Rle_lt_trans _ (bpow 0));
  [apply bpow_le; lia|simpl; lra].
Qed.

Lemma u_rod1pu_ro_pos : (0 <= u_ro / (1 + u_ro))%R.
Proof using .
apply Rmult_le_pos; [|apply Rlt_le, Rinv_0_lt_compat];
assert (H := u_ro_pos); lra.
Qed.

Lemma u_rod1pu_ro_le_u_ro : (u_ro / (1 + u_ro) <= u_ro)%R.
Proof using .
assert (Pu_ro := u_ro_pos).
apply (Rmult_le_reg_r (1 + u_ro)); [lra|].
unfold Rdiv; rewrite Rmult_assoc, Rinv_l; [|lra].
assert (0 <= u_ro * u_ro)%R; [apply Rmult_le_pos|]; lra.
Qed.

Theorem relative_error_N_FLX' :
  forall x,
  (Rabs (round beta (FLX_exp prec) (Znearest choice) x - x)
   <= u_ro / (1 + u_ro) * Rabs x)%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intro x.
assert (Pu_ro : (0 <= u_ro)%R).
{
 apply Rmult_le_pos; [lra|apply bpow_ge_0].
}
destruct (Req_dec x 0) as [Zx|Nzx].
{
 rewrite Zx, Rabs_R0, Rmult_0_r, round_0...
  now unfold Rminus; rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0; right.
}
set (ufpx := bpow (mag beta x - 1)%Z).
set (rx := round _ _ _ _).
assert (Pufpx : (0 <= ufpx)%R); [now apply bpow_ge_0|].
assert (H_2_1 : (Rabs (rx - x) <= u_ro * ufpx)%R).
{
 refine (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _) _);
    [now apply FLX_exp_valid|right].
  unfold ulp, cexp, FLX_exp, u_ro, ufpx; rewrite (Req_bool_false _ _ Nzx).
  rewrite Rmult_assoc, <-bpow_plus; do 2 f_equal; ring.
}
assert (H_2_3 : (ufpx + Rabs (rx - x) <= Rabs x)%R).
{
 apply (Rplus_le_reg_r (- ufpx)); ring_simplify.
  destruct (Rle_or_lt 0 x) as [Sx|Sx].
  {
 apply (Rle_trans _ (Rabs (ufpx - x))).
    {
 apply round_N_pt; [now apply FLX_exp_valid|].
      apply generic_format_bpow; unfold FLX_exp; lia.
}
    rewrite Rabs_minus_sym, Rabs_pos_eq.
    {
 now rewrite Rabs_pos_eq; [right; ring|].
}
    apply (Rplus_le_reg_r ufpx); ring_simplify.
    now rewrite <-(Rabs_pos_eq _ Sx); apply bpow_mag_le.
}
  apply (Rle_trans _ (Rabs (- ufpx - x))).
  {
 apply round_N_pt; [now apply FLX_exp_valid|].
    apply generic_format_opp, generic_format_bpow; unfold FLX_exp; lia.
}
  rewrite Rabs_pos_eq; [now rewrite Rabs_left; [right|]|].
  apply (Rplus_le_reg_r x); ring_simplify.
  rewrite <-(Ropp_involutive x); apply Ropp_le_contravar; unfold ufpx.
  rewrite <-mag_opp, <-Rabs_pos_eq; [apply bpow_mag_le|]; lra.
}
assert (H : (Rabs ((rx - x) / x) <= u_ro / (1 + u_ro))%R).
{
 assert (H : (0 < ufpx + Rabs (rx - x))%R).
  {
 apply Rplus_lt_le_0_compat; [apply bpow_gt_0|apply Rabs_pos].
}
  apply (Rle_trans _ (Rabs (rx - x) / (ufpx + Rabs (rx - x)))).
  {
 unfold Rdiv; rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos|].
    now rewrite (Rabs_Rinv _ Nzx); apply Rinv_le.
}
  apply (Rmult_le_reg_r ((ufpx + Rabs (rx - x)) * (1 + u_ro))).
  {
 apply Rmult_lt_0_compat; lra.
}
  field_simplify; [try unfold Rdiv; rewrite ?Rinv_1, ?Rmult_1_r| |]; lra.
}
revert H; unfold Rdiv; rewrite Rabs_mult, (Rabs_Rinv _ Nzx); intro H.
apply (Rmult_le_reg_r (/ Rabs x)); [now apply Rinv_0_lt_compat, Rabs_pos_lt|].
now apply (Rle_trans _ _ _ H); right; field; split; [apply Rabs_no_R0|lra].
Qed.

Theorem relative_error_N_FLX_ex :
  forall x,
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLX_exp prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros x.
apply relative_error_le_conversion...
apply Rlt_le.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply bpow_gt_0.
now apply relative_error_N_FLX.
Qed.

Theorem relative_error_N_FLX'_ex :
  forall x,
  exists eps,
  (Rabs eps <= u_ro / (1 + u_ro))%R /\
  round beta (FLX_exp prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros x.
apply relative_error_le_conversion...
{
 apply u_rod1pu_ro_pos.
}
now apply relative_error_N_FLX'.
Qed.

Lemma relative_error_N_round_ex_derive :
  forall x rx,
  (exists eps, (Rabs eps <= u_ro / (1 + u_ro))%R /\ rx = (x * (1 + eps))%R) ->
  exists eps, (Rabs eps <= u_ro)%R /\ x = (rx * (1 + eps))%R.
Proof using Hp.
intros x rx (d, (Bd, Hd)).
assert (Pu_ro := u_ro_pos).
assert (H := Rabs_le_inv _ _ Bd).
assert (H' := u_rod1pu_ro_le_u_ro); assert (H'' := u_ro_lt_1).
destruct (Req_dec rx 0) as [Zfx|Nzfx].
{
 exists 0%R; split; [now rewrite Rabs_R0|].
  rewrite Rplus_0_r, Rmult_1_r, Zfx.
  now rewrite Zfx in Hd; destruct (Rmult_integral _ _ (sym_eq Hd)); [|lra].
}
destruct (Req_dec x 0) as [Zx|Nzx].
{
 now exfalso; revert Hd; rewrite Zx, Rmult_0_l.
}
set (d' := ((x - rx) / rx)%R).
assert (Hd' : (Rabs d' <= u_ro)%R).
{
 unfold d'; rewrite Hd.
  replace (_ / _)%R with (- d / (1 + d))%R; [|now field; split; lra].
  unfold Rdiv; rewrite Rabs_mult, Rabs_Ropp.
  rewrite (Rabs_pos_eq (/ _)); [|apply Rlt_le, Rinv_0_lt_compat; lra].
  apply (Rmult_le_reg_r (1 + d)); [lra|].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [|lra].
  apply (Rle_trans _ _ _ Bd).
  unfold Rdiv; apply Rmult_le_compat_l; [now apply u_ro_pos|].
  apply (Rle_trans _ (1 - u_ro / (1 + u_ro))); [right; field|]; lra.
}
now exists d'; split; [|unfold d'; field].
Qed.

Theorem relative_error_N_FLX_round_ex :
  forall x,
  exists eps,
  (Rabs eps <= u_ro)%R /\
  x = (round beta (FLX_exp prec) (Znearest choice) x * (1 + eps))%R.
Proof using Hp.
intro x; apply relative_error_N_round_ex_derive, relative_error_N_FLX'_ex.
Qed.

Theorem relative_error_N_FLX_round :
  forall x,
  (Rabs (round beta (FLX_exp prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs(round beta (FLX_exp prec) (Znearest choice) x))%R.
Proof using Hp.
intro x.
apply relative_error_le_conversion_round_inv, relative_error_N_FLX_round_ex.
Qed.

End Fprop_relative_FLX.

Section Fprop_relative_FLT.

Variable emin prec : Z.
Variable Hp : Z.lt 0 prec.

Lemma relative_error_FLT_aux :
  forall k, (emin + prec - 1 < k)%Z -> (prec <= k - FLT_exp emin prec k)%Z.
Proof using .
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
lia.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem relative_error_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof using Hp valid_rnd.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error with (emin + prec - 1)%Z...
apply relative_error_FLT_aux.
Qed.

Theorem relative_error_FLT_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof using Hp valid_rnd.
Proof with auto with typeclass_instances.
intros m x Zx.
destruct (Rlt_or_le (Rabs x) (bpow (emin + prec - 1))) as [Hx|Hx].
rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_lt_0_compat.
apply bpow_gt_0.
now apply Rabs_pos_lt.
apply generic_format_FLT_FIX...
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx).
apply bpow_le.
apply Zle_pred.
apply generic_format_FIX.
now exists (Float beta m emin).
now apply relative_error_FLT.
Qed.

Theorem relative_error_FLT_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) rnd x = (x * (1 + eps))%R.
Proof using Hp valid_rnd.
Proof with auto with typeclass_instances.
intros m x.
apply relative_error_lt_conversion...
apply bpow_gt_0.
now apply relative_error_FLT_F2R_emin.
Qed.

Theorem relative_error_FLT_ex :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) rnd x = (x * (1 + eps))%R.
Proof using Hp valid_rnd.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_lt_conversion...
apply bpow_gt_0.
intros _; now apply relative_error_FLT.
Qed.

Variable choice : Z -> bool.

Theorem relative_error_N_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_N with (emin + prec - 1)%Z...
apply relative_error_FLT_aux.
Qed.

Theorem relative_error_N_FLT_ex :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_le_conversion...
apply Rlt_le.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply bpow_gt_0.
now apply relative_error_N_FLT.
Qed.

Theorem relative_error_N_FLT_round :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (round beta (FLT_exp emin prec) (Znearest choice) x))%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_N_round with (emin + prec - 1)%Z...
apply relative_error_FLT_aux.
Qed.

Theorem relative_error_N_FLT_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros m x.
destruct (Rlt_or_le (Rabs x) (bpow (emin + prec - 1))) as [Hx|Hx].
rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
apply Rmult_le_pos.
apply Rlt_le.
apply (RinvN_pos 1).
apply bpow_ge_0.
apply Rabs_pos.
apply generic_format_FLT_FIX...
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx).
apply bpow_le.
apply Zle_pred.
apply generic_format_FIX.
now exists (Float beta m emin).
now apply relative_error_N_FLT.
Qed.

Theorem relative_error_N_FLT_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros m x.
apply relative_error_le_conversion...
apply Rmult_le_pos.
apply Rlt_le.
apply (RinvN_pos 1).
apply bpow_ge_0.
now apply relative_error_N_FLT_F2R_emin.
Qed.

Theorem relative_error_N_FLT_round_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (round beta (FLT_exp emin prec) (Znearest choice) x))%R.
Proof using Hp.
Proof with auto with typeclass_instances.
intros m x.
destruct (Rlt_or_le (Rabs x) (bpow (emin + prec - 1))) as [Hx|Hx].
rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
apply Rmult_le_pos.
apply Rlt_le.
apply (RinvN_pos 1).
apply bpow_ge_0.
apply Rabs_pos.
apply generic_format_FLT_FIX...
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx).
apply bpow_le.
apply Zle_pred.
apply generic_format_FIX.
now exists (Float beta m emin).
apply relative_error_N_round with (emin := (emin + prec - 1)%Z)...
apply relative_error_FLT_aux.
Qed.

Lemma error_N_FLT_aux :
  forall x,
  (0 < x)%R ->
  exists eps, exists  eta,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\
  (Rabs eta <= /2 * bpow (emin))%R      /\
  (eps*eta=0)%R /\
  round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps) + eta)%R.
Proof using Hp.
intros x Hx2.
case (Rle_or_lt (bpow (emin+prec)) x); intros Hx.

destruct relative_error_N_ex with (FLT_exp emin prec) (emin+prec)%Z prec choice x
  as (eps,(Heps1,Heps2)).
now apply FLT_exp_valid.
intros; unfold FLT_exp.
lia.
rewrite Rabs_right;[assumption|apply Rle_ge; now left].
exists eps; exists 0%R.
split;[assumption|split].
rewrite Rabs_R0; apply Rmult_le_pos.
apply Rlt_le, pos_half_prf.
apply bpow_ge_0.
split;[apply Rmult_0_r|idtac].
now rewrite Rplus_0_r.

exists 0%R; exists (round beta (FLT_exp emin prec) (Znearest choice) x - x)%R.
split.
rewrite Rabs_R0; apply Rmult_le_pos.
apply Rlt_le, pos_half_prf.
apply bpow_ge_0.
split.
apply Rle_trans with (/2*ulp beta (FLT_exp emin prec) x)%R.
apply error_le_half_ulp.
now apply FLT_exp_valid.
apply Rmult_le_compat_l.
apply Rlt_le, pos_half_prf.
rewrite ulp_neq_0.
2: now apply Rgt_not_eq.
apply bpow_le.
unfold FLT_exp, cexp.
rewrite Zmax_right.
lia.
destruct (mag beta x) as (e,He); simpl.
assert (e-1 < emin+prec)%Z.
apply (lt_bpow beta).
apply Rle_lt_trans with (2:=Hx).
rewrite <- (Rabs_pos_eq x) by now apply Rlt_le.
now apply He, Rgt_not_eq.
lia.
split ; ring.
Qed.

Theorem relative_error_N_FLT'_ex :
  forall x,
  exists eps eta : R,
  (Rabs eps <= u_ro prec / (1 + u_ro prec))%R /\
  (Rabs eta <= /2 * bpow emin)%R /\
  (eps * eta = 0)%R /\
  round beta (FLT_exp emin prec) (Znearest choice) x
  = (x * (1 + eps) + eta)%R.
Proof using Hp.
intro x.
set (rx := round _ _ _ x).
assert (Pb := u_rod1pu_ro_pos prec).
destruct (Rle_or_lt (bpow (emin + prec - 1)) (Rabs x)) as [MX|Mx].
{
 destruct (relative_error_N_FLX'_ex prec Hp choice x) as (d, (Bd, Hd)).
  exists d, 0%R; split; [exact Bd|]; split.
  {
 rewrite Rabs_R0; apply Rmult_le_pos; [lra|apply bpow_ge_0].
}
  rewrite Rplus_0_r, Rmult_0_r; split; [reflexivity|].
  now rewrite <- Hd; apply round_FLT_FLX.
}
assert (H : (Rabs (rx - x) <= /2 * bpow emin)%R).
{
 refine (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _) _);
    [now apply FLT_exp_valid|].
  rewrite ulp_FLT_small; [now right|now simpl|].
  apply (Rlt_le_trans _ _ _ Mx), bpow_le; lia.
}
exists 0%R, (rx - x)%R; split; [now rewrite Rabs_R0|]; split; [exact H|].
now rewrite Rmult_0_l, Rplus_0_r, Rmult_1_r; split; [|ring].
Qed.

Theorem relative_error_N_FLT'_ex_separate :
  forall x,
  exists x' : R,
  round beta (FLT_exp emin prec) (Znearest choice) x'
  = round beta (FLT_exp emin prec) (Znearest choice) x /\
  (exists eta, Rabs eta <= /2 * bpow emin /\ x' = x + eta)%R /\
  (exists eps, Rabs eps <= u_ro prec / (1 + u_ro prec) /\
               round beta (FLT_exp emin prec) (Znearest choice) x'
               = x' * (1 + eps))%R.
Proof using Hp.
intro x.
set (rx := round _ _ _ x).
destruct (relative_error_N_FLT'_ex x) as (d, (e, (Bd, (Be, (Hde0, Hde))))).
destruct (Rlt_or_le (Rabs (d * x)) (Rabs e)) as [HdxLte|HeLedx].
{
 exists rx; split; [|split].
  {
 apply round_generic; [now apply valid_rnd_N|].
    now apply generic_format_round; [apply FLT_exp_valid|apply valid_rnd_N].
}
  {
 exists e; split; [exact Be|].
    unfold rx; rewrite Hde; destruct (Rmult_integral _ _ Hde0) as [Zd|Ze].
    {
 now rewrite Zd, Rplus_0_r, Rmult_1_r.
}
    exfalso; revert HdxLte; rewrite Ze, Rabs_R0; apply Rle_not_lt, Rabs_pos.
}
  exists 0%R; split; [now rewrite Rabs_R0; apply u_rod1pu_ro_pos|].
  rewrite Rplus_0_r, Rmult_1_r; apply round_generic; [now apply valid_rnd_N|].
  now apply generic_format_round; [apply FLT_exp_valid|apply valid_rnd_N].
}
exists x; split; [now simpl|split].
{
 exists 0%R; split;
    [rewrite Rabs_R0; apply Rmult_le_pos; [lra|apply bpow_ge_0]|ring].
}
exists d; rewrite Hde; destruct (Rmult_integral _ _ Hde0) as [Zd|Ze].
{
 split; [exact Bd|].
  assert (Ze : e = 0%R); [|now rewrite Ze, Rplus_0_r].
  apply Rabs_eq_R0, Rle_antisym; [|now apply Rabs_pos].
  now revert HeLedx; rewrite Zd, Rmult_0_l, Rabs_R0.
}
now rewrite Ze, Rplus_0_r.
Qed.

End Fprop_relative_FLT.

Theorem error_N_FLT :
  forall (emin prec : Z), (0 < prec)%Z ->
  forall (choice : Z -> bool),
  forall (x : R),
  exists eps eta : R,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\
  (Rabs eta <= /2 * bpow emin)%R /\
  (eps * eta = 0)%R /\
  (round beta (FLT_exp emin prec) (Znearest choice) x
   = x * (1 + eps) + eta)%R.
Proof using .
intros emin prec Pprec choice x.
destruct (Rtotal_order x 0) as [Nx|[Zx|Px]].
{
 assert (Pmx : (0 < - x)%R).
  {
 now rewrite <- Ropp_0; apply Ropp_lt_contravar.
}
  destruct (@error_N_FLT_aux emin prec Pprec
                             (fun t : Z => negb (choice (- (t + 1))%Z))
                             (- x)%R Pmx)
    as (d,(e,(Hd,(He,(Hde,Hr))))).
  exists d; exists (- e)%R; split; [exact Hd|split; [|split]].
  {
 now rewrite Rabs_Ropp.
}
  {
 now rewrite Ropp_mult_distr_r_reverse, <- Ropp_0; apply f_equal.
}
  rewrite <- (Ropp_involutive x), round_N_opp.
  now rewrite Ropp_mult_distr_l_reverse, <- Ropp_plus_distr; apply f_equal.
}
{
 assert (Ph2 : (0 <= / 2)%R).
  {
 apply (Rmult_le_reg_l 2 _ _ Rlt_0_2).
    rewrite Rmult_0_r, Rinv_r; [exact Rle_0_1|].
    apply Rgt_not_eq, Rlt_gt, Rlt_0_2.
}
  exists 0%R; exists 0%R; rewrite Zx; split; [|split; [|split]].
  {
 now rewrite Rabs_R0; apply Rmult_le_pos; [|apply bpow_ge_0].
}
  {
 now rewrite Rabs_R0; apply Rmult_le_pos; [|apply bpow_ge_0].
}
  {
 now rewrite Rmult_0_l.
}
  now rewrite Rmult_0_l, Rplus_0_l, round_0; [|apply valid_rnd_N].
}
now apply error_N_FLT_aux.
Qed.

End Fprop_relative.

End Relative.

End AVOID_RESERVED_Prop.

End Flocq.

End Flocq_DOT_Prop_DOT_Relative.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.Reals.Reals.
Require Stdlib.ZArith.ZArith.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Lia.
Require Stdlib.micromega.Psatz.

Module Export Flocq_DOT_IEEE754_DOT_BinarySingleNaN.
Module Export Flocq.
Module Export IEEE754.
Module Export BinarySingleNaN.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz Stdlib.Floats.SpecFloat.
Import Flocq.Core.Core Flocq.Calc.Round Flocq.Calc.Bracket Flocq.Calc.Operations Flocq.Calc.Div Flocq.Calc.Sqrt Flocq_DOT_Prop_DOT_Relative.Flocq.AVOID_RESERVED_Prop.Relative.

Definition SF2R beta x :=
  match x with
  | S754_finite s m e => F2R (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

Class Prec_lt_emax prec emax := prec_lt_emax : (prec < emax)%Z.
Arguments prec_lt_emax prec emax {Prec_lt_emax}.

Section Binary.

Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Context (prec_lt_emax_ : Prec_lt_emax prec emax).

Notation emin := (emin prec emax).
Notation fexp := (fexp prec emax).
Instance fexp_correct : Valid_exp fexp := FLT_exp_valid emin prec.
Instance fexp_monotone : Monotone_exp fexp := FLT_exp_monotone emin prec.

Notation canonical_mantissa := (canonical_mantissa prec emax).

Notation bounded := (SpecFloat.bounded prec emax).

Notation valid_binary := (valid_binary prec emax).

Inductive binary_float :=
  | B754_zero (s : bool)
  | B754_infinity (s : bool)
  | B754_nan : binary_float
  | B754_finite (s : bool) (m : positive) (e : Z) :
    bounded m e = true -> binary_float.

Definition SF2B x :=
  match x as x return valid_binary x = true -> binary_float with
  | S754_finite s m e => B754_finite s m e
  | S754_infinity s => fun _ => B754_infinity s
  | S754_zero s => fun _ => B754_zero s
  | S754_nan => fun _ => B754_nan
  end.

Definition SF2B' x :=
  match x with
  | S754_zero s => B754_zero s
  | S754_infinity s => B754_infinity s
  | S754_nan => B754_nan
  | S754_finite s m e =>
    match bounded m e as b return bounded m e = b -> _ with
    | true => B754_finite s m e
    | false => fun H => B754_nan
    end eq_refl
  end.

Definition B2SF x :=
  match x with
  | B754_finite s m e _ => S754_finite s m e
  | B754_infinity s => S754_infinity s
  | B754_zero s => S754_zero s
  | B754_nan => S754_nan
  end.

Definition B2R f :=
  match f with
  | B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

Theorem SF2R_B2SF :
  forall x,
  SF2R radix2 (B2SF x) = B2R x.
Proof using .
now intros [sx|sx| |sx mx ex Hx].
Qed.

Theorem B2SF_SF2B :
  forall x Hx,
  B2SF (SF2B x Hx) = x.
Proof using .
now intros [sx|sx| |sx mx ex] Hx.
Qed.

Theorem valid_binary_B2SF :
  forall x,
  valid_binary (B2SF x) = true.
Proof using .
now intros [sx|sx| |sx mx ex Hx].
Qed.

Theorem SF2B_B2SF :
  forall x H,
  SF2B (B2SF x) H = x.
Proof using .
intros [sx|sx| |sx mx ex Hx] H ; try easy.
apply f_equal, eqbool_irrelevance.
Qed.

Theorem SF2B_B2SF_valid :
  forall x,
  SF2B (B2SF x) (valid_binary_B2SF x) = x.
Proof using .
intros x.
apply SF2B_B2SF.
Qed.

Theorem B2R_SF2B :
  forall x Hx,
  B2R (SF2B x Hx) = SF2R radix2 x.
Proof using .
now intros [sx|sx| |sx mx ex] Hx.
Qed.

Theorem match_SF2B :
  forall {T} fz fi fn ff x Hx,
  match SF2B x Hx return T with
  | B754_zero sx => fz sx
  | B754_infinity sx => fi sx
  | B754_nan => fn
  | B754_finite sx mx ex _ => ff sx mx ex
  end =
  match x with
  | S754_zero sx => fz sx
  | S754_infinity sx => fi sx
  | S754_nan => fn
  | S754_finite sx mx ex => ff sx mx ex
  end.
Proof using .
now intros T fz fi fn ff [sx|sx| |sx mx ex] Hx.
Qed.

Theorem canonical_canonical_mantissa :
  forall (sx : bool) mx ex,
  canonical_mantissa mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof using .
intros sx mx ex H.
assert (Hx := Zeq_bool_eq _ _ H).
clear H.
apply sym_eq.
simpl.
pattern ex at 2 ; rewrite <- Hx.
apply (f_equal fexp).
rewrite mag_F2R_Zdigits.
rewrite <- Zdigits_abs.
rewrite Zpos_digits2_pos.
now case sx.
now case sx.
Qed.

Theorem canonical_bounded :
  forall sx mx ex,
  bounded mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof using .
intros sx mx ex H.
apply canonical_canonical_mantissa.
now apply andb_prop in H.
Qed.

Lemma emin_lt_emax :
  (emin < emax)%Z.
Proof using prec_gt_0_ prec_lt_emax_.
unfold emin.
unfold Prec_gt_0 in prec_gt_0_.
unfold Prec_lt_emax in prec_lt_emax_.
lia.
Qed.

Lemma fexp_emax :
  fexp emax = (emax - prec)%Z.
Proof using prec_gt_0_ prec_lt_emax_.
apply Z.max_l.
unfold emin.
unfold Prec_gt_0 in prec_gt_0_.
unfold Prec_lt_emax in prec_lt_emax_.
lia.
Qed.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof using .
intros [sx|sx| |sx mx ex Hx] ; try apply generic_format_0.
simpl.
apply generic_format_canonical.
now apply canonical_bounded.
Qed.

Theorem FLT_format_B2R :
  forall x,
  FLT_format radix2 emin prec (B2R x).
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
intros x.
apply FLT_format_generic...
apply generic_format_B2R.
Qed.

Theorem B2SF_inj :
  forall x y : binary_float,
  B2SF x = B2SF y ->
  x = y.
Proof using .
intros [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy.

intros H.
now inversion H.

intros H.
now inversion H.

intros H.
inversion H.
clear H.
revert Hx.
rewrite H2, H3.
intros Hx.
apply f_equal, eqbool_irrelevance.
Qed.

Theorem SF2B'_B2SF :
  forall x,
  SF2B' (B2SF x) = x.
Proof using .
intros [s|s| |s m e H] ; try easy.
apply B2SF_inj.
simpl.
generalize (eq_refl (bounded m e)).
pattern (bounded m e) at 2 3.
apply eq_sym in H.
now elim H.
Qed.

Definition is_finite_strict f :=
  match f with
  | B754_finite _ _ _ _ => true
  | _ => false
  end.

Definition is_finite_strict_SF f :=
  match f with
  | S754_finite _ _ _ => true
  | _ => false
  end.

Theorem is_finite_strict_B2R :
  forall x,
  B2R x <> 0%R ->
  is_finite_strict x = true.
Proof using .
now intros [sx|sx| |sx mx ex Bx] Hx.
Qed.

Theorem is_finite_strict_SF2B :
  forall x Hx,
  is_finite_strict (SF2B x Hx) = is_finite_strict_SF x.
Proof using .
now intros [sx|sx| |sx mx ex] Hx.
Qed.

Theorem B2R_inj:
  forall x y : binary_float,
  is_finite_strict x = true ->
  is_finite_strict y = true ->
  B2R x = B2R y ->
  x = y.
Proof using .
intros [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy.
simpl.
intros _ _ Heq.
assert (Hs: sx = sy).

revert Heq.
clear.
case sx ; case sy ; try easy ;
  intros Heq ; apply False_ind ; revert Heq.
apply Rlt_not_eq.
apply Rlt_trans with R0.
now apply F2R_lt_0.
now apply F2R_gt_0.
apply Rgt_not_eq.
apply Rgt_trans with R0.
now apply F2R_gt_0.
now apply F2R_lt_0.
assert (mx = my /\ ex = ey).

refine (_ (canonical_unique _ fexp _ _ _ _ Heq)).
rewrite Hs.
now case sy ; intro H ; injection H ; split.
now apply canonical_bounded.
now apply canonical_bounded.

revert Hx.
rewrite Hs, (proj1 H), (proj2 H).
intros Hx.
apply f_equal.
apply eqbool_irrelevance.
Qed.

Definition Bsign x :=
  match x with
  | B754_nan => false
  | B754_zero s => s
  | B754_infinity s => s
  | B754_finite s _ _ _ => s
  end.

Definition sign_SF x :=
  match x with
  | S754_nan => false
  | S754_zero s => s
  | S754_infinity s => s
  | S754_finite s _ _ => s
  end.

Theorem Bsign_SF2B :
  forall x H,
  Bsign (SF2B x H) = sign_SF x.
Proof using .
now intros [sx|sx| |sx mx ex] H.
Qed.

Definition is_finite f :=
  match f with
  | B754_finite _ _ _ _ => true
  | B754_zero _ => true
  | _ => false
  end.

Definition is_finite_SF f :=
  match f with
  | S754_finite _ _ _ => true
  | S754_zero _ => true
  | _ => false
  end.

Theorem is_finite_SF2B :
  forall x Hx,
  is_finite (SF2B x Hx) = is_finite_SF x.
Proof using .
now intros [| | |].
Qed.

Theorem is_finite_SF_B2SF :
  forall x,
  is_finite_SF (B2SF x) = is_finite x.
Proof using .
now intros [| | |].
Qed.

Theorem B2R_Bsign_inj:
  forall x y : binary_float,
    is_finite x = true ->
    is_finite y = true ->
    B2R x = B2R y ->
    Bsign x = Bsign y ->
    x = y.
Proof using .
intros.
destruct x, y; try (apply B2R_inj; now eauto).
-
 simpl in H2.
congruence.
-
 symmetry in H1.
apply Rmult_integral in H1.
  destruct H1.
apply (eq_IZR _ 0) in H1.
destruct s0; discriminate H1.
  simpl in H1.
pose proof (bpow_gt_0 radix2 e).
  rewrite H1 in H3.
apply Rlt_irrefl in H3.
destruct H3.
-
 apply Rmult_integral in H1.
  destruct H1.
apply (eq_IZR _ 0) in H1.
destruct s; discriminate H1.
  simpl in H1.
pose proof (bpow_gt_0 radix2 e).
  rewrite H1 in H3.
apply Rlt_irrefl in H3.
destruct H3.
Qed.

Definition is_nan f :=
  match f with
  | B754_nan => true
  | _ => false
  end.

Definition is_nan_SF f :=
  match f with
  | S754_nan => true
  | _ => false
  end.

Theorem is_nan_SF2B :
  forall x Hx,
  is_nan (SF2B x Hx) = is_nan_SF x.
Proof using .
now intros [| | |].
Qed.

Theorem is_nan_SF_B2SF :
  forall x,
  is_nan_SF (B2SF x) = is_nan x.
Proof using .
now intros [| | |].
Qed.

Definition erase (x : binary_float) : binary_float.
Proof.
destruct x as [s|s| |s m e H].
-
 exact (B754_zero s).
-
 exact (B754_infinity s).
-
 exact B754_nan.
-
 apply (B754_finite s m e).
  destruct bounded.
  apply eq_refl.
  exact H.
Defined.

Theorem erase_correct :
  forall x, erase x = x.
Proof using .
destruct x as [s|s| |s m e H] ; try easy ; simpl.
-
 apply f_equal, eqbool_irrelevance.
Qed.

Definition Bopp x :=
  match x with
  | B754_nan => x
  | B754_infinity sx => B754_infinity (negb sx)
  | B754_finite sx mx ex Hx => B754_finite (negb sx) mx ex Hx
  | B754_zero sx => B754_zero (negb sx)
  end.

Theorem Bopp_involutive :
  forall x,
  Bopp (Bopp x) = x.
Proof using .
now intros [sx|sx| |sx mx ex Hx] ; simpl ; try rewrite Bool.negb_involutive.
Qed.

Theorem B2R_Bopp :
  forall x,
  B2R (Bopp x) = (- B2R x)%R.
Proof using .
intros [sx|sx| |sx mx ex Hx]; apply sym_eq ; try apply Ropp_0.
simpl.
rewrite <- F2R_opp.
now case sx.
Qed.

Theorem is_nan_Bopp :
  forall x,
  is_nan (Bopp x) = is_nan x.
Proof using .
now intros [| | |].
Qed.

Theorem is_finite_Bopp :
  forall x,
  is_finite (Bopp x) = is_finite x.
Proof using .
now intros [| | |].
Qed.

Theorem is_finite_strict_Bopp :
  forall x,
  is_finite_strict (Bopp x) = is_finite_strict x.
Proof using .
now intros [| | |].
Qed.

Lemma Bsign_Bopp :
  forall x, is_nan x = false -> Bsign (Bopp x) = negb (Bsign x).
Proof using .
now intros [s|s| |s m e H].
Qed.

Definition Babs (x : binary_float) : binary_float :=
  match x with
  | B754_nan => x
  | B754_infinity sx => B754_infinity false
  | B754_finite sx mx ex Hx => B754_finite false mx ex Hx
  | B754_zero sx => B754_zero false
  end.

Theorem B2R_Babs :
  forall x,
  B2R (Babs x) = Rabs (B2R x).
Proof using .
intros [sx|sx| |sx mx ex Hx]; apply sym_eq ; try apply Rabs_R0.
simpl.
rewrite <- F2R_abs.
now destruct sx.
Qed.

Theorem is_nan_Babs :
  forall x,
  is_nan (Babs x) = is_nan x.
Proof using .
now intros [| | |].
Qed.

Theorem is_finite_Babs :
  forall x,
  is_finite (Babs x) = is_finite x.
Proof using .
now intros [| | |].
Qed.

Theorem is_finite_strict_Babs :
  forall x,
  is_finite_strict (Babs x) = is_finite_strict x.
Proof using .
now intros [| | |].
Qed.

Theorem Bsign_Babs :
  forall x,
  Bsign (Babs x) = false.
Proof using .
now intros [| | |].
Qed.

Theorem Babs_idempotent :
  forall (x: binary_float),
  Babs (Babs x) = Babs x.
Proof using .
now intros [sx|sx| |sx mx ex Hx].
Qed.

Theorem Babs_Bopp :
  forall x,
  Babs (Bopp x) = Babs x.
Proof using .
now intros [| | |].
Qed.

Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  SFcompare (B2SF f1) (B2SF f2).

Theorem Bcompare_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bcompare f1 f2 = Some (Rcompare (B2R f1) (B2R f2)).
Proof using .
assert (Hb: forall m1 e1 m2 e2, bounded m1 e1 = true -> bounded m2 e2 = true -> (e1 < e2)%Z ->
  (F2R (Float radix2 (Zpos m1) e1) < F2R (Float radix2 (Zpos m2) e2))%R).
{
 intros m1 e1 m2 e2 B1 B2 He.
  apply (lt_cexp_pos radix2 fexp).
  now apply F2R_gt_0.
  rewrite <- (canonical_bounded false _ _ B1).
  rewrite <- (canonical_bounded false _ _ B2).
  easy.
}
assert (Hc: forall m1 e1 m2 e2, bounded m1 e1 = true -> bounded m2 e2 = true ->
  Rcompare (F2R (Float radix2 (Zpos m1) e1)) (F2R (Float radix2 (Zpos m2) e2)) =
  match Z.compare e1 e2 with Eq => Z.compare (Zpos m1) (Zpos m2) | Lt => Lt | Gt => Gt end).
{
 intros m1 e1 m2 e2 B1 B2.
  case Zcompare_spec ; intros He.
  +
 apply Rcompare_Lt.
    now apply Hb.
  +
 now rewrite He, Rcompare_F2R.
  +
 apply Rcompare_Gt.
    now apply Hb.
}
intros [s1|[|]| |[|] m1 e1 B1] ; try easy ;
  intros [s2|[|]| |[|] m2 e2 B2] ; try easy ;
  intros _ _ ; apply (f_equal Some), eq_sym.
-
 now apply Rcompare_Eq.
-
 apply Rcompare_Gt.
  now apply F2R_lt_0.
-
 apply Rcompare_Lt.
  now apply F2R_gt_0.
-
 apply Rcompare_Lt.
  now apply F2R_lt_0.
-
 unfold B2R.
  rewrite 2!F2R_cond_Zopp.
  rewrite Rcompare_opp.
  rewrite Hc by easy.
  rewrite (Z.compare_antisym e1), (Z.compare_antisym (Zpos m1)).
  now case Z.compare.
-
 apply Rcompare_Lt.
  apply Rlt_trans with 0%R.
  now apply F2R_lt_0.
  now apply F2R_gt_0.
-
 apply Rcompare_Gt.
  now apply F2R_gt_0.
-
 apply Rcompare_Gt.
  apply Rlt_trans with 0%R.
  now apply F2R_lt_0.
  now apply F2R_gt_0.
-
 now apply Hc.
Qed.

Theorem Bcompare_swap :
  forall x y,
  Bcompare y x = match Bcompare x y with Some c => Some (CompOpp c) | None => None end.
Proof using .
  intros.
  unfold Bcompare.
  destruct x as [ ? | [] | | [] mx ex Bx ];
  destruct y as [ ? | [] | | [] my ey By ]; simpl; try easy.
-
 rewrite <- (Zcompare_antisym ex ey).
destruct (ex ?= ey)%Z; try easy.
  now rewrite (Pcompare_antisym mx my).
-
 rewrite <- (Zcompare_antisym ex ey).
destruct (ex ?= ey)%Z; try easy.
  now rewrite Pcompare_antisym.
Qed.

Definition Beqb (f1 f2 : binary_float) : bool := SFeqb (B2SF f1) (B2SF f2).

Theorem Beqb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Beqb f1 f2 = Req_bool (B2R f1) (B2R f2).
Proof using .
intros f1 f2 F1 F2.
generalize (Bcompare_correct _ _ F1 F2).
unfold Beqb, SFeqb, Bcompare.
intros ->.
case Rcompare_spec; intro H; case Req_bool_spec; intro H'; try reflexivity; lra.
Qed.

Theorem Beqb_refl :
  forall f, Beqb f f = negb (is_nan f).
Proof using .
intros f.
generalize (fun H => Beqb_correct f f H H).
destruct f as [s|[|]| |s m e H] ; try easy.
intros ->.
2: easy.
now apply Req_bool_true.
Qed.

Definition Bltb (f1 f2 : binary_float) : bool := SFltb (B2SF f1) (B2SF f2).

Theorem Bltb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bltb f1 f2 = Rlt_bool (B2R f1) (B2R f2).
Proof using .
intros f1 f2 F1 F2.
generalize (Bcompare_correct _ _ F1 F2).
unfold Bltb, SFltb, Bcompare.
intros ->.
case Rcompare_spec; intro H; case Rlt_bool_spec; intro H'; try reflexivity; lra.
Qed.

Definition Bleb (f1 f2 : binary_float) : bool := SFleb (B2SF f1) (B2SF f2).

Theorem Bleb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bleb f1 f2 = Rle_bool (B2R f1) (B2R f2).
Proof using .
intros f1 f2 F1 F2.
generalize (Bcompare_correct _ _ F1 F2).
unfold Bleb, SFleb, Bcompare.
intros ->.
case Rcompare_spec; intro H; case Rle_bool_spec; intro H'; try reflexivity; lra.
Qed.

Theorem bounded_le_emax_minus_prec :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex)
   <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof using prec_gt_0_.
clear prec_lt_emax_.
intros mx ex Hx.
apply Rle_trans with ((bpow radix2 (Zdigits radix2 (Z.pos mx)) - 1) * bpow radix2 ex)%R.
-
 apply Rmult_le_compat_r.
  apply bpow_ge_0.
  rewrite <- IZR_Zpower by apply Zdigits_ge_0.
  rewrite <- minus_IZR.
  apply IZR_le.
  apply Z.lt_le_pred.
  rewrite <- (Z.abs_eq (Z.pos mx)) by easy.
  apply Zdigits_correct.
-
 destruct (andb_prop _ _ Hx) as [H1 H2].
  apply Rle_trans with (bpow radix2 (ex + prec) - bpow radix2 ex)%R.
  {
 rewrite Rmult_minus_distr_r, Rmult_1_l, <- bpow_plus.
    apply Rplus_le_compat_r.
    apply bpow_le.
    apply Zeq_bool_eq in H1.
    rewrite Zpos_digits2_pos in H1.
    unfold fexp, FLT_exp in H1.
    clear -H1 ; lia.
}
  replace emax with (emax - prec - ex + (ex + prec))%Z at 1 by ring.
  replace (emax - prec)%Z with (emax - prec - ex + ex)%Z at 2 by ring.
  do 2 rewrite (bpow_plus _ (emax - prec - ex)).
  rewrite <- Rmult_minus_distr_l.
  rewrite <- (Rmult_1_l (_ - _)) at 1.
  apply Rmult_le_compat_r.
  +
 apply Rle_0_minus, bpow_le.
    unfold Prec_gt_0 in prec_gt_0_.
    clear -prec_gt_0_ ; lia.
  +
 apply (bpow_le radix2 0).
    apply Zle_minus_le_0.
    now apply Zle_bool_imp_le.
Qed.

Theorem bounded_lt_emax :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R.
Proof using .
intros mx ex Hx.
destruct (andb_prop _ _ Hx) as (H1,H2).
generalize (Zeq_bool_eq _ _ H1).
clear H1.
intro H1.
generalize (Zle_bool_imp_le _ _ H2).
clear H2.
intro H2.
generalize (mag_F2R_Zdigits radix2 (Zpos mx) ex).
destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex).
unfold mag_val.
intros H.
apply Rlt_le_trans with (bpow radix2 e').
change (Zpos mx) with (Z.abs (Zpos mx)).
rewrite F2R_Zabs.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0.
apply bpow_le.
rewrite H.
2: discriminate.
revert H1.
clear -H2.
rewrite Zpos_digits2_pos.
unfold fexp, FLT_exp.
intros ; lia.
Qed.

Theorem bounded_ge_emin :
  forall mx ex,
  bounded mx ex = true ->
  (bpow radix2 emin <= F2R (Float radix2 (Zpos mx) ex))%R.
Proof using .
intros mx ex Hx.
destruct (andb_prop _ _ Hx) as [H1 _].
apply Zeq_bool_eq in H1.
generalize (mag_F2R_Zdigits radix2 (Zpos mx) ex).
destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as [e' Ex].
unfold mag_val.
intros H.
assert (H0 : Zpos mx <> 0%Z) by easy.
rewrite Rabs_pos_eq in Ex by now apply F2R_ge_0.
refine (Rle_trans _ _ _ _ (proj1 (Ex _))).
2: now apply F2R_neq_0.
apply bpow_le.
rewrite H by easy.
revert H1.
rewrite Zpos_digits2_pos.
generalize (Zdigits radix2 (Zpos mx)) (Zdigits_gt_0 radix2 (Zpos mx) H0).
unfold fexp, FLT_exp.
clear -prec_gt_0_.
unfold Prec_gt_0 in prec_gt_0_.
intros ; lia.
Qed.

Theorem abs_B2R_le_emax_minus_prec :
  forall x,
  (Rabs (B2R x) <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof using prec_gt_0_.
intros [sx|sx| |sx mx ex Hx] ; simpl ;
  [rewrite Rabs_R0 ; apply Rle_0_minus, bpow_le ;
   revert prec_gt_0_; unfold Prec_gt_0; lia..|].
rewrite <- F2R_Zabs, abs_cond_Zopp.
now apply bounded_le_emax_minus_prec.
Qed.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof using .
intros [sx|sx| |sx mx ex Hx] ; simpl ; try ( rewrite Rabs_R0 ; apply bpow_gt_0 ).
rewrite <- F2R_Zabs, abs_cond_Zopp.
now apply bounded_lt_emax.
Qed.

Theorem abs_B2R_ge_emin :
  forall x,
  is_finite_strict x = true ->
  (bpow radix2 emin <= Rabs (B2R x))%R.
Proof using .
intros [sx|sx| |sx mx ex Hx] ; simpl ; try discriminate.
intros; case sx; simpl.
-
 unfold F2R; simpl; rewrite Rabs_mult, <-abs_IZR; simpl.
  rewrite Rabs_pos_eq; [|apply bpow_ge_0].
  now apply bounded_ge_emin.
-
 unfold F2R; simpl; rewrite Rabs_mult, <-abs_IZR; simpl.
  rewrite Rabs_pos_eq; [|apply bpow_ge_0].
  now apply bounded_ge_emin.
Qed.

Theorem bounded_canonical_lt_emax :
  forall mx ex,
  canonical radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R ->
  bounded mx ex = true.
Proof using prec_gt_0_ prec_lt_emax_.
intros mx ex Cx Bx.
apply andb_true_intro.
split.
unfold canonical_mantissa.
unfold canonical, Fexp in Cx.
rewrite Cx at 2.
rewrite Zpos_digits2_pos.
unfold cexp.
rewrite mag_F2R_Zdigits.
2: discriminate.
now apply -> Zeq_is_eq_bool.
apply Zle_bool_true.
unfold canonical, Fexp in Cx.
rewrite Cx.
unfold cexp, fexp, FLT_exp.
destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex).
simpl.
apply Z.max_lub.
cut (e' - 1 < emax)%Z.
clear ; lia.
apply lt_bpow with radix2.
apply Rle_lt_trans with (2 := Bx).
change (Zpos mx) with (Z.abs (Zpos mx)).
rewrite F2R_Zabs.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0.
apply Z.max_l_iff, fexp_emax.
Qed.

Theorem shr_m_shr_record_of_loc :
  forall m l,
  shr_m (shr_record_of_loc m l) = m.
Proof using .
now intros m [|[| |]].
Qed.

Theorem loc_of_shr_record_of_loc :
  forall m l,
  loc_of_shr_record (shr_record_of_loc m l) = l.
Proof using .
now intros m [|[| |]].
Qed.

Lemma inbetween_shr_1 :
  forall x mrs e,
  (0 <= shr_m mrs)%Z ->
  inbetween_float radix2 (shr_m mrs) e x (loc_of_shr_record mrs) ->
  inbetween_float radix2 (shr_m (shr_1 mrs)) (e + 1) x (loc_of_shr_record (shr_1 mrs)).
Proof using .
intros x mrs e Hm Hl.
refine (_ (new_location_even_correct (F2R (Float radix2 (shr_m (shr_1 mrs)) (e + 1))) (bpow radix2 e) 2 _ _ _ x (if shr_r (shr_1 mrs) then 1 else 0) (loc_of_shr_record mrs) _ _)) ; try easy.
2: apply bpow_gt_0.
2: now case (shr_r (shr_1 mrs)) ; split.
change 2%R with (bpow radix2 1).
rewrite <- bpow_plus.
rewrite (Zplus_comm 1), <- (F2R_bpow radix2 (e + 1)).
unfold inbetween_float, F2R.
simpl.
rewrite plus_IZR, Rmult_plus_distr_r.
replace (Bracket.new_location_even 2 (if shr_r (shr_1 mrs) then 1%Z else 0%Z) (loc_of_shr_record mrs)) with (loc_of_shr_record (shr_1 mrs)).
easy.
clear -Hm.
destruct mrs as (m, r, s).
now destruct m as [|[m|m|]|m] ; try (now elim Hm) ; destruct r as [|] ; destruct s as [|].
rewrite (F2R_change_exp radix2 e).
2: apply Zle_succ.
unfold F2R.
simpl.
rewrite <- 2!Rmult_plus_distr_r, <- 2!plus_IZR.
rewrite Zplus_assoc.
replace (shr_m (shr_1 mrs) * 2 ^ (e + 1 - e) + (if shr_r (shr_1 mrs) then 1%Z else 0%Z))%Z with (shr_m mrs).
exact Hl.
ring_simplify (e + 1 - e)%Z.
change (2^1)%Z with 2%Z.
rewrite Zmult_comm.
clear -Hm.
destruct mrs as (m, r, s).
now destruct m as [|[m|m|]|m] ; try (now elim Hm) ; destruct r as [|] ; destruct s as [|].
Qed.

Lemma shr_nat :
  forall mrs e n, (0 <= n)%Z ->
  shr mrs e n = (iter_nat shr_1 (Z.to_nat n) mrs, (e + n)%Z).
Proof using .
intros mrs e n Hn.
destruct n as [|n|n] ; simpl.
now rewrite Zplus_0_r.
now rewrite iter_pos_nat.
easy.
Qed.

Lemma le_shr1_le :
  forall mrs, (0 <= shr_m mrs)%Z ->
  (0 <= shr_m (shr_1 mrs))%Z /\
  (2 * shr_m (shr_1 mrs) <= shr_m mrs < 2 * (shr_m (shr_1 mrs) + 1))%Z.
Proof using .
  intros [[|p|p] r s] ; try easy.
  intros _.
  destruct p as [p|p|] ; simpl ; lia.
Qed.

Theorem inbetween_shr :
  forall x m e l n,
  (0 <= m)%Z ->
  inbetween_float radix2 m e x l ->
  let '(mrs, e') := shr (shr_record_of_loc m l) e n in
  inbetween_float radix2 (shr_m mrs) e' x (loc_of_shr_record mrs).
Proof using .
  intros x m e l n Hm Hl.
  destruct (Zle_or_lt 0 n).
  2: {
    destruct n as [|n|n] ; try easy.
    simpl.
    now rewrite shr_m_shr_record_of_loc, loc_of_shr_record_of_loc.
}
  rewrite shr_nat by easy.
  rewrite <- (Z2Nat.id n) at 2 by easy.
  clear H.
  induction (Z.to_nat n) as [|n' IHn].
  {
 rewrite Zplus_0_r.
    simpl.
    now rewrite shr_m_shr_record_of_loc, loc_of_shr_record_of_loc.
}
  rewrite iter_nat_S, inj_S.
  unfold Z.succ.
  rewrite Zplus_assoc.
  revert IHn.
  apply inbetween_shr_1.
  clear -Hm.
  induction n'.
  simpl.
  now rewrite shr_m_shr_record_of_loc.
  rewrite iter_nat_S.
  now apply le_shr1_le.
Qed.

Lemma le_shr_le :
  forall mrs e n,
  (0 <= shr_m mrs)%Z -> (0 <= n)%Z ->
  (0 <= shr_m (fst (shr mrs e n)))%Z /\
  (2 ^ n * shr_m (fst (shr mrs e n)) <= shr_m mrs < 2 ^ n * (shr_m (fst (shr mrs e n)) + 1))%Z.
Proof using .
  intros mrs e n Hmrs Hn.
  rewrite shr_nat by easy.
  simpl.
  rewrite <- (Z2Nat.id n) at 2 4 by easy.
  induction (Z.to_nat n) as [|n' IHn].
  {
 simpl Z.pow.
rewrite 2!Zmult_1_l.
    simpl.
lia.
}
  clear n Hn.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Zle_0_nat.
  rewrite iter_nat_S.
  revert IHn.
  generalize (iter_nat shr_1 n' mrs).
  intros mrs' [H [IH1 IH2]].
  destruct (le_shr1_le _ H) as [H' [K1 K2]].
  apply (conj H').
  rewrite (Zmult_comm 2), <- 2!Zmult_assoc.
  split.
  -
 apply Z.le_trans with (2 := IH1).
    apply Zmult_le_compat_l with (1 := K1).
    apply (Zpower_ge_0 radix2).
  -
 apply Z.lt_le_trans with (1 := IH2).
    apply Zmult_le_compat_l.
    lia.
    apply (Zpower_ge_0 radix2).
Qed.

Lemma shr_limit :
  forall mrs e n,
  ((0 < shr_m mrs)%Z \/ shr_m mrs = 0%Z /\ (shr_r mrs || shr_s mrs = true)%bool) ->
  (shr_m mrs < radix2 ^ (n - 1))%Z ->
  fst (shr mrs e n) = {| shr_m := 0%Z; shr_r := false; shr_s := true |}.
Proof using .
  intros mrs e n Hmrs0.
set (n' := (n - 1)%Z).
replace n with (n' + 1)%Z; [| lia].
  destruct n' as [| p | p ].
  -
 simpl.
destruct Hmrs0 as [Hmrs0 | Hmrs0]; [lia | intros _].
    destruct mrs as [m r s].
simpl in Hmrs0.
destruct Hmrs0 as [Hmrs00 Hmrs01].
    rewrite Hmrs00.
simpl.
now rewrite Hmrs01.
  -
 intros Hmrs1.
rewrite !Z.add_1_r.
rewrite <-Pos2Z.inj_succ.
simpl shr.
    rewrite iter_pos_nat.
rewrite Pos2Nat.inj_succ.
simpl iter_nat.
    rewrite <-(positive_nat_Z p) in Hmrs1.
rewrite <-(Pos2Nat.id p) at 2.
    revert Hmrs1.
revert Hmrs0.
revert mrs.
    induction (nat_of_P p) as [| n'' IHn''].
    +
 simpl in *.
intros mrs [Hmrs0 | [Hmrs00 Hmrs01]] Hmrs1; [lia |].
      destruct mrs as [m r s].
simpl in Hmrs00, Hmrs01, Hmrs1.
rewrite Hmrs00.
      simpl.
now rewrite Hmrs01.
    +
 intros mrs Hmrs0 Hmrs1.
simpl iter_nat.
      destruct (le_shr1_le mrs) as [Hmrs'0 [Hmrs'1 Hmrs'2]]; [destruct Hmrs0; lia |].
      set (mrs' := shr_1 mrs).
apply IHn''.
      *
 case (0 <? shr_m (shr_1 mrs))%Z eqn:Hmrs'3;
         [apply Zlt_is_lt_bool in Hmrs'3; now left |].
        fold mrs' in Hmrs'0, Hmrs'1, Hmrs'2, Hmrs'3.
        apply Z.ltb_ge in Hmrs'3.
        apply (Z.le_antisymm _ _ Hmrs'3) in Hmrs'0.
right.
split; [assumption |].
        destruct Hmrs0 as [Hmrs0 | [Hmrs00 Hmrs01]].
        --
 rewrite Hmrs'0 in Hmrs'2.
simpl in Hmrs'2.
           assert (Hmrs2 : shr_m mrs = 1%Z) by lia.
destruct mrs as [m r s].
           simpl in Hmrs2.
unfold mrs'.
now rewrite Hmrs2.
        --
 destruct mrs as [m r s].
simpl in Hmrs00, Hmrs01.
unfold mrs'.
           now rewrite Hmrs00.
      *
 simpl Z.of_nat in Hmrs1.
unfold mrs'.
rewrite Zpos_P_of_succ_nat in Hmrs1.
        rewrite Z.pow_succ_r in Hmrs1; [| lia].
apply (Z.le_lt_trans _ _ _ Hmrs'1) in Hmrs1.
        apply Z.mul_lt_mono_pos_l in Hmrs1; [assumption | easy].
  -
 simpl.
destruct Hmrs0 as [Hmrs0 | Hmrs0]; lia.
Qed.

Theorem shr_truncate :
  forall f m e l,
  Valid_exp f ->
  (0 <= m)%Z ->
  shr (shr_record_of_loc m l) e (f (Zdigits2 m + e) - e)%Z =
  let '(m', e', l') := truncate radix2 f (m, e, l) in (shr_record_of_loc m' l', e').
Proof using .
  intros f m e l Hf Hm.
case_eq (truncate radix2 f (m, e, l)).
intros (m', e') l'.
  unfold shr_fexp.
rewrite Zdigits2_Zdigits.
case_eq (f (Zdigits radix2 m + e) - e)%Z.
  -
 intros He.
unfold truncate.
rewrite He.
simpl.
intros H.
now inversion H.
  -
 intros p Hp.
assert (He: (e <= f (Zdigits radix2 m + e))%Z); [ clear -Hp; lia |].
    destruct (inbetween_float_ex radix2 m e l) as (x, Hx).
    generalize (inbetween_shr x m e l (f (Zdigits radix2 m + e) - e) Hm Hx)%Z.
    assert (Hx0 : (0 <= x)%R);
     [apply Rle_trans with (F2R (Float radix2 m e));
       [now apply F2R_ge_0
       |exact (proj1 (inbetween_float_bounds _ _ _ _ _ Hx))]
     |].
    case_eq (shr (shr_record_of_loc m l) e (f (Zdigits radix2 m + e) - e))%Z.
    intros mrs e'' H3 H4 H1.
    generalize (truncate_correct radix2 _ x m e l Hx0 Hx (or_introl _ He)).
    rewrite H1.
intros (H2,_).
rewrite <- Hp, H3.
    assert (e'' = e').
    {
 change (snd (mrs, e'') = snd (fst (m',e',l'))).
 rewrite <- H1, <- H3.
      unfold truncate.
now rewrite Hp.
}
    rewrite H in H4 |- *.
apply (f_equal (fun v => (v, _))).
    destruct (inbetween_float_unique _ _ _ _ _ _ _ H2 H4) as (H5, H6).
    rewrite H5, H6.
case mrs.
now intros m0 [|] [|].
  -
 intros p Hp.
unfold truncate.
rewrite Hp.
simpl.
intros H.
now inversion H.
Qed.

Notation shr_fexp := (shr_fexp prec emax).

Theorem shr_fexp_truncate :
  forall m e l,
  (0 <= m)%Z ->
  shr_fexp m e l =
  let '(m', e', l') := truncate radix2 fexp (m, e, l) in (shr_record_of_loc m' l', e').
Proof using prec_gt_0_.
intros m e l Hm.
case_eq (truncate radix2 fexp (m, e, l)).
intros (m', e') l'.
unfold shr_fexp.
rewrite Zdigits2_Zdigits.
case_eq (fexp (Zdigits radix2 m + e) - e)%Z.

intros He.
unfold truncate.
rewrite He.
simpl.
intros H.
now inversion H.

intros p Hp.
assert (He: (e <= fexp (Zdigits radix2 m + e))%Z).
clear -Hp ; lia.
destruct (inbetween_float_ex radix2 m e l) as (x, Hx).
generalize (inbetween_shr x m e l (fexp (Zdigits radix2 m + e) - e) Hm Hx).
assert (Hx0 : (0 <= x)%R).
apply Rle_trans with (F2R (Float radix2 m e)).
now apply F2R_ge_0.
exact (proj1 (inbetween_float_bounds _ _ _ _ _ Hx)).
case_eq (shr (shr_record_of_loc m l) e (fexp (Zdigits radix2 m + e) - e)).
intros mrs e'' H3 H4 H1.
generalize (truncate_correct radix2 _ x m e l Hx0 Hx (or_introl _ He)).
rewrite H1.
intros (H2,_).
rewrite <- Hp, H3.
assert (e'' = e').
change (snd (mrs, e'') = snd (fst (m',e',l'))).
rewrite <- H1, <- H3.
unfold truncate.
now rewrite Hp.
rewrite H in H4 |- *.
apply (f_equal (fun v => (v, _))).
destruct (inbetween_float_unique _ _ _ _ _ _ _ H2 H4) as (H5, H6).
rewrite H5, H6.
case mrs.
now intros m0 [|] [|].

intros p Hp.
unfold truncate.
rewrite Hp.
simpl.
intros H.
now inversion H.
Qed.

Inductive mode := mode_NE | mode_ZR | mode_DN | mode_UP | mode_NA.

Definition round_mode m :=
  match m with
  | mode_NE => ZnearestE
  | mode_ZR => Ztrunc
  | mode_DN => Zfloor
  | mode_UP => Zceil
  | mode_NA => ZnearestA
  end.

Definition choice_mode m sx mx lx :=
  match m with
  | mode_NE => cond_incr (round_N (negb (Z.even mx)) lx) mx
  | mode_ZR => mx
  | mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode_NA => cond_incr (round_N true lx) mx
  end.

Lemma le_choice_mode_le :
  forall m sx mx lx, (mx <= choice_mode m sx mx lx <= mx + 1)%Z.
Proof using .
  unfold choice_mode; intros m sx mx lx; case m; simpl; try lia; apply le_cond_incr_le.
Qed.

Lemma round_mode_choice_mode :
  forall md x m l,
  inbetween_int m (Rabs x) l ->
  round_mode md x = cond_Zopp (Rlt_bool x 0) (choice_mode md (Rlt_bool x 0) m l).
Proof using .
  destruct md.
  -
 exact inbetween_int_NE_sign.
  -
 exact inbetween_int_ZR_sign.
  -
 exact inbetween_int_DN_sign.
  -
 exact inbetween_int_UP_sign.
  -
 exact inbetween_int_NA_sign.
Qed.

Global Instance valid_rnd_round_mode : forall m, Valid_rnd (round_mode m).
Proof using .
destruct m ; unfold round_mode ; auto with typeclass_instances.
Qed.

Definition overflow_to_inf m s :=
  match m with
  | mode_NE => true
  | mode_NA => true
  | mode_ZR => false
  | mode_UP => negb s
  | mode_DN => s
  end.

Definition binary_overflow m s :=
  if overflow_to_inf m s then S754_infinity s
  else S754_finite s (Z.to_pos (Zpower 2 prec - 1)%Z) (emax - prec).

Theorem is_nan_binary_overflow :
  forall mode s,
  is_nan_SF (binary_overflow mode s) = false.
Proof using .
intros mode s.
unfold binary_overflow.
now destruct overflow_to_inf.
Qed.

Theorem binary_overflow_correct :
  forall m s,
  valid_binary (binary_overflow m s) = true.
Proof using prec_gt_0_ prec_lt_emax_.
intros m s.
unfold binary_overflow.
case overflow_to_inf.
easy.
unfold valid_binary, bounded.
rewrite Zle_bool_refl.
rewrite Bool.andb_true_r.
apply Zeq_bool_true.
rewrite Zpos_digits2_pos.
replace (Zdigits radix2 _) with prec.
ring_simplify (prec + (emax - prec))%Z.
apply fexp_emax.
change 2%Z with (radix_val radix2).
assert (H: (0 < radix2 ^ prec - 1)%Z).
  apply Zlt_succ_pred.
  now apply Zpower_gt_1.
rewrite Z2Pos.id by exact H.
apply Zle_antisym.
-
 apply Z.lt_pred_le.
  apply Zdigits_gt_Zpower.
  rewrite Z.abs_eq by now apply Zlt_le_weak.
  apply Z.lt_le_pred.
  apply Zpower_lt.
  now apply Zlt_le_weak.
  apply Z.lt_pred_l.
-
 apply Zdigits_le_Zpower.
  rewrite Z.abs_eq by now apply Zlt_le_weak.
  apply Z.lt_pred_l.
Qed.

Definition binary_fit_aux mode sx mx ex :=
  if Zle_bool ex (emax - prec) then S754_finite sx mx ex
  else binary_overflow mode sx.

Theorem binary_fit_aux_correct :
  forall mode sx mx ex,
  canonical_mantissa mx ex = true ->
  let x := SF2R radix2 (S754_finite sx mx ex) in
  let z := binary_fit_aux mode sx mx ex in
  valid_binary z = true /\
  if Rlt_bool (Rabs x) (bpow radix2 emax) then
    SF2R radix2 z = x /\ is_finite_SF z = true /\ sign_SF z = sx
  else
    z = binary_overflow mode sx.
Proof using prec_gt_0_ prec_lt_emax_.
intros m sx mx ex Cx.
unfold binary_fit_aux.
simpl.
rewrite F2R_cond_Zopp.
rewrite abs_cond_Ropp.
rewrite Rabs_pos_eq by now apply F2R_ge_0.
destruct Zle_bool eqn:He.
-
 assert (Hb: bounded mx ex = true).
  {
 unfold bounded.
now rewrite Cx.
}
  apply (conj Hb).
  rewrite Rlt_bool_true.
  repeat split.
  apply F2R_cond_Zopp.
  now apply bounded_lt_emax.
-
 rewrite Rlt_bool_false.
  {
 repeat split.
    apply binary_overflow_correct.
}
  apply Rnot_lt_le.
  intros Hx.
  apply bounded_canonical_lt_emax in Hx.
  revert Hx.
  unfold bounded.
  now rewrite Cx, He.
  now apply (canonical_canonical_mantissa false).
Qed.

Definition binary_round_aux mode sx mx ex lx :=
  let '(mrs', e') := shr_fexp mx ex lx in
  let '(mrs'', e'') := shr_fexp (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact in
  match shr_m mrs'' with
  | Z0 => S754_zero sx
  | Zpos m => binary_fit_aux mode sx m e''
  | _ => S754_nan
  end.

Theorem binary_round_aux_correct' :
  forall mode x mx ex lx,
  (x <> 0)%R ->
  inbetween_float radix2 mx ex (Rabs x) lx ->
  (ex <= cexp radix2 fexp x)%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) mx ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_SF z = true /\ sign_SF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof using prec_gt_0_ prec_lt_emax_.
Proof with auto with typeclass_instances.
intros m x mx ex lx Px Bx Ex z.
unfold binary_round_aux in z.
revert z.
rewrite shr_fexp_truncate.
refine (_ (round_trunc_sign_any_correct' _ _ (round_mode m) (choice_mode m) _ x mx ex lx Bx (or_introl _ Ex))).
rewrite <- cexp_abs in Ex.
refine (_ (truncate_correct_partial' _ fexp _ _ _ _ _ Bx Ex)).
destruct (truncate radix2 fexp (mx, ex, lx)) as ((m1, e1), l1).
rewrite loc_of_shr_record_of_loc, shr_m_shr_record_of_loc.
set (m1' := choice_mode m (Rlt_bool x 0) m1 l1).
intros (H1a,H1b) H1c.
rewrite H1c.
assert (Hm: (m1 <= m1')%Z).

unfold m1', choice_mode, cond_incr.
case m ;
  try apply Z.le_refl ;
  match goal with |- (m1 <= if ?b then _ else _)%Z =>
    case b ; [ apply Zle_succ | apply Z.le_refl ] end.
assert (Hr: Rabs (round radix2 fexp (round_mode m) x) = F2R (Float radix2 m1' e1)).

rewrite <- (Z.abs_eq m1').
rewrite <- (abs_cond_Zopp (Rlt_bool x 0) m1').
rewrite F2R_Zabs.
now apply f_equal.
apply Z.le_trans with (2 := Hm).
apply Zlt_succ_le.
apply gt_0_F2R with radix2 e1.
apply Rle_lt_trans with (1 := Rabs_pos x).
exact (proj2 (inbetween_float_bounds _ _ _ _ _ H1a)).

assert (Br: inbetween_float radix2 m1' e1 (Rabs (round radix2 fexp (round_mode m) x)) loc_Exact).
now apply inbetween_Exact.
destruct m1' as [|m1'|m1'].

rewrite shr_fexp_truncate.
2: apply Z.le_refl.
generalize (truncate_0 radix2 fexp e1 loc_Exact).
destruct (truncate radix2 fexp (Z0, e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros Hm2.
rewrite Hm2.
repeat split.
rewrite Rlt_bool_true.
repeat split.
apply sym_eq.
case Rlt_bool ; apply F2R_0.
rewrite <- F2R_Zabs, abs_cond_Zopp, F2R_0.
apply bpow_gt_0.

assert (He: (e1 <= fexp (Zdigits radix2 (Zpos m1') + e1))%Z).
rewrite <- mag_F2R_Zdigits, <- Hr, mag_abs.
2: discriminate.
rewrite H1b.
rewrite cexp_abs.
fold (cexp radix2 fexp (round radix2 fexp (round_mode m) x)).
apply cexp_round_ge...
rewrite H1c.
case (Rlt_bool x 0).
apply Rlt_not_eq.
now apply F2R_lt_0.
apply Rgt_not_eq.
now apply F2R_gt_0.
refine (_ (truncate_correct_partial _ _ _ _ _ _ _ Br He)).
2: now rewrite Hr ; apply F2R_gt_0.
refine (_ (truncate_correct_format radix2 fexp (Zpos m1') e1 _ _ He)).
2: discriminate.
rewrite shr_fexp_truncate.
2: easy.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0.
destruct (binary_fit_aux_correct m (Rlt_bool x 0) m2 e2) as [H5 H6].
  apply Zeq_bool_true.
  rewrite Zpos_digits2_pos.
  rewrite <- mag_F2R_Zdigits by easy.
  now rewrite <- H3.
apply (conj H5).
revert H6.
simpl.
rewrite 2!F2R_cond_Zopp.
now rewrite <- H3.
elim Rgt_not_eq with (2 := H3).
apply Rlt_trans with R0.
now apply F2R_lt_0.
now apply F2R_gt_0.
rewrite <- Hr.
apply generic_format_abs...
apply generic_format_round...

elim Rgt_not_eq with (2 := Hr).
apply Rlt_le_trans with R0.
now apply F2R_lt_0.
apply Rabs_pos.

now apply Rabs_pos_lt.

clear.
case m.
exact inbetween_int_NE_sign.
exact inbetween_int_ZR_sign.
exact inbetween_int_DN_sign.
exact inbetween_int_UP_sign.
exact inbetween_int_NA_sign.

apply inbetween_float_bounds in Bx.
apply Zlt_succ_le.
eapply gt_0_F2R.
apply Rle_lt_trans with (2 := proj2 Bx).
apply Rabs_pos.
Qed.

Theorem binary_round_aux_correct :
  forall mode x mx ex lx,
  inbetween_float radix2 (Zpos mx) ex (Rabs x) lx ->
  (ex <= fexp (Zdigits radix2 (Zpos mx) + ex))%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) (Zpos mx) ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_SF z = true /\ sign_SF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof using prec_gt_0_ prec_lt_emax_.
Proof with auto with typeclass_instances.
intros m x mx ex lx Bx Ex z.
unfold binary_round_aux in z.
revert z.
rewrite shr_fexp_truncate.
2: easy.
refine (_ (round_trunc_sign_any_correct _ _ (round_mode m) (choice_mode m) _ x (Zpos mx) ex lx Bx (or_introl _ Ex))).
refine (_ (truncate_correct_partial _ _ _ _ _ _ _ Bx Ex)).
destruct (truncate radix2 fexp (Zpos mx, ex, lx)) as ((m1, e1), l1).
rewrite loc_of_shr_record_of_loc, shr_m_shr_record_of_loc.
set (m1' := choice_mode m (Rlt_bool x 0) m1 l1).
intros (H1a,H1b) H1c.
rewrite H1c.
assert (Hm: (m1 <= m1')%Z).

unfold m1', choice_mode, cond_incr.
case m ;
  try apply Z.le_refl ;
  match goal with |- (m1 <= if ?b then _ else _)%Z =>
    case b ; [ apply Zle_succ | apply Z.le_refl ] end.
assert (Hr: Rabs (round radix2 fexp (round_mode m) x) = F2R (Float radix2 m1' e1)).

rewrite <- (Z.abs_eq m1').
rewrite <- (abs_cond_Zopp (Rlt_bool x 0) m1').
rewrite F2R_Zabs.
now apply f_equal.
apply Z.le_trans with (2 := Hm).
apply Zlt_succ_le.
apply gt_0_F2R with radix2 e1.
apply Rle_lt_trans with (1 := Rabs_pos x).
exact (proj2 (inbetween_float_bounds _ _ _ _ _ H1a)).

assert (Br: inbetween_float radix2 m1' e1 (Rabs (round radix2 fexp (round_mode m) x)) loc_Exact).
now apply inbetween_Exact.
destruct m1' as [|m1'|m1'].

rewrite shr_fexp_truncate.
2: apply Z.le_refl.
generalize (truncate_0 radix2 fexp e1 loc_Exact).
destruct (truncate radix2 fexp (Z0, e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros Hm2.
rewrite Hm2.
repeat split.
rewrite Rlt_bool_true.
repeat split.
apply sym_eq.
case Rlt_bool ; apply F2R_0.
rewrite <- F2R_Zabs, abs_cond_Zopp, F2R_0.
apply bpow_gt_0.

assert (He: (e1 <= fexp (Zdigits radix2 (Zpos m1') + e1))%Z).
rewrite <- mag_F2R_Zdigits, <- Hr, mag_abs.
2: discriminate.
rewrite H1b.
rewrite cexp_abs.
fold (cexp radix2 fexp (round radix2 fexp (round_mode m) x)).
apply cexp_round_ge...
rewrite H1c.
case (Rlt_bool x 0).
apply Rlt_not_eq.
now apply F2R_lt_0.
apply Rgt_not_eq.
now apply F2R_gt_0.
refine (_ (truncate_correct_partial _ _ _ _ _ _ _ Br He)).
2: now rewrite Hr ; apply F2R_gt_0.
refine (_ (truncate_correct_format radix2 fexp (Zpos m1') e1 _ _ He)).
2: discriminate.
rewrite shr_fexp_truncate.
2: easy.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0.
destruct (binary_fit_aux_correct m (Rlt_bool x 0) m2 e2) as [H5 H6].
  apply Zeq_bool_true.
  rewrite Zpos_digits2_pos.
  rewrite <- mag_F2R_Zdigits by easy.
  now rewrite <- H3.
apply (conj H5).
revert H6.
simpl.
rewrite 2!F2R_cond_Zopp.
now rewrite <- H3.
elim Rgt_not_eq with (2 := H3).
apply Rlt_trans with R0.
now apply F2R_lt_0.
now apply F2R_gt_0.
rewrite <- Hr.
apply generic_format_abs...
apply generic_format_round...

elim Rgt_not_eq with (2 := Hr).
apply Rlt_le_trans with R0.
now apply F2R_lt_0.
apply Rabs_pos.

apply Rlt_le_trans with (2 := proj1 (inbetween_float_bounds _ _ _ _ _ Bx)).
now apply F2R_gt_0.

clear.
case m.
exact inbetween_int_NE_sign.
exact inbetween_int_ZR_sign.
exact inbetween_int_DN_sign.
exact inbetween_int_UP_sign.
exact inbetween_int_NA_sign.
Qed.

Lemma Bmult_correct_aux :
  forall m sx mx ex (Hx : bounded mx ex = true) sy my ey (Hy : bounded my ey = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  let z := binary_round_aux m (xorb sx sy) (Zpos (mx * my)) (ex + ey) loc_Exact in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (x * y))) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode m) (x * y) /\
    is_finite_SF z = true /\ sign_SF z = xorb sx sy
  else
    z = binary_overflow m (xorb sx sy).
Proof using prec_gt_0_ prec_lt_emax_.
intros m sx mx ex Hx sy my ey Hy x y.
unfold x, y.
rewrite <- F2R_mult.
simpl.
replace (xorb sx sy) with (Rlt_bool (F2R (Float radix2 (cond_Zopp sx (Zpos mx) * cond_Zopp sy (Zpos my)) (ex + ey))) 0).
apply binary_round_aux_correct.
constructor.
rewrite <- F2R_abs.
apply F2R_eq.
rewrite Zabs_Zmult.
now rewrite 2!abs_cond_Zopp.

change (Zpos (mx * my)) with (Zpos mx * Zpos my)%Z.
assert (forall m e, bounded m e = true -> fexp (Zdigits radix2 (Zpos m) + e) = e)%Z.
clear.
intros m e Hb.
destruct (andb_prop _ _ Hb) as (H,_).
apply Zeq_bool_eq.
now rewrite <- Zpos_digits2_pos.
generalize (H _ _ Hx) (H _ _ Hy).
clear x y sx sy Hx Hy H.
unfold fexp, FLT_exp.
refine (_ (Zdigits_mult_ge radix2 (Zpos mx) (Zpos my) _ _)) ; try discriminate.
refine (_ (Zdigits_gt_0 radix2 (Zpos mx) _) (Zdigits_gt_0 radix2 (Zpos my) _)) ; try discriminate.
generalize (Zdigits radix2 (Zpos mx)) (Zdigits radix2 (Zpos my)) (Zdigits radix2 (Zpos mx * Zpos my)).
intros dx dy dxy Hx Hy Hxy.
unfold emin.
generalize (prec_lt_emax prec emax).
lia.

case sx ; case sy.
apply Rlt_bool_false.
now apply F2R_ge_0.
apply Rlt_bool_true.
now apply F2R_lt_0.
apply Rlt_bool_true.
now apply F2R_lt_0.
apply Rlt_bool_false.
now apply F2R_ge_0.
Qed.

Definition Bmult m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity _, B754_zero _ => B754_nan
  | B754_zero _, B754_infinity _ => B754_nan
  | B754_finite sx _ _ _, B754_zero sy => B754_zero (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_zero (xorb sx sy)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    SF2B _ (proj1 (Bmult_correct_aux m sx mx ex Hx sy my ey Hy))
  end.

Theorem Bmult_correct :
  forall m x y,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x * B2R y))) (bpow radix2 emax) then
    B2R (Bmult m x y) = round radix2 fexp (round_mode m) (B2R x * B2R y) /\
    is_finite (Bmult m x y) = andb (is_finite x) (is_finite y) /\
    (is_nan (Bmult m x y) = false ->
      Bsign (Bmult m x y) = xorb (Bsign x) (Bsign y))
  else
    B2SF (Bmult m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof using .
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ;
  try ( rewrite ?Rmult_0_r, ?Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ simpl ; try easy ; now rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan | apply bpow_gt_0 | now auto with typeclass_instances ] ).
simpl.
case Bmult_correct_aux.
intros H1.
case Rlt_bool.
intros (H2, (H3, H4)).
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
rewrite Bsign_SF2B.
auto.
intros H2.
now rewrite B2SF_SF2B.
Qed.

Theorem shl_align_correct':
  forall mx ex e,
  (e <= ex)%Z ->
  let (mx', ex') := shl_align mx ex e in
  F2R (Float radix2 (Zpos mx') e) = F2R (Float radix2 (Zpos mx) ex) /\
  ex' = e.
Proof using .
intros mx ex ex' He.
unfold shl_align.
destruct (ex' - ex)%Z as [|d|d] eqn:Hd ; simpl.
-
 now replace ex with ex' by lia.
-
 exfalso ; lia.
-
 refine (conj _ eq_refl).
  fold (shift_pos d mx).
  rewrite shift_pos_correct, Zmult_comm.
  change (Zpower_pos 2 d) with (Zpower radix2 (Z.opp (Z.neg d))).
  rewrite <- Hd.
  replace (- (ex' - ex))%Z with (ex - ex')%Z by ring.
  now apply eq_sym, F2R_change_exp.
Qed.

Theorem shl_align_correct :
  forall mx ex ex',
  let (mx', ex'') := shl_align mx ex ex' in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex'') /\
  (ex'' <= ex')%Z.
Proof using .
intros mx ex ex'.
generalize (shl_align_correct' mx ex ex').
unfold shl_align.
destruct (ex' - ex)%Z as [|d|d] eqn:Hd ; simpl.
-
 refine (fun H => _ (H _)).
  2: clear -Hd; lia.
  clear.
  intros [H1 ->].
  now split.
-
 intros _.
  refine (conj eq_refl _).
  lia.
-
 refine (fun H => _ (H _)).
  2: clear -Hd; lia.
  clear.
  now split.
Qed.

Theorem snd_shl_align :
  forall mx ex ex',
  (ex' <= ex)%Z ->
  snd (shl_align mx ex ex') = ex'.
Proof using .
intros mx ex ex' He.
generalize (shl_align_correct' mx ex ex' He).
now destruct shl_align as [m e].
Qed.

Definition shl_align_fexp mx ex :=
  shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex)).

Theorem shl_align_fexp_correct :
  forall mx ex,
  let (mx', ex') := shl_align_fexp mx ex in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') /\
  (ex' <= fexp (Zdigits radix2 (Zpos mx') + ex'))%Z.
Proof using .
intros mx ex.
unfold shl_align_fexp.
generalize (shl_align_correct mx ex (fexp (Zpos (digits2_pos mx) + ex))).
rewrite Zpos_digits2_pos.
case shl_align.
intros mx' ex' (H1, H2).
split.
exact H1.
rewrite <- mag_F2R_Zdigits.
2: easy.
rewrite <- H1.
now rewrite mag_F2R_Zdigits.
Qed.

Definition binary_round m sx mx ex :=
  let '(mz, ez) := shl_align_fexp mx ex in binary_round_aux m sx (Zpos mz) ez loc_Exact.

Theorem binary_round_correct :
  forall m sx mx ex,
  let z := binary_round m sx mx ex in
  valid_binary z = true /\
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) x)) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode m) x /\
    is_finite_SF z = true /\
    sign_SF z = sx
  else
    z = binary_overflow m sx.
Proof using prec_gt_0_ prec_lt_emax_.
intros m sx mx ex.
unfold binary_round.
generalize (shl_align_fexp_correct mx ex).
destruct (shl_align_fexp mx ex) as (mz, ez).
intros (H1, H2).
set (x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex)).
replace sx with (Rlt_bool x 0).
apply binary_round_aux_correct.
constructor.
unfold x.
now rewrite <- F2R_Zabs, abs_cond_Zopp.
exact H2.
unfold x.
case sx.
apply Rlt_bool_true.
now apply F2R_lt_0.
apply Rlt_bool_false.
now apply F2R_ge_0.
Qed.

Theorem is_nan_binary_round :
  forall mode sx mx ex,
  is_nan_SF (binary_round mode sx mx ex) = false.
Proof using prec_gt_0_ prec_lt_emax_.
intros mode sx mx ex.
generalize (binary_round_correct mode sx mx ex).
simpl.
destruct binary_round ; try easy.
intros [_ H].
destruct Rlt_bool ; try easy.
unfold binary_overflow in H.
now destruct overflow_to_inf.
Qed.

Definition binary_normalize mode m e szero :=
  match m with
  | Z0 => B754_zero szero
  | Zpos m => SF2B _ (proj1 (binary_round_correct mode false m e))
  | Zneg m => SF2B _ (proj1 (binary_round_correct mode true m e))
  end.

Theorem binary_normalize_correct :
  forall m mx ex szero,
  let x := F2R (Float radix2 mx ex) in
  let z := binary_normalize m mx ex szero in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) x)) (bpow radix2 emax) then
    B2R z = round radix2 fexp (round_mode m) x /\
    is_finite z = true /\
    Bsign z =
      match Rcompare x 0 with
        | Eq => szero
        | Lt => true
        | Gt => false
      end
  else
    B2SF z = binary_overflow m (Rlt_bool x 0).
Proof using .
Proof with auto with typeclass_instances.
intros m mx ez szero.
destruct mx as [|mz|mz] ; simpl.
rewrite F2R_0, round_0, Rabs_R0, Rlt_bool_true...
split...
split...
rewrite Rcompare_Eq...
apply bpow_gt_0.

generalize (binary_round_correct m false mz ez).
simpl.
case Rlt_bool_spec.
intros _ (Vz, (Rz, (Rz', Rz''))).
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
rewrite Bsign_SF2B, Rz''.
rewrite Rcompare_Gt...
now apply F2R_gt_0.
intros Hz' (Vz, Rz).
rewrite B2SF_SF2B, Rz.
apply f_equal.
apply sym_eq.
apply Rlt_bool_false.
now apply F2R_ge_0.

generalize (binary_round_correct m true mz ez).
simpl.
case Rlt_bool_spec.
intros _ (Vz, (Rz, (Rz', Rz''))).
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
rewrite Bsign_SF2B, Rz''.
rewrite Rcompare_Lt...
now apply F2R_lt_0.
intros Hz' (Vz, Rz).
rewrite B2SF_SF2B, Rz.
apply f_equal.
apply sym_eq.
apply Rlt_bool_true.
now apply F2R_lt_0.
Qed.

Theorem is_nan_binary_normalize :
  forall mode m e szero,
  is_nan (binary_normalize mode m e szero) = false.
Proof using .
intros mode m e szero.
generalize (binary_normalize_correct mode m e szero).
simpl.
destruct Rlt_bool.
-
 intros [_ [H _]].
  now destruct binary_normalize.
-
 intros H.
  rewrite <- is_nan_SF_B2SF.
  rewrite H.
  unfold binary_overflow.
  now destruct overflow_to_inf.
Qed.

Definition Fplus_naive sx mx ex sy my ey ez :=
  (Zplus (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))).

Lemma Fplus_naive_correct :
  forall sx mx ex sy my ey ez,
  (ez <= ex)%Z -> (ez <= ey)%Z ->
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  F2R (Float radix2 (Fplus_naive sx mx ex sy my ey ez) ez) = (x + y)%R.
Proof using .
intros sx mx ex sy my ey ez Ex Ey.
unfold Fplus_naive, F2R.
simpl.
generalize (shl_align_correct' mx ex ez Ex).
generalize (shl_align_correct' my ey ez Ey).
destruct shl_align as [my' ey'].
destruct shl_align as [mx' ex'].
intros [Hy _].
intros [Hx _].
simpl.
rewrite plus_IZR, Rmult_plus_distr_r.
generalize (f_equal (cond_Ropp sx) Hx).
generalize (f_equal (cond_Ropp sy) Hy).
rewrite <- 4!F2R_cond_Zopp.
unfold F2R.
simpl.
now intros -> ->.
Qed.

Lemma sign_plus_overflow :
  forall m sx mx ex sy my ey,
  bounded mx ex = true ->
  bounded my ey = true ->
  let z := (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) + F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey))%R in
  (bpow radix2 emax <= Rabs (round radix2 fexp (round_mode m) z))%R ->
  sx = Rlt_bool z 0 /\ sx = sy.
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
intros m sx mx ex sy my ey Hx Hy z Bz.
destruct (Bool.bool_dec sx sy) as [Hs|Hs].

refine (conj _ Hs).
unfold z.
rewrite Hs.
apply sym_eq.
case sy.
apply Rlt_bool_true.
rewrite <- (Rplus_0_r 0).
apply Rplus_lt_compat.
now apply F2R_lt_0.
now apply F2R_lt_0.
apply Rlt_bool_false.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
now apply F2R_ge_0.
now apply F2R_ge_0.

elim Rle_not_lt with (1 := Bz).
generalize (bounded_lt_emax _ _ Hx) (bounded_lt_emax _ _ Hy).
intros Bx By.
generalize (canonical_bounded sx _ _ Hx) (canonical_bounded sy _ _ Hy).
clear -Bx By Hs prec_gt_0_.
intros Cx Cy.
destruct sx.

destruct sy.
now elim Hs.
clear Hs.
apply Rabs_lt.
split.
apply Rlt_le_trans with (F2R (Float radix2 (cond_Zopp true (Zpos mx)) ex)).
rewrite F2R_Zopp.
now apply Ropp_lt_contravar.
apply round_ge_generic...
now apply generic_format_canonical.
pattern (F2R (Float radix2 (cond_Zopp true (Zpos mx)) ex)) at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
now apply F2R_ge_0.
apply Rle_lt_trans with (2 := By).
apply round_le_generic...
now apply generic_format_canonical.
rewrite <- (Rplus_0_l (F2R (Float radix2 (Zpos my) ey))).
apply Rplus_le_compat_r.
now apply F2R_le_0.

destruct sy.
2: now elim Hs.
clear Hs.
apply Rabs_lt.
split.
apply Rlt_le_trans with (F2R (Float radix2 (cond_Zopp true (Zpos my)) ey)).
rewrite F2R_Zopp.
now apply Ropp_lt_contravar.
apply round_ge_generic...
now apply generic_format_canonical.
pattern (F2R (Float radix2 (cond_Zopp true (Zpos my)) ey)) at 1 ; rewrite <- Rplus_0_l.
apply Rplus_le_compat_r.
now apply F2R_ge_0.
apply Rle_lt_trans with (2 := Bx).
apply round_le_generic...
now apply generic_format_canonical.
rewrite <- (Rplus_0_r (F2R (Float radix2 (Zpos mx) ex))).
apply Rplus_le_compat_l.
now apply F2R_le_0.
Qed.

Definition Bplus m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy => if Bool.eqb sx sy then x else B754_nan
  | B754_infinity _, _ => x
  | _, B754_infinity _ => y
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx sy then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, _ => y
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Z.min ex ey in
    binary_normalize m (Fplus_naive sx mx ex sy my ey ez)
      ez (match m with mode_DN => true | _ => false end)
  end.

Theorem Bplus_correct :
  forall m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x + B2R y))) (bpow radix2 emax) then
    B2R (Bplus m x y) = round radix2 fexp (round_mode m) (B2R x + B2R y) /\
    is_finite (Bplus m x y) = true /\
    Bsign (Bplus m x y) =
      match Rcompare (B2R x + B2R y) 0 with
        | Eq => match m with mode_DN => orb (Bsign x) (Bsign y)
                                 | _ => andb (Bsign x) (Bsign y) end
        | Lt => true
        | Gt => false
      end
  else
    (B2SF (Bplus m x y) = binary_overflow m (Bsign x) /\ Bsign x = Bsign y).
Proof using .
Proof with auto with typeclass_instances.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] Fx Fy ; try easy.

rewrite Rplus_0_r, round_0, Rabs_R0, Rlt_bool_true...
simpl.
rewrite Rcompare_Eq by auto.
destruct sx, sy; try easy; now case m.
apply bpow_gt_0.

rewrite Rplus_0_l, round_generic, Rlt_bool_true...
split...
split...
simpl.
unfold F2R.
erewrite <- Rmult_0_l, Rcompare_mult_r.
rewrite Rcompare_IZR with (y:=0%Z).
destruct sy...
apply bpow_gt_0.
apply abs_B2R_lt_emax.
apply generic_format_B2R.

rewrite Rplus_0_r, round_generic, Rlt_bool_true...
split...
split...
simpl.
unfold F2R.
erewrite <- Rmult_0_l, Rcompare_mult_r.
rewrite Rcompare_IZR with (y:=0%Z).
destruct sx...
apply bpow_gt_0.
apply abs_B2R_lt_emax.
apply generic_format_B2R.

clear Fx Fy.
simpl.
set (szero := match m with mode_DN => true | _ => false end).
set (ez := Z.min ex ey).
assert (Hp := Fplus_naive_correct sx mx ex sy my ey ez (Z.le_min_l _ _) (Z.le_min_r _ _)).
set (mz := Fplus_naive sx mx ex sy my ey ez).
simpl in Hp.
fold mz in Hp.
rewrite <- Hp.
generalize (binary_normalize_correct m mz ez szero).
simpl.
case Rlt_bool_spec ; intros Hz.
intros [H1 [H2 H3]].
apply (conj H1).
apply (conj H2).
rewrite H3.
case Rcompare_spec ; try easy.
intros Hz'.
rewrite Hz' in Hp.
apply eq_sym, Rplus_opp_r_uniq in Hp.
rewrite <- F2R_Zopp in Hp.
eapply canonical_unique in Hp.
inversion Hp.
clear -H0.
destruct sy, sx, m ; easy.
now apply canonical_bounded.
rewrite <- cond_Zopp_negb.
now apply canonical_bounded.
intros Vz.
rewrite Hp in Hz.
assert (Sz := sign_plus_overflow m sx mx ex sy my ey Hx Hy Hz).
split.
rewrite Vz.
apply f_equal.
now rewrite Hp.
apply Sz.
Qed.

Definition Bminus m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy =>
    if Bool.eqb sx (negb sy) then x else B754_nan
  | B754_infinity _, _ => x
  | _, B754_infinity sy => B754_infinity (negb sy)
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx (negb sy) then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, B754_finite sy my ey Hy => B754_finite (negb sy) my ey Hy
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Z.min ex ey in
    binary_normalize m (Fplus_naive sx mx ex (negb sy) my ey ez)
      ez (match m with mode_DN => true | _ => false end)
  end.

Theorem Bminus_correct :
  forall m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x - B2R y))) (bpow radix2 emax) then
    B2R (Bminus m x y) = round radix2 fexp (round_mode m) (B2R x - B2R y) /\
    is_finite (Bminus m x y) = true /\
    Bsign (Bminus m x y) =
      match Rcompare (B2R x - B2R y) 0 with
        | Eq => match m with mode_DN => orb (Bsign x) (negb (Bsign y))
                                 | _ => andb (Bsign x) (negb (Bsign y)) end
        | Lt => true
        | Gt => false
      end
  else
    (B2SF (Bminus m x y) = binary_overflow m (Bsign x) /\ Bsign x = negb (Bsign y)).
Proof using .
Proof with auto with typeclass_instances.
intros m x y Fx Fy.
generalize (Bplus_correct m x (Bopp y) Fx).
rewrite is_finite_Bopp, B2R_Bopp.
intros H.
specialize (H Fy).
rewrite <- Bsign_Bopp.
destruct x as [| | |sx mx ex Hx], y as [| | |sy my ey Hy] ; try easy.
now clear -Fy; destruct y as [ | | | ].
Qed.

Definition Bfma_szero m (x y z: binary_float) : bool :=
  let s_xy := xorb (Bsign x) (Bsign y) in
  if Bool.eqb s_xy (Bsign z) then s_xy
  else match m with mode_DN => true | _ => false end.

Definition Bfma m (x y z: binary_float) :=
  match x, y with
  | B754_nan, _ | _, B754_nan
  | B754_infinity _, B754_zero _
  | B754_zero _, B754_infinity _ =>

      B754_nan
  | B754_infinity sx, B754_infinity sy
  | B754_infinity sx, B754_finite sy _ _ _
  | B754_finite sx _ _ _, B754_infinity sy =>
      let s := xorb sx sy in

      match z with
      | B754_nan => B754_nan
      | B754_infinity sz => if Bool.eqb s sz then z else B754_nan
      | _ => B754_infinity s
      end
  | B754_finite sx _ _ _, B754_zero sy
  | B754_zero sx, B754_finite sy _ _ _
  | B754_zero sx, B754_zero sy =>

      match z with
      | B754_nan => B754_nan
      | B754_zero _ => B754_zero (Bfma_szero m x y z)
      | _ => z
      end
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>

      match z with
      | B754_nan => B754_nan
      | B754_infinity sz => z
      | B754_zero _ =>
         let X := Float radix2 (cond_Zopp sx (Zpos mx)) ex in
         let Y := Float radix2 (cond_Zopp sy (Zpos my)) ey in
         let '(Float _ mr er) := Fmult X Y in
         binary_normalize m mr er (Bfma_szero m x y z)
      | B754_finite sz mz ez _ =>
         let X := Float radix2 (cond_Zopp sx (Zpos mx)) ex in
         let Y := Float radix2 (cond_Zopp sy (Zpos my)) ey in
         let Z := Float radix2 (cond_Zopp sz (Zpos mz)) ez in
         let '(Float _ mr er) := Fplus (Fmult X Y) Z in
         binary_normalize m mr er (Bfma_szero m x y z)
      end
  end.

Theorem Bfma_correct:
  forall m x y z,
  is_finite x = true ->
  is_finite y = true ->
  is_finite z = true ->
  let res := (B2R x * B2R y + B2R z)%R in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) res)) (bpow radix2 emax) then
    B2R (Bfma m x y z) = round radix2 fexp (round_mode m) res /\
    is_finite (Bfma m x y z) = true /\
    Bsign (Bfma m x y z) =
      match Rcompare res 0 with
        | Eq => Bfma_szero m x y z
        | Lt => true
        | Gt => false
      end
  else
    B2SF (Bfma m x y z) = binary_overflow m (Rlt_bool res 0).
Proof using .
  intros.
pattern (Bfma m x y z).
  match goal with |- ?p ?x => set (PROP := p) end.
  set (szero := Bfma_szero m x y z).
  assert (BINORM: forall mr er, F2R (Float radix2 mr er) = res ->
       PROP (binary_normalize m mr er szero)).
  {
 intros mr er E.
    specialize (binary_normalize_correct m mr er szero).
    change (FLT_exp (3 - emax - prec) prec) with fexp.
rewrite E.
tauto.
  }
  set (add_zero :=
    match z with
    | B754_nan => B754_nan
    | B754_zero sz => B754_zero szero
    | _ => z
    end).
  assert (ADDZERO: B2R x = 0%R \/ B2R y = 0%R -> PROP add_zero).
  {
    intros Z.
    assert (RES: res = B2R z).
    {
 unfold res.
destruct Z as [E|E]; rewrite E, ?Rmult_0_l, ?Rmult_0_r, Rplus_0_l; auto.
}
    unfold PROP, add_zero; destruct z as [ sz | sz | | sz mz ez Bz]; try discriminate.
  -
 simpl in RES; rewrite RES; rewrite round_0 by apply valid_rnd_round_mode.
    rewrite Rlt_bool_true.
split.
reflexivity.
split.
reflexivity.
    rewrite Rcompare_Eq by auto.
reflexivity.
    rewrite Rabs_R0; apply bpow_gt_0.
  -
 rewrite RES, round_generic, Rlt_bool_true.
    split.
reflexivity.
split.
reflexivity.
    unfold B2R.
destruct sz.
    rewrite Rcompare_Lt.
auto.
apply F2R_lt_0.
reflexivity.
    rewrite Rcompare_Gt.
auto.
apply F2R_gt_0.
reflexivity.
    apply abs_B2R_lt_emax.
apply valid_rnd_round_mode.
apply generic_format_B2R.
  }
  destruct x as [ sx | sx | | sx mx ex Bx];
  destruct y as [ sy | sy | | sy my ey By];
  try discriminate.
-
 apply ADDZERO; auto.
-
 apply ADDZERO; auto.
-
 apply ADDZERO; auto.
-
 destruct z as [ sz | sz | | sz mz ez Bz]; try discriminate; unfold Bfma.
+
 set (X := Float radix2 (cond_Zopp sx (Zpos mx)) ex).
  set (Y := Float radix2 (cond_Zopp sy (Zpos my)) ey).
  destruct (Fmult X Y) as [mr er] eqn:FRES.
  apply BINORM.
unfold res.
rewrite <- FRES, F2R_mult, Rplus_0_r.
auto.
+
 set (X := Float radix2 (cond_Zopp sx (Zpos mx)) ex).
  set (Y := Float radix2 (cond_Zopp sy (Zpos my)) ey).
  set (Z := Float radix2 (cond_Zopp sz (Zpos mz)) ez).
  destruct (Fplus (Fmult X Y) Z) as [mr er] eqn:FRES.
  apply BINORM.
unfold res.
rewrite <- FRES, F2R_plus, F2R_mult.
auto.
Qed.

Lemma Bdiv_correct_aux :
  forall m sx mx ex sy my ey,
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  let z :=
    let '(mz, ez, lz) := SFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey in
    binary_round_aux m (xorb sx sy) mz ez lz in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (x / y))) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode m) (x / y) /\
    is_finite_SF z = true /\ sign_SF z = xorb sx sy
  else
    z = binary_overflow m (xorb sx sy).
Proof using prec_gt_0_ prec_lt_emax_.
intros m sx mx ex sy my ey.
unfold SFdiv_core_binary.
rewrite 2!Zdigits2_Zdigits.
set (e' := Z.min _ _).
match goal with |- context [Z.div_eucl ?m _] => set (mx' := m) end.
generalize (Fdiv_core_correct radix2 (Zpos mx) ex (Zpos my) ey e' eq_refl eq_refl).
unfold Fdiv_core.
rewrite Zle_bool_true by apply Z.le_min_r.
assert (mx' = Zpos mx * Zpower radix2 (ex - ey - e'))%Z as <-.
{
 unfold mx'.
  destruct (ex - ey - e')%Z as [|p|p].
  now rewrite Zmult_1_r.
  now rewrite Z.shiftl_mul_pow2.
  easy.
}
clearbody mx'.
destruct Z.div_eucl as [q r].
intros Bz.
assert (xorb sx sy = Rlt_bool (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) *
  / F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey)) 0) as ->.
{
 apply eq_sym.
case sy ; simpl.
change (Zneg my) with (Z.opp (Zpos my)).
rewrite F2R_Zopp.
rewrite <- Ropp_inv_permute.
rewrite Ropp_mult_distr_r_reverse.
case sx ; simpl.
apply Rlt_bool_false.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rmult_le_pos.
rewrite <- F2R_opp.
now apply F2R_ge_0.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0.
apply Rlt_bool_true.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
now apply F2R_gt_0.
apply Rinv_0_lt_compat.
now apply F2R_gt_0.
apply Rgt_not_eq.
now apply F2R_gt_0.
case sx.
apply Rlt_bool_true.
rewrite F2R_Zopp.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
now apply F2R_gt_0.
apply Rinv_0_lt_compat.
now apply F2R_gt_0.
apply Rlt_bool_false.
apply Rmult_le_pos.
now apply F2R_ge_0.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0.
}
unfold Rdiv.
apply binary_round_aux_correct'.
-
 apply Rmult_integral_contrapositive_currified.
  now apply F2R_neq_0 ; case sx.
  apply Rinv_neq_0_compat.
  now apply F2R_neq_0 ; case sy.
-
 rewrite Rabs_mult, Rabs_Rinv.
  +
 rewrite <- 2!F2R_Zabs, 2!abs_cond_Zopp; simpl.
    replace (SpecFloat.new_location _ _) with (Bracket.new_location (Z.pos my) r loc_Exact);
      [exact Bz|].
    case my as [p|p|]; [reflexivity| |reflexivity].
    unfold Bracket.new_location, SpecFloat.new_location; simpl.
    unfold Bracket.new_location_even, SpecFloat.new_location_even; simpl.
    now case Zeq_bool; [|case r as [|rp|rp]; case Z.compare].
  +
 now apply F2R_neq_0 ; case sy.
-
 rewrite <- cexp_abs, Rabs_mult, Rabs_Rinv.
  rewrite 2!F2R_cond_Zopp, 2!abs_cond_Ropp, <- Rabs_Rinv.
  rewrite <- Rabs_mult, cexp_abs.
  apply Z.le_trans with (1 := Z.le_min_l _ _).
  apply FLT_exp_monotone.
  now apply mag_div_F2R.
  now apply F2R_neq_0.
  now apply F2R_neq_0 ; case sy.
Qed.

Definition Bdiv m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy => B754_nan
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_infinity sx, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_finite sx _ _ _, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_nan
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>
    SF2B _ (proj1 (Bdiv_correct_aux m sx mx ex sy my ey))
  end.

Theorem Bdiv_correct :
  forall m x y,
  B2R y <> 0%R ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x / B2R y))) (bpow radix2 emax) then
    B2R (Bdiv m x y) = round radix2 fexp (round_mode m) (B2R x / B2R y) /\
    is_finite (Bdiv m x y) = is_finite x /\
    (is_nan (Bdiv m x y) = false ->
      Bsign (Bdiv m x y) = xorb (Bsign x) (Bsign y))
  else
    B2SF (Bdiv m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof using .
intros m x [sy|sy| |sy my ey Hy] Zy ; try now elim Zy.
revert x.
unfold Rdiv.
intros [sx|sx| |sx mx ex Hx] ;
  try ( rewrite Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ simpl ; try easy ; now rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan | apply bpow_gt_0 | auto with typeclass_instances ] ).
simpl.
case Bdiv_correct_aux.
intros H1.
unfold Rdiv.
case Rlt_bool.
intros (H2, (H3, H4)).
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
rewrite Bsign_SF2B.
congruence.
intros H2.
now rewrite B2SF_SF2B.
Qed.

Lemma Bsqrt_correct_aux :
  forall m mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (Zpos mx) ex) in
  let z :=
    let '(mz, ez, lz) := SFsqrt_core_binary prec emax (Zpos mx) ex in
    binary_round_aux m false mz ez lz in
  valid_binary z = true /\
  SF2R radix2 z = round radix2 fexp (round_mode m) (sqrt x) /\
  is_finite_SF z = true /\ sign_SF z = false.
Proof using prec_gt_0_ prec_lt_emax_.
Proof with auto with typeclass_instances.
intros m mx ex Hx.
unfold SFsqrt_core_binary.
rewrite Zdigits2_Zdigits.
set (e' := Z.min _ _).
assert (2 * e' <= ex)%Z as He.
{
 assert (e' <= Z.div2 ex)%Z by apply Z.le_min_r.
  rewrite (Zdiv2_odd_eqn ex).
  destruct Z.odd ; lia.
}
generalize (Fsqrt_core_correct radix2 (Zpos mx) ex e' eq_refl He).
unfold Fsqrt_core.
set (mx' := match (ex - 2 * e')%Z with Z0 => _ | _ => _ end).
assert (mx' = Zpos mx * Zpower radix2 (ex - 2 * e'))%Z as <-.
{
 unfold mx'.
  destruct (ex - 2 * e')%Z as [|p|p].
  now rewrite Zmult_1_r.
  now rewrite Z.shiftl_mul_pow2.
  easy.
}
clearbody mx'.
destruct Z.sqrtrem as [mz r].
set (lz := if Zeq_bool r 0 then _ else _).
clearbody lz.
intros Bz.
refine (_ (binary_round_aux_correct' m (sqrt (F2R (Float radix2 (Zpos mx) ex))) mz e' lz _ _ _)) ; cycle 1.
  now apply Rgt_not_eq, sqrt_lt_R0, F2R_gt_0.
  rewrite Rabs_pos_eq.
  exact Bz.
  apply sqrt_ge_0.
  apply Z.le_trans with (1 := Z.le_min_l _ _).
  apply FLT_exp_monotone.
  rewrite mag_sqrt_F2R by easy.
  apply Z.le_refl.
rewrite Rlt_bool_false by apply sqrt_ge_0.
rewrite Rlt_bool_true.
easy.
rewrite Rabs_pos_eq.
refine (_ (relative_error_FLT_ex radix2 emin prec (prec_gt_0 prec) (round_mode m) (sqrt (F2R (Float radix2 (Zpos mx) ex))) _)).
fold fexp.
intros (eps, (Heps, Hr)).
change fexp with (FLT_exp emin prec).
rewrite Hr.
assert (Heps': (Rabs eps < 1)%R).
apply Rlt_le_trans with (1 := Heps).
fold (bpow radix2 0).
apply bpow_le.
generalize (prec_gt_0 prec).
clear ; lia.
apply Rsqr_incrst_0.
3: apply bpow_ge_0.
rewrite Rsqr_mult.
rewrite Rsqr_sqrt.
2: now apply F2R_ge_0.
unfold Rsqr.
apply Rmult_ge_0_gt_0_lt_compat.
apply Rle_ge.
apply Rle_0_sqr.
apply bpow_gt_0.
now apply bounded_lt_emax.
apply Rlt_le_trans with 4%R.
apply (Rsqr_incrst_1 _ 2).
apply Rplus_lt_compat_l.
apply (Rabs_lt_inv _ _ Heps').
rewrite <- (Rplus_opp_r 1).
apply Rplus_le_compat_l.
apply Rlt_le.
apply (Rabs_lt_inv _ _ Heps').
now apply IZR_le.
change 4%R with (bpow radix2 2).
apply bpow_le.
generalize (prec_gt_0 prec) (prec_lt_emax prec emax).
clear ; lia.
apply Rmult_le_pos.
apply sqrt_ge_0.
rewrite <- (Rplus_opp_r 1).
apply Rplus_le_compat_l.
apply Rlt_le.
apply (Rabs_lt_inv _ _ Heps').
rewrite Rabs_pos_eq.
2: apply sqrt_ge_0.
apply Rsqr_incr_0.
2: apply bpow_ge_0.
2: apply sqrt_ge_0.
rewrite Rsqr_sqrt.
2: now apply F2R_ge_0.
apply Rle_trans with (bpow radix2 emin).
unfold Rsqr.
rewrite <- bpow_plus.
apply bpow_le.
unfold emin.
generalize (prec_lt_emax prec emax).
clear ; lia.
apply generic_format_ge_bpow with fexp.
intros.
apply Z.le_max_r.
now apply F2R_gt_0.
apply generic_format_canonical.
now apply (canonical_bounded false).
apply round_ge_generic...
apply generic_format_0.
apply sqrt_ge_0.
Qed.

Definition Bsqrt m x :=
  match x with
  | B754_nan => B754_nan
  | B754_infinity false => x
  | B754_infinity true => B754_nan
  | B754_finite true _ _ _ => B754_nan
  | B754_zero _ => x
  | B754_finite sx mx ex Hx =>
    SF2B _ (proj1 (Bsqrt_correct_aux m mx ex Hx))
  end.

Theorem Bsqrt_correct :
  forall m x,
  B2R (Bsqrt m x) = round radix2 fexp (round_mode m) (sqrt (B2R x)) /\
  is_finite (Bsqrt m x) = match x with B754_zero _ => true | B754_finite false _ _ _ => true | _ => false end /\
  (is_nan (Bsqrt m x) = false -> Bsign (Bsqrt m x) = Bsign x).
Proof using .
intros m [sx|[|]| |sx mx ex Hx] ;
  try ( simpl ; rewrite sqrt_0, round_0, ?B2R_build_nan, ?is_finite_build_nan, ?is_nan_build_nan ; intuition auto with typeclass_instances ; easy).
simpl.
case Bsqrt_correct_aux.
intros H1 (H2, (H3, H4)).
case sx.
refine (conj _ (conj (refl_equal false) _)).
apply sym_eq.
unfold sqrt.
case Rcase_abs.
intros _.
apply round_0.
auto with typeclass_instances.
intros H.
elim Rge_not_lt with (1 := H).
now apply F2R_lt_0.
easy.
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
intros _.
now rewrite Bsign_SF2B.
Qed.

Definition SFnearbyint_binary_aux m sx mx ex :=
  if (0 <=? ex)%Z then ((Z.pos mx) * 2 ^ ex)%Z else
  let mrs := {| shr_m := Z.pos mx; shr_r := false; shr_s := false |} in
  let mrs' := if (ex <? - prec)%Z then
    {| shr_m := Z0; shr_r := false; shr_s := true |} else
    fst (shr mrs ex (- ex)) in
  let l' := loc_of_shr_record mrs' in
  let mx' := shr_m mrs' in
  choice_mode m sx mx' l'.

Definition SFnearbyint_binary m sx mx ex :=
  if (0 <=? ex)%Z then S754_finite sx mx ex else
  let mx'' := SFnearbyint_binary_aux m sx mx ex in
  match mx'' with
  | Z.pos n =>
    let (mx''', ex''') := shl_align_fexp n 0 in
    S754_finite sx mx''' ex'''
  | Z.neg n => S754_nan
  | Z0      => S754_zero sx
  end.

Lemma Bnearbyint_correct_aux :
  forall md sx mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let z := SFnearbyint_binary md sx mx ex in
  valid_binary z = true /\
  SF2R radix2 z = (round radix2 (FIX_exp 0) (round_mode md) x) /\
  is_finite_SF z = true /\ (is_nan_SF z = false -> sign_SF z = sx).
Proof using prec_lt_emax_.
  intros md sx mx ex Hmxex.
simpl.
  set (mrs' := if (ex <? - prec)%Z then
    {| shr_m := Z0; shr_r := false; shr_s := true |} else
    fst (shr {| shr_m := Z.pos mx; shr_r := false; shr_s := false |} ex (- ex))).
  assert (mrs'_simpl : mrs' = fst (shr {| shr_m := Z.pos mx; shr_r := false; shr_s := false |} ex (- ex))).
  {
 unfold mrs'.
case Zlt_bool_spec; [ | easy].
intros Hex1.
symmetry.
    apply shr_limit; simpl; [now left |].
apply Z.lt_le_trans with (radix2 ^ prec)%Z.
    -
 unfold bounded, canonical_mantissa, fexp in Hmxex.
apply andb_prop in Hmxex.
      destruct Hmxex as [Hmxex _].
apply Zeq_bool_eq in Hmxex.
      rewrite Zpos_digits2_pos in Hmxex.
apply Z.eq_le_incl in Hmxex.
      apply Z.max_lub_l in Hmxex.
      assert (Hmx : (Zdigits radix2 (Z.pos mx) <= prec)%Z) by lia.
      replace (Z.pos mx) with (Z.abs (Z.pos mx)); [| now simpl].
      now apply Zpower_gt_Zdigits.
    -
 apply Zpower_le.
lia.
    }
  assert (mrs'_ge_0 : (ex < 0)%Z -> (0 <= shr_m mrs')%Z).

  {
 intros Hex.
    rewrite mrs'_simpl.
    apply le_shr_le.
    easy.
    lia.
}
  repeat split; unfold SFnearbyint_binary, SFnearbyint_binary_aux;
  case Zle_bool_spec; intros Hex0; fold mrs'; auto.

  -
 destruct choice_mode eqn:H0; auto.
    unfold shl_align_fexp.
destruct shl_align as [mx''' ex'''] eqn:H1; simpl.
    unfold bounded, canonical_mantissa in Hmxex.
apply andb_prop in Hmxex.
    destruct Hmxex as [Hmxex Hex'].
    unfold bounded, canonical_mantissa.
    assert (A : (fexp (Z.pos (digits2_pos p) + 0) <= 0)%Z).
    {
 rewrite Z.add_0_r in *.
rewrite Zpos_digits2_pos in *.
      destruct (le_choice_mode_le md sx (shr_m mrs') (loc_of_shr_record mrs')) as [H4 H5].
      rewrite H0 in H4, H5.
      transitivity (fexp (Zdigits radix2 (shr_m mrs' + 1)));
        [apply fexp_monotone; apply Zdigits_le; [lia | assumption] |
      transitivity (fexp ((Zdigits radix2 (shr_m mrs') + 1)));
        [apply fexp_monotone; apply Zdigits_succ_le; now apply mrs'_ge_0 |
      transitivity (fexp (Zdigits radix2 ((shr_m {| shr_m := Z.pos mx; shr_r := false; shr_s := false |}) / (2 ^ (- ex))) + 1));
        [apply fexp_monotone; apply Zplus_le_compat_r; apply Zdigits_le; simpl; auto | simpl
      ]]].
      -
 apply Zdiv.Zdiv_le_lower_bound; [lia |].
rewrite Z.mul_comm.
rewrite mrs'_simpl.
        apply le_shr_le; simpl; lia.
      -
 transitivity (fexp (Zdigits radix2 (Z.pos mx / 2 ^ 1) + 1)).
        +
 apply fexp_monotone.
apply Zplus_le_compat_r.
apply Zdigits_le.
          *
 apply Z.div_pos; lia.
          *
 apply Z.opp_pos_neg in Hex0.
apply Z.div_le_compat_l; [lia |].
            split; [lia |].
apply Z.pow_le_mono_r; lia.
        +
 rewrite Zdigits_div_Zpower; [| lia |].
          *
 rewrite Z.sub_add.
apply Zeq_bool_eq in Hmxex.
unfold fexp in *.
            rewrite Z.max_lub_iff.
split; [| lia].
apply (Zplus_le_reg_l _ _ ex).
            rewrite Zplus_0_r.
rewrite Z.add_sub_assoc.
rewrite Z.add_comm.
            rewrite <-Hmxex at 2.
apply Z.le_max_l.
          *
 split; [lia |].
replace 1%Z with (Zdigits radix2 (Z.pos 1)); [| easy].
            apply Zdigits_le; lia.
}
    refine (_ (shl_align_correct' p 0 (fexp (Z.pos (digits2_pos p) + 0)) _)).
    +
 rewrite H1.
intros [H2 H3].
rewrite <-H3 in H2.
      apply andb_true_intro; split.
      *
 apply Zeq_bool_true.
rewrite H3 at 2.
rewrite !Zpos_digits2_pos.
        rewrite <-!mag_F2R_Zdigits; [| lia | lia].
        now apply (f_equal (fun f => fexp (mag radix2 f))).
      *
 apply Zle_bool_true.
rewrite H3.
transitivity 0%Z; [assumption|].
        apply Zle_minus_le_0.
apply Z.lt_le_incl.
apply prec_lt_emax_.
    +
 assumption.

  -
 symmetry.
apply round_generic; auto.
    +
 apply valid_rnd_round_mode.
    +
 apply generic_format_FIX.
      exists (Float radix2 (cond_Zopp sx (Z.pos mx) * Z.pow 2 ex) 0); auto.
      simpl.
rewrite <-(Z.sub_0_r ex) at 2.
now apply F2R_change_exp.

  -
 rewrite round_trunc_sign_any_correct with (choice := choice_mode md)
      (m := Z.pos mx) (e := ex) (l := loc_Exact).
    +
 fold (shr_record_of_loc (Z.pos mx) loc_Exact) in mrs'_simpl.
rewrite mrs'_simpl.
      replace (- ex)%Z with (FIX_exp 0 (Zdigits2 (Z.pos mx) + ex) - ex)%Z; [| auto].
      rewrite !shr_truncate; [ | apply FIX_exp_valid | easy ].
      destruct truncate as (rec, loc) eqn:H0.
destruct rec as (z0, z1) eqn:H1.
      simpl.
rewrite shr_m_shr_record_of_loc.
rewrite loc_of_shr_record_of_loc.
      replace (Rlt_bool (F2R {| Fnum := cond_Zopp sx (Z.pos mx); Fexp := ex |}) 0) with sx.
      *
 destruct choice_mode as [| p0 | p0] eqn:H2.
        --
 simpl.
symmetry.
rewrite cond_Zopp_0.
apply F2R_0.
        --
 generalize (shl_align_fexp_correct p0 0).
           destruct shl_align_fexp as (p1, z2).
simpl.
intros [H3 _].
           rewrite !F2R_cond_Zopp.
apply f_equal.
simpl in H0.
           rewrite Zlt_bool_true in H0; [| lia].
           rewrite Z.add_opp_diag_r in H0.
injection H0.
           intros _ H4 _.
now rewrite <-H4.
        --
 destruct (le_choice_mode_le md sx z0 loc) as [H3 _].
           rewrite H2 in H3.
simpl in H0.
           rewrite Zlt_bool_true in H0 by lia.
           injection H0.
intros _ _ H4.
           elim (Zle_not_lt 0 z0).
           rewrite <- H4.
           apply Z_div_pos.
           apply Z.lt_gt, (Zpower_gt_0 radix2).
lia.
           easy.
           now apply Z.le_lt_trans with (1 := H3).
      *
 rewrite F2R_cond_Zopp.
apply eq_sym, Rlt_bool_cond_Ropp.
        now apply F2R_gt_0.
    +
 apply FIX_exp_valid.
    +
 apply valid_rnd_round_mode.
    +
 apply round_mode_choice_mode.
    +
 rewrite <-F2R_abs.
simpl.
rewrite abs_cond_Zopp.
simpl.
now apply inbetween_Exact.
    +
 auto.

  -
 destruct choice_mode eqn:H0; [easy | now destruct shl_align_fexp |].
    apply mrs'_ge_0 in Hex0.
    destruct (le_choice_mode_le md sx (shr_m mrs') (loc_of_shr_record mrs')) as [H2 H3].
    rewrite H0 in H2, H3.
lia.

  -
 destruct choice_mode eqn:H0; [easy | now destruct shl_align_fexp | easy].
Qed.

Definition Bnearbyint md (x : binary_float) :=
  match x with
  | B754_nan => B754_nan
  | B754_zero s => B754_zero s
  | B754_infinity s => B754_infinity s
  | B754_finite s m e H =>
    SF2B _ (proj1 (Bnearbyint_correct_aux md s m e H))
  end.

Theorem Bnearbyint_correct :
  forall md x,
  B2R (Bnearbyint md x) = round radix2 (FIX_exp 0) (round_mode md) (B2R x) /\
  is_finite (Bnearbyint md x) = is_finite x /\
  (is_nan (Bnearbyint md x) = false -> Bsign (Bnearbyint md x) = Bsign x).
Proof using .
  intros md.
  assert (round_0_ : 0%R = (round radix2 (FIX_exp 0) (round_mode md) 0)).
  {
 symmetry.
    apply round_0.
    apply valid_rnd_round_mode.
}
  intros [sx | sx | | sx mx ex Hx]; try easy.
  unfold Bnearbyint.
destruct Bnearbyint_correct_aux as [H1 [H2 [H3 H4]]].
repeat split.
  -
 rewrite B2R_SF2B.
easy.
  -
 rewrite is_finite_SF2B.
easy.
  -
 rewrite is_nan_SF2B.
rewrite Bsign_SF2B.
easy.
Qed.

Definition Btrunc (x : binary_float) :=
  match x with
  | B754_finite s m e _ =>
    cond_Zopp s (SFnearbyint_binary_aux mode_ZR s m e)
  | _ => 0%Z
  end.

Theorem Btrunc_correct :
  forall x,
  IZR (Btrunc x) = round radix2 (FIX_exp 0) Ztrunc (B2R x).
Proof using prec_lt_emax_.
  assert (round_0_to_0 : 0%R = (round radix2 (FIX_exp 0) Ztrunc 0)).
  {
 symmetry.
apply round_0.
apply valid_rnd_ZR.
}
  intros [sx | sx | | sx mx ex Hx]; simpl; try assumption.
  destruct (Bnearbyint_correct_aux mode_ZR sx mx ex) as [_ [H0 _]]; [easy |].
  simpl round_mode in H0.
rewrite <-H0.
unfold SFnearbyint_binary, SFnearbyint_binary_aux.
  set (mrs' :=
   (if (ex <? - prec)%Z
    then {| shr_m := 0; shr_r := false; shr_s := true |}
    else fst (shr {| shr_m := Z.pos mx; shr_r := false; shr_s := false |} ex (- ex)))).
  fold mrs'.
  set (n := choice_mode mode_ZR sx (shr_m mrs') (loc_of_shr_record mrs')).
  fold n.
case Zle_bool_spec; intros H1.
  -
 simpl SF2R.
unfold F2R.
simpl Fnum.
simpl bpow.
destruct sx; unfold cond_Zopp;
    [rewrite Zopp_mult_distr_l |]; rewrite mult_IZR; apply f_equal; destruct ex; easy.
  -
 destruct n as [ | p | p] eqn:H2; [now destruct sx | |].
    +
 generalize (shl_align_fexp_correct p 0).
destruct shl_align_fexp.
      simpl SF2R.
unfold F2R.
simpl.
intros [H3 H4].
rewrite Rmult_1_r in H3.
      destruct sx; unfold cond_Zopp; [| assumption].
      rewrite 2Ropp_Ropp_IZR.
rewrite <-Ropp_mult_distr_l.
now rewrite H3.
    +
 unfold n in H2.
      destruct (le_choice_mode_le mode_ZR sx (shr_m mrs') (loc_of_shr_record mrs')) as [H3 _].
      rewrite H2 in H3.
unfold mrs' in H3.
case (ex <? - prec)%Z in H3.
      *
 simpl in H3.
lia.
      *
 elim (Zle_not_lt 0 (Z.neg p)).
2: easy.
        apply Z.le_trans with (2 := H3).
        apply le_shr_le.
        easy.
        lia.
Qed.

Definition Bone := SF2B _ (proj1 (binary_round_correct mode_NE false 1 0)).

Theorem Bone_correct : B2R Bone = 1%R.
Proof using .
unfold Bone; simpl.
set (Hr := binary_round_correct _ _ _ _).
unfold Hr; rewrite B2R_SF2B.
destruct Hr as (Vz, Hr).
revert Hr.
fold emin; simpl.
rewrite round_generic; [|now apply valid_rnd_N|].
-
 unfold F2R; simpl; rewrite Rmult_1_r.
  rewrite Rlt_bool_true.
  +
 now intros (Hr, Hr'); rewrite Hr.
  +
 rewrite Rabs_R1.
    change 1%R with (bpow radix2 0); apply bpow_lt.
    generalize (prec_gt_0 prec) (prec_lt_emax prec emax).
    lia.
-
 apply generic_format_F2R; intros _.
  unfold cexp, fexp, FLT_exp, F2R; simpl; rewrite Rmult_1_r, mag_1.
  unfold emin.
  generalize (prec_gt_0 prec) (prec_lt_emax prec emax).
  lia.
Qed.

Theorem is_finite_strict_Bone :
  is_finite_strict Bone = true.
Proof using .
apply is_finite_strict_B2R.
rewrite Bone_correct.
apply R1_neq_R0.
Qed.

Theorem is_nan_Bone :
  is_nan Bone = false.
Proof using .
unfold Bone.
rewrite is_nan_SF2B.
apply is_nan_binary_round.
Qed.

Theorem is_finite_Bone :
  is_finite Bone = true.
Proof using .
generalize is_finite_strict_Bone.
now destruct Bone.
Qed.

Theorem Bsign_Bone :
  Bsign Bone = false.
Proof using .
generalize Bone_correct is_finite_strict_Bone.
destruct Bone as [sx|sx| |[|] mx ex Bx] ; try easy.
intros H _.
contradict H.
apply Rlt_not_eq, Rlt_trans with (2 := Rlt_0_1).
now apply F2R_lt_0.
Qed.

Lemma Bmax_float_proof :
  valid_binary
    (S754_finite false (shift_pos (Z.to_pos prec) 1 - 1) (emax - prec))
  = true.
Proof using prec_gt_0_ prec_lt_emax_.
unfold valid_binary, bounded; apply andb_true_intro; split.
-
 unfold canonical_mantissa; apply Zeq_bool_true.
  set (p := Z.pos (digits2_pos _)).
  assert (H : p = prec).
  {
 unfold p; rewrite Zpos_digits2_pos, Pos2Z.inj_sub.
    -
 rewrite shift_pos_correct, Z.mul_1_r.
      assert (P2pm1 : (0 <= 2 ^ prec - 1)%Z).
      {
 apply Z.lt_le_pred.
        apply (Zpower_gt_0 radix2).
        now apply Zlt_le_weak.
}
      apply Zdigits_unique ;
        rewrite Z.pow_pos_fold, Z2Pos.id; [|exact prec_gt_0_]; simpl; split.
      +
 rewrite (Z.abs_eq _ P2pm1).
        apply Z.lt_le_pred.
        apply (Zpower_lt radix2).
        now apply Zlt_le_weak.
        apply Z.lt_pred_l.
      +
 rewrite Z.abs_eq by easy.
        apply Z.lt_pred_l.
    -
 change (Z.pos 1 < Z.pos (shift_pos (Z.to_pos prec) 1))%Z.
      rewrite shift_pos_correct, Z.mul_1_r, Z.pow_pos_fold.
      rewrite Z2Pos.id; [|exact prec_gt_0_].
      now apply (Zpower_gt_1 radix2).
}
  rewrite H.
  ring_simplify (prec + (emax - prec))%Z.
  apply fexp_emax.
-
 apply Zle_bool_true, Z.le_refl.
Qed.

Definition Bmax_float := SF2B _ Bmax_float_proof.

Definition Bnormfr_mantissa x := SFnormfr_mantissa prec (B2SF x).

Lemma Bnormfr_mantissa_correct :
  forall x,
  (/ 2 <= Rabs (B2R x) < 1)%R ->
  match x with
  | B754_finite _ m e _ =>
    Bnormfr_mantissa x = N.pos m
    /\ Z.pos (digits2_pos m) = prec /\ (e = - prec)%Z
  | _ => False
  end.
Proof using prec_lt_emax_.
intro x.
destruct x as [s|s| |s m e B]; [now simpl; rewrite Rabs_R0; lra..| ].
unfold Bnormfr_mantissa, SFnormfr_mantissa; simpl.
intro Hx.
cut (e = -prec /\ Z.pos (digits2_pos m) = prec)%Z.
{
 now intros [-> ->]; rewrite Z.eqb_refl.
}
revert Hx.
change (/ 2)%R with (bpow radix2 (0 - 1)); change 1%R with (bpow radix2 0).
intro H; generalize (mag_unique _ _ _ H); clear H.
rewrite Float_prop.mag_F2R_Zdigits; [ |now case s].
replace (Digits.Zdigits _ _)
  with (Digits.Zdigits radix2 (Z.pos m)); [ |now case s].
clear s.
rewrite <-Digits.Zpos_digits2_pos.
intro He; replace e with (e - 0)%Z by ring; rewrite <-He.
cut (Z.pos (digits2_pos m) = prec)%Z.
{
 now intro H; split; [ |exact H]; ring_simplify; rewrite H.
}
revert B; unfold bounded, canonical_mantissa.
intro H; generalize (andb_prop _ _ H); clear H; intros [H _]; revert H.
intro H; generalize (Zeq_bool_eq _ _ H); clear H.
unfold fexp, emin.
unfold Prec_gt_0 in prec_gt_0_; unfold Prec_lt_emax in prec_lt_emax_.
lia.
Qed.

Definition Bldexp mode f e :=
  match f with
  | B754_finite sx mx ex _ =>
    SF2B _ (proj1 (binary_round_correct mode sx mx (ex+e)))
  | _ => f
  end.

Theorem is_nan_Bldexp :
  forall mode x e,
  is_nan (Bldexp mode x e) = is_nan x.
Proof using .
intros mode [sx|sx| |sx mx ex Bx] e ; try easy.
unfold Bldexp.
rewrite is_nan_SF2B.
apply is_nan_binary_round.
Qed.

Theorem Bldexp_correct :
  forall m (f : binary_float) e,
  if Rlt_bool
       (Rabs (round radix2 fexp (round_mode m) (B2R f * bpow radix2 e)))
       (bpow radix2 emax) then
    (B2R (Bldexp m f e)
     = round radix2 fexp (round_mode m) (B2R f * bpow radix2 e))%R /\
    is_finite (Bldexp m f e) = is_finite f /\
    Bsign (Bldexp m f e) = Bsign f
  else
    B2SF (Bldexp m f e) = binary_overflow m (Bsign f).
Proof using .
intros m f e.
case f.
-
 intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
-
 intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
-
 simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
-
 intros s mf ef Hmef.
  case (Rlt_bool_spec _ _); intro Hover.
  +
 unfold Bldexp; rewrite B2R_SF2B, is_finite_SF2B, Bsign_SF2B.
    simpl; unfold F2R; simpl; rewrite Rmult_assoc, <-bpow_plus.
    destruct (binary_round_correct m s mf (ef + e)) as (Hf, Hr).
    fold emin in Hr; simpl in Hr; rewrite Rlt_bool_true in Hr.
    *
 now destruct Hr as (Hr, (Hfr, Hsr)); rewrite Hr, Hfr, Hsr.
    *
 now revert Hover; unfold B2R, F2R; simpl; rewrite Rmult_assoc, bpow_plus.
  +
 unfold Bldexp; rewrite B2SF_SF2B; simpl.
    destruct (binary_round_correct m s mf (ef + e)) as (Hf, Hr).
    fold emin in Hr; simpl in Hr; rewrite Rlt_bool_false in Hr; [exact Hr|].
    now revert Hover; unfold B2R, F2R; simpl; rewrite Rmult_assoc, bpow_plus.
Qed.

Lemma Bldexp_Bopp_NE x e : Bldexp mode_NE (Bopp x) e = Bopp (Bldexp mode_NE x e).
Proof using .
case x as [s|s| |s m e' B]; [now simpl..| ].
apply B2SF_inj.
replace (B2SF (Bopp _)) with (SFopp (B2SF (Bldexp mode_NE (B754_finite s m e' B) e))).
{
 unfold Bldexp, Bopp; rewrite !B2SF_SF2B.
  unfold binary_round.
  set (shl := shl_align_fexp _ _); case shl; intros mz ez.
  unfold binary_round_aux.
  set (shr := shr_fexp _ _ _); case shr; intros mrs e''.
  unfold choice_mode.
  set (shr' := shr_fexp _ _ _); case shr'; intros mrs' e'''.
  unfold binary_fit_aux.
  now case (shr_m mrs') as [|p|p]; [|case Z.leb|].
}
now case Bldexp as [s'|s'| |s' m' e'' B'].
Qed.

Definition Ffrexp_core_binary s m e :=
  if Zlt_bool (-prec) emin then
    (S754_finite s m e, 0%Z)
  else if (Z.to_pos prec <=? digits2_pos m)%positive then
    (S754_finite s m (-prec), (e + prec)%Z)
  else
    let d := (prec - Z.pos (digits2_pos m))%Z in
    (S754_finite s (shift_pos (Z.to_pos d) m) (-prec), (e + prec - d)%Z).

Lemma Bfrexp_correct_aux :
  forall sx mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Z.pos mx)) ex) in
  let z := fst (Ffrexp_core_binary sx mx ex) in
  let e := snd (Ffrexp_core_binary sx mx ex) in
  valid_binary z = true /\
  ((2 < emax)%Z -> (/2 <= Rabs (SF2R radix2 z) < 1)%R) /\
  (x = SF2R radix2 z * bpow radix2 e)%R.
Proof using prec_gt_0_.
intros sx mx ex Bx.
set (x := F2R _).
set (z := fst _).
set (e := snd _); simpl.
assert (Dmx_le_prec : (Z.pos (digits2_pos mx) <= prec)%Z).
{
 revert Bx; unfold bounded; rewrite Bool.andb_true_iff.
  unfold canonical_mantissa; rewrite <-Zeq_is_eq_bool; unfold fexp, FLT_exp.
  case (Z.max_spec (Z.pos (digits2_pos mx) + ex - prec) emin); lia.
}
assert (Dmx_le_prec' : (digits2_pos mx <= Z.to_pos prec)%positive).
{
 change (_ <= _)%positive
    with (Z.pos (digits2_pos mx) <= Z.pos (Z.to_pos prec))%Z.
  now rewrite Z2Pos.id; [|now apply prec_gt_0_].
}
unfold z, e, Ffrexp_core_binary.
case Z.ltb_spec ; intros Hp ; unfold emin in Hp.
{
 apply (conj Bx).
  split.
  clear -Hp ; lia.
  now rewrite Rmult_1_r.
}
case (Pos.leb_spec _ _); simpl; intro Dmx.
-
 unfold bounded, F2R; simpl.
  assert (Dmx' : digits2_pos mx = Z.to_pos prec).
  {
 now apply Pos.le_antisym.
}
  assert (Dmx'' : Z.pos (digits2_pos mx) = prec).
  {
 now rewrite Dmx', Z2Pos.id; [|apply prec_gt_0_].
}
  split; [|split].
  +
 apply andb_true_intro.
    split ; cycle 1.
    {
 apply Zle_bool_true.
clear -Hp ; lia.
}
    apply Zeq_bool_true; unfold fexp, FLT_exp.
    rewrite Dmx', Z2Pos.id by apply prec_gt_0_.
    rewrite Z.max_l.
    ring.
    clear -Hp.
    unfold emin ; lia.
  +
 intros _.
    rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by now apply bpow_ge_0.
    rewrite <-abs_IZR, abs_cond_Zopp; simpl; split.
    *
 apply (Rmult_le_reg_r (bpow radix2 prec)); [now apply bpow_gt_0|].
      rewrite Rmult_assoc, <-bpow_plus, Z.add_opp_diag_l; simpl.
      rewrite Rmult_1_r.
      change (/ 2)%R with (bpow radix2 (- 1)); rewrite <-bpow_plus.
      rewrite <-Dmx'', Z.add_comm, Zpos_digits2_pos, Zdigits_mag; [|lia].
      set (b := bpow _ _).
      rewrite <- (Rabs_pos_eq (IZR _)) by now apply IZR_le.
      now apply bpow_mag_le, IZR_neq.
    *
 apply (Rmult_lt_reg_r (bpow radix2 prec)); [now apply bpow_gt_0|].
      rewrite Rmult_assoc, <-bpow_plus, Z.add_opp_diag_l; simpl.
      rewrite Rmult_1_l, Rmult_1_r.
      rewrite <-Dmx'', Zpos_digits2_pos, Zdigits_mag; [|lia].
      set (b := bpow _ _).
      rewrite <- (Rabs_pos_eq (IZR _)) by now apply IZR_le.
      apply bpow_mag_gt.
  +
 rewrite Rmult_assoc, <- bpow_plus.
    now replace (_ + _)%Z with ex by ring.
-
 unfold bounded, F2R; simpl.
  assert (Dmx' : (Z.pos (digits2_pos mx) < prec)%Z).
  {
 now rewrite <-(Z2Pos.id prec); [|now apply prec_gt_0_].
}
  split; [|split].
  +
 unfold bounded; apply andb_true_intro.
    split ; cycle 1.
    {
 apply Zle_bool_true.
clear -Hp ; lia.
}
    apply Zeq_bool_true; unfold fexp, FLT_exp.
    rewrite Zpos_digits2_pos, shift_pos_correct, Z.pow_pos_fold.
    rewrite Z2Pos.id; [|lia].
    rewrite Z.mul_comm; change 2%Z with (radix2 : Z).
    rewrite Zdigits_mult_Zpower; [|lia|lia].
    rewrite Zpos_digits2_pos; replace (_ - _)%Z with (- prec)%Z by ring.
    now apply Z.max_l.
  +
 rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)); [|now apply bpow_ge_0].
    rewrite <-abs_IZR, abs_cond_Zopp; simpl.
    rewrite shift_pos_correct, mult_IZR.
    change (IZR (Z.pow_pos _ _))
      with (bpow radix2 (Z.pos (Z.to_pos ((prec - Z.pos (digits2_pos mx)))))).
    rewrite Z2Pos.id; [|lia].
    rewrite Rmult_comm, <-Rmult_assoc, <-bpow_plus.
    set (d := Z.pos (digits2_pos mx)).
    replace (_ + _)%Z with (- d)%Z by ring; split.
    *
 apply (Rmult_le_reg_l (bpow radix2 d)); [now apply bpow_gt_0|].
      rewrite <-Rmult_assoc, <-bpow_plus, Z.add_opp_diag_r.
      rewrite Rmult_1_l.
      change (/ 2)%R with (bpow radix2 (- 1)); rewrite <-bpow_plus.
      rewrite <- (Rabs_pos_eq (IZR _)) by now apply IZR_le.
      unfold d; rewrite Zpos_digits2_pos, Zdigits_mag; [|lia].
      now apply bpow_mag_le, IZR_neq.
    *
 apply (Rmult_lt_reg_l (bpow radix2 d)); [now apply bpow_gt_0|].
      rewrite <-Rmult_assoc, <-bpow_plus, Z.add_opp_diag_r.
      rewrite Rmult_1_l, Rmult_1_r.
      rewrite <- (Rabs_pos_eq (IZR _)) by now apply IZR_le.
      unfold d; rewrite Zpos_digits2_pos, Zdigits_mag; [|lia].
      apply bpow_mag_gt.
  +
 rewrite Rmult_assoc, <-bpow_plus, shift_pos_correct.
    rewrite IZR_cond_Zopp, mult_IZR, cond_Ropp_mult_r, <-IZR_cond_Zopp.
    change (IZR (Z.pow_pos _ _))
      with (bpow radix2 (Z.pos (Z.to_pos (prec - Z.pos (digits2_pos mx))))).
    rewrite Z2Pos.id; [|lia].
    rewrite Rmult_comm, <-Rmult_assoc, <-bpow_plus.
    now replace (_ + _)%Z with ex by ring; rewrite Rmult_comm.
Qed.

Definition Bfrexp f :=
  match f with
  | B754_finite s m e H =>
    let e' := snd (Ffrexp_core_binary s m e) in
    (SF2B _ (proj1 (Bfrexp_correct_aux s m e H)), e')
  | _ => (f, (-2*emax-prec)%Z)
  end.

Theorem is_nan_Bfrexp :
  forall x,
  is_nan (fst (Bfrexp x)) = is_nan x.
Proof using .
intros [sx|sx| |sx mx ex Bx] ; try easy.
simpl.
rewrite is_nan_SF2B.
unfold Ffrexp_core_binary.
destruct Zlt_bool ; try easy.
now destruct Pos.leb.
Qed.

Theorem Bfrexp_correct :
  forall f,
  is_finite_strict f = true ->
  let (z, e) := Bfrexp f in
  (B2R f = B2R z * bpow radix2 e)%R /\
  ( (2 < emax)%Z -> (/2 <= Rabs (B2R z) < 1)%R /\ e = mag radix2 (B2R f) ).
Proof using .
intro f; case f; intro s; try discriminate; intros m e Hf _.
generalize (Bfrexp_correct_aux s m e Hf).
intros (_, (Hb, Heq)); simpl; rewrite B2R_SF2B.
split.
easy.
intros Hp.
specialize (Hb Hp).
split.
easy.
rewrite Heq, mag_mult_bpow.
-
 apply (Z.add_reg_l (- (snd (Ffrexp_core_binary s m e)))).
  now ring_simplify; symmetry; apply mag_unique.
-
 intro H; destruct Hb as (Hb, _); revert Hb; rewrite H, Rabs_R0; lra.
Qed.

Lemma Bulp_correct_aux :
  bounded 1 emin = true.
Proof using prec_gt_0_ prec_lt_emax_.
unfold bounded, canonical_mantissa.
rewrite Zeq_bool_true.
apply Zle_bool_true.
apply Z.max_l_iff, fexp_emax.
apply Z.max_r.
simpl digits2_pos.
generalize (prec_gt_0 prec).
lia.
Qed.

Definition Bulp x :=
  match x with
  | B754_zero _ => B754_finite false 1 emin Bulp_correct_aux
  | B754_infinity _ => B754_infinity false
  | B754_nan => B754_nan
  | B754_finite _ _ e _ => binary_normalize mode_ZR 1 e false
  end.

Theorem is_nan_Bulp :
  forall x,
  is_nan (Bulp x) = is_nan x.
Proof using .
intros [sx|sx| |sx mx ex Bx] ; try easy.
unfold Bulp.
apply is_nan_binary_normalize.
Qed.

Theorem Bulp_correct :
  forall x,
  is_finite x = true ->
  B2R (Bulp x) = ulp radix2 fexp (B2R x) /\
  is_finite (Bulp x) = true /\
  Bsign (Bulp x) = false.
Proof using .
intros [sx|sx| |sx mx ex Hx] Fx ; try easy ; simpl.
-
 repeat split.
  change fexp with (FLT_exp emin prec).
  rewrite ulp_FLT_0 by easy.
  apply F2R_bpow.
-
 destruct (binary_round_correct mode_ZR false 1 ex) as [H1 H2].
  revert H2.
  simpl.
  destruct (andb_prop _ _ Hx) as [H5 H6].
  replace (round _ _ _ _) with (bpow radix2 ex).
  rewrite Rlt_bool_true.
  intros [H2 [H3 H4]].
  split ; [|split].
  +
 rewrite B2R_SF2B.
    rewrite ulp_canonical.
    exact H2.
    now case sx.
    now apply canonical_canonical_mantissa.
  +
 now rewrite is_finite_SF2B.
  +
 now rewrite Bsign_SF2B.
  +
 rewrite Rabs_pos_eq by apply bpow_ge_0.
    apply bpow_lt.
    generalize (prec_gt_0 prec) (Zle_bool_imp_le _ _ H6).
    clear ; lia.
  +
 rewrite F2R_bpow.
    apply sym_eq, round_generic.
    typeclasses eauto.
    apply generic_format_FLT_bpow.
    easy.
    rewrite (canonical_canonical_mantissa false _ _ H5).
    apply Z.max_le_iff.
    now right.
Qed.

Theorem is_finite_strict_Bulp :
  forall x,
  is_finite_strict (Bulp x) = is_finite x.
Proof using .
intros [sx|sx| |sx mx ex Bx] ; try easy.
generalize (Bulp_correct (B754_finite sx mx ex Bx) eq_refl).
destruct Bulp as [sy| | |] ; try easy.
intros [H _].
contradict H.
rewrite ulp_neq_0.
apply Rlt_not_eq.
apply bpow_gt_0.
apply F2R_neq_0.
now destruct sx.
Qed.

Definition Bulp' x := Bldexp mode_NE Bone (fexp (snd (Bfrexp x))).

Theorem Bulp'_correct :
  (2 < emax)%Z ->
  forall x,
  is_finite x = true ->
  Bulp' x = Bulp x.
Proof using .
intros Hp x Fx.
assert (B2R (Bulp' x) = ulp radix2 fexp (B2R x) /\
        is_finite (Bulp' x) = true /\
        Bsign (Bulp' x) = false) as [H1 [H2 H3]].
{
 destruct x as [sx|sx| |sx mx ex Hx] ; unfold Bulp'.
-
 replace (fexp _) with emin.
  +
 generalize (Bldexp_correct mode_NE Bone emin).
    rewrite Bone_correct, Rmult_1_l, round_generic;
      [|now apply valid_rnd_N|apply generic_format_bpow; unfold fexp, FLT_exp;
        rewrite Z.max_r; unfold Prec_gt_0 in prec_gt_0_; lia].
    rewrite Rlt_bool_true.
    *
 intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
      split; [|now split; [apply is_finite_Bone|apply Bsign_Bone]].
      simpl; unfold ulp; rewrite Req_bool_true; [|reflexivity].
      destruct (negligible_exp_FLT emin prec) as (n, (Hn, Hn')).
      change fexp with (FLT_exp emin prec); rewrite Hn.
      now unfold FLT_exp; rewrite Z.max_r;
        [|unfold Prec_gt_0 in prec_gt_0_; lia].
    *
 rewrite Rabs_pos_eq; [|now apply bpow_ge_0]; apply bpow_lt.
      apply emin_lt_emax.
  +
 simpl; change (fexp _) with (fexp (-2 * emax - prec)).
    unfold fexp, FLT_exp; rewrite Z.max_r; [reflexivity|].
    unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
-
 discriminate.
-
 discriminate.
-
 unfold ulp, cexp.
  set (f := B754_finite _ _ _ _).
  rewrite Req_bool_false.
  +
 destruct (Bfrexp_correct f (eq_refl _)) as (Hfr1, (Hfr2, Hfr3)).
    apply Hp.
    simpl.
    rewrite Hfr3.
    set (e' := fexp _).
    generalize (Bldexp_correct mode_NE Bone e').
    rewrite Bone_correct, Rmult_1_l, round_generic; [|now apply valid_rnd_N|].
    {
 rewrite Rlt_bool_true.
      -
 intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
        now split; [|split; [apply is_finite_Bone|apply Bsign_Bone]].
      -
 rewrite Rabs_pos_eq; [|now apply bpow_ge_0].
        unfold e', fexp, FLT_exp.
        apply bpow_lt.
        case (Z.max_spec (mag radix2 (B2R f) - prec) emin)
          as [(_, Hm)|(_, Hm)]; rewrite Hm.
        apply emin_lt_emax.
        apply (Zplus_lt_reg_r _ _ prec); ring_simplify.
        assert (mag radix2 (B2R f) <= emax)%Z;
          [|now unfold Prec_gt_0 in prec_gt_0_; lia].
        apply mag_le_bpow; [|now apply abs_B2R_lt_emax].
        now unfold f, B2R; apply F2R_neq_0; case sx.
}
    apply generic_format_bpow, Z.max_lub.
    *
 unfold Prec_gt_0 in prec_gt_0_; lia.
    *
 apply Z.le_max_r.
  +
 now unfold f, B2R; apply F2R_neq_0; case sx.
}
destruct (Bulp_correct x Fx) as [H4 [H5 H6]].
apply B2R_Bsign_inj ; try easy.
now rewrite H4.
now rewrite H3.
Qed.

Definition Bsucc x :=
  match x with
  | B754_zero _ => B754_finite false 1 emin Bulp_correct_aux
  | B754_infinity false => x
  | B754_infinity true => Bopp Bmax_float
  | B754_nan => B754_nan
  | B754_finite false mx ex _ =>
    SF2B _ (proj1 (binary_round_correct mode_UP false (mx + 1) ex))
  | B754_finite true mx ex _ =>
    SF2B _ (proj1 (binary_round_correct mode_ZR true (xO mx - 1) (ex - 1)))
  end.

Theorem is_nan_Bsucc :
  forall x,
  is_nan (Bsucc x) = is_nan x.
Proof using .
unfold Bsucc.
intros [sx|[|]| |[|] mx ex Bx] ; try easy.
rewrite is_nan_SF2B.
apply is_nan_binary_round.
rewrite is_nan_SF2B.
apply is_nan_binary_round.
Qed.

Theorem Bsucc_correct :
  forall x,
  is_finite x = true ->
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc x) = true /\
    (Bsign (Bsucc x) = Bsign x && is_finite_strict x)%bool
  else
    B2SF (Bsucc x) = S754_infinity false.
Proof using .
intros [sx|sx| | [|] mx ex Bx] Hx ; try easy ; clear Hx.
-
 simpl.
  change fexp with (FLT_exp emin prec).
  rewrite succ_0, ulp_FLT_0 by easy.
  rewrite Rlt_bool_true.
  repeat split ; cycle 1.
  now case sx.
  apply F2R_bpow.
  apply bpow_lt.
  apply emin_lt_emax.
-
 change (B2R (B754_finite _ _ _ _)) with (F2R (Fopp (Float radix2 (Zpos mx) ex))).
  rewrite F2R_opp, succ_opp.
  rewrite Rlt_bool_true ; cycle 1.
  {
 apply Rle_lt_trans with 0%R.
    2: apply bpow_gt_0.
    rewrite <- Ropp_0.
    apply Ropp_le_contravar.
    apply pred_ge_0.
    now apply FLT_exp_valid.
    now apply F2R_gt_0.
    apply generic_format_canonical.
    now apply (canonical_bounded false).
}
  simpl.
  rewrite B2R_SF2B, is_finite_SF2B, Bsign_SF2B.
  generalize (binary_round_correct mode_ZR true (xO mx - 1) (ex - 1)).
  set (z := binary_round _ _ _ _).
  rewrite F2R_cond_Zopp.
  simpl.
  rewrite round_ZR_opp.
  rewrite round_ZR_DN by now apply F2R_ge_0.
  assert (H: F2R (Float radix2 (Zpos (xO mx - 1)) (ex - 1)) = (F2R (Float radix2 (Zpos mx) ex) - F2R (Float radix2 1 (ex - 1)))%R).
  {
 rewrite (F2R_change_exp _ (ex - 1) _ ex) by apply Z.le_pred_l.
    rewrite <- F2R_minus, Fminus_same_exp.
    apply F2R_eq.
    replace (ex - (ex - 1))%Z with 1%Z by ring.
    now rewrite Zmult_comm.
}
  rewrite Rlt_bool_true.
  +
 intros [_ [H1 [H2 H3]]].
    split.
    2: now split.
    rewrite H1, H.
    apply f_equal.
    apply round_DN_minus_eps_pos.
      now apply FLT_exp_valid.
      now apply F2R_gt_0.
      apply (generic_format_B2R (B754_finite false mx ex Bx)).
    split.
      now apply F2R_gt_0.
    rewrite F2R_bpow.
    change fexp with (FLT_exp emin prec).
    destruct (ulp_FLT_pred_pos radix2 emin prec (F2R (Float radix2 (Zpos mx) ex))) as [Hu|[Hu1 Hu2]].
    *
 apply (generic_format_B2R (B754_finite false mx ex Bx)).
    *
 now apply F2R_ge_0.
    *
 rewrite Hu.
      rewrite ulp_canonical.
      apply bpow_le.
      apply Z.le_pred_l.
      easy.
      now apply (canonical_bounded false).
    *
 rewrite Hu2.
      rewrite ulp_canonical.
      rewrite <- (Zmult_1_r radix2).
      change (_ / _)%R with (bpow radix2 ex * bpow radix2 (-1))%R.
      rewrite <- bpow_plus.
      apply Rle_refl.
      easy.
      now apply (canonical_bounded false).
  +
 rewrite Rabs_Ropp, Rabs_pos_eq.
    eapply Rle_lt_trans.
    2: apply bounded_lt_emax with (1 := Bx).
    apply Rle_trans with (F2R (Float radix2 (Zpos (xO mx - 1)) (ex - 1))).
    apply round_DN_pt.
    now apply FLT_exp_valid.
    rewrite H.
    rewrite <- (Rminus_0_r (F2R _)) at 2.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    now apply F2R_ge_0.
    apply round_DN_pt.
    now apply FLT_exp_valid.
    apply generic_format_0.
    now apply F2R_ge_0.
-
 assert (Cx := proj1 (andb_prop _ _ Bx)).
  apply (canonical_canonical_mantissa false) in Cx.
  replace (succ _ _ _) with (F2R (Float radix2 (Zpos mx + 1) ex)) ; cycle 1.
  {
 unfold succ, B2R.
    rewrite Rle_bool_true by now apply F2R_ge_0.
    rewrite ulp_canonical by easy.
    rewrite <- F2R_bpow.
    rewrite <- F2R_plus.
    now rewrite Fplus_same_exp.
}
  simpl.
  rewrite B2R_SF2B, is_finite_SF2B, Bsign_SF2B.
  generalize (binary_round_correct mode_UP false (mx + 1) ex).
  simpl.
  rewrite round_generic.
  +
 rewrite Rabs_pos_eq by now apply F2R_ge_0.
    case Rlt_bool_spec ; intros Hs.
    now intros [_ H].
    intros H.
    rewrite B2SF_SF2B.
    now rewrite (proj2 H).
  +
 apply valid_rnd_UP.
  +
 destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as [e He].
    rewrite Rabs_pos_eq in He by now apply F2R_ge_0.
    refine (_ (He _)).
    2: now apply F2R_neq_0.
    clear He.
intros He.
    destruct (F2R_p1_le_bpow _ (Zpos mx) _ _ eq_refl (proj2 He)) as [H|H].
    *
 apply generic_format_F2R.
      intros _.
      rewrite Cx at 2.
      apply cexp_ge_bpow.
      apply FLT_exp_monotone.
      rewrite Rabs_pos_eq by now apply F2R_ge_0.
      rewrite (mag_unique_pos _ _ e).
      apply He.
      split.
      apply Rle_trans with (1 := proj1 He).
      apply F2R_le.
      apply Z.le_succ_diag_r.
      exact H.
    *
 simpl in H.
      rewrite H.
      apply generic_format_FLT_bpow.
      easy.
      apply le_bpow with radix2.
      apply Rlt_le.
      apply Rle_lt_trans with (2 := proj2 He).
      apply generic_format_ge_bpow with fexp.
      intros e'.
      apply Z.le_max_r.
      now apply F2R_gt_0.
      now apply generic_format_canonical.
Qed.

Definition Bpred x := Bopp (Bsucc (Bopp x)).

Theorem is_nan_Bpred :
  forall x,
  is_nan (Bpred x) = is_nan x.
Proof using .
intros x.
unfold Bpred.
rewrite is_nan_Bopp, is_nan_Bsucc.
apply is_nan_Bopp.
Qed.

Theorem Bpred_correct :
  forall x,
  is_finite x = true ->
  if Rlt_bool (- bpow radix2 emax) (pred radix2 fexp (B2R x)) then
    B2R (Bpred x) = pred radix2 fexp (B2R x) /\
    is_finite (Bpred x) = true /\
    (Bsign (Bpred x) = Bsign x || negb (is_finite_strict x))%bool
  else
    B2SF (Bpred x) = S754_infinity true.
Proof using .
intros x Fx.
assert (Fox : is_finite (Bopp x) = true).
{
 now rewrite is_finite_Bopp.
}
rewrite <-(Ropp_involutive (B2R x)), <-B2R_Bopp.
rewrite pred_opp, Rlt_bool_opp.
generalize (Bsucc_correct _ Fox).
case (Rlt_bool _ _).
-
 intros (HR, (HF, HS)); unfold Bpred.
  rewrite B2R_Bopp, HR, is_finite_Bopp.
  rewrite <-(Bool.negb_involutive (Bsign x)), <-Bool.negb_andb.
  apply (conj eq_refl).
  apply (conj HF).
  rewrite Bsign_Bopp, <-(Bsign_Bopp x), HS.
  +
 now rewrite is_finite_strict_Bopp.
  +
 now revert Fx; case x.
  +
 now revert HF; case (Bsucc _).
-
 now unfold Bpred; case (Bsucc _); intro s; case s.
Qed.

Definition Bpred_pos' x :=
  match x with
  | B754_finite _ mx _ _ =>
    let d :=
      if (mx~0 =? shift_pos (Z.to_pos prec) 1)%positive then
        Bldexp mode_NE Bone (fexp (snd (Bfrexp x) - 1))
      else
        Bulp' x in
    Bminus mode_NE x d
  | _ => x
  end.

Theorem Bpred_pos'_correct :
  (2 < emax)%Z ->
  forall x,
  (0 < B2R x)%R ->
  Bpred_pos' x = Bpred x.
Proof using .
intros Hp x Fx.
assert (B2R (Bpred_pos' x) = pred_pos radix2 fexp (B2R x) /\
        is_finite (Bpred_pos' x) = true /\
        Bsign (Bpred_pos' x) = false) as [H1 [H2 H3]].
{
 generalize (Bfrexp_correct x).
  destruct x as [sx|sx| |sx mx ex Bx] ; try elim (Rlt_irrefl _ Fx).
  intros Hfrexpx.
  assert (Hsx : sx = false).
  {
 apply gt_0_F2R in Fx.
    revert Fx.
    now case sx.
}
  clear Fx.
  rewrite Hsx in Hfrexpx |- *; clear Hsx sx.
  specialize (Hfrexpx (eq_refl _)).
  simpl in Hfrexpx; rewrite B2R_SF2B in Hfrexpx.
  destruct Hfrexpx as (Hfrexpx_bounds, (Hfrexpx_eq, Hfrexpx_exp)).
  apply Hp.
  unfold Bpred_pos', Bfrexp.
  simpl (snd (_, snd _)).
  rewrite Hfrexpx_exp.
  set (x' := B754_finite _ _ _ _).
  set (xr := F2R _).
  assert (Nzxr : xr <> 0%R).
  {
 now apply F2R_neq_0.
}
  assert (Hulp := Bulp_correct x' (eq_refl _)).
  rewrite <- (Bulp'_correct Hp x') in Hulp by easy.
  assert (Hldexp := Bldexp_correct mode_NE Bone (fexp (mag radix2 xr - 1))).
  rewrite Bone_correct, Rmult_1_l in Hldexp.
  assert (Fbpowxr : generic_format radix2 fexp
                      (bpow radix2 (fexp (mag radix2 xr - 1)))).
  {
 apply generic_format_bpow, Z.max_lub.
    -
 unfold Prec_gt_0 in prec_gt_0_; lia.
    -
 apply Z.le_max_r.
}
  assert (H : Rlt_bool (Rabs
               (round radix2 fexp (round_mode mode_NE)
                  (bpow radix2 (fexp (mag radix2 xr - 1)))))
              (bpow radix2 emax) = true); [|rewrite H in Hldexp; clear H].
  {
 apply Rlt_bool_true; rewrite round_generic;
      [|apply valid_rnd_round_mode|apply Fbpowxr].
    rewrite Rabs_pos_eq; [|apply bpow_ge_0]; apply bpow_lt.
    apply Z.max_lub_lt.
2: apply emin_lt_emax.
    apply (Zplus_lt_reg_r _ _ (prec + 1)); ring_simplify.
    rewrite Z.add_1_r; apply Zle_lt_succ, mag_le_bpow.
    -
 exact Nzxr.
    -
 apply (Rlt_le_trans _ (bpow radix2 emax)).
      +
 change xr with (B2R x'); apply abs_B2R_lt_emax.
      +
 apply bpow_le; unfold Prec_gt_0 in prec_gt_0_; lia.
}
  set (d := if (mx~0 =? _)%positive then _ else _).
  assert (Hminus := Bminus_correct mode_NE x' d (eq_refl _)).
  assert (Fd : is_finite d = true).
  {
 unfold d; case (_ =? _)%positive.
    -
 now rewrite (proj1 (proj2 Hldexp)), is_finite_Bone.
    -
 now rewrite (proj1 (proj2 Hulp)).
}
  specialize (Hminus Fd).
  assert (Px : (0 <= B2R x')%R).
  {
 unfold B2R, x', F2R; simpl.
    now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0].
}
  assert (Pd : (0 <= B2R d)%R).
  {
 unfold d; case (_ =? _)%positive.
    -
 rewrite (proj1 Hldexp).
      now rewrite round_generic; [apply bpow_ge_0|apply valid_rnd_N|].
    -
 rewrite (proj1 Hulp); apply ulp_ge_0.
}
  assert (Hdlex : (B2R d <= B2R x')%R).
  {
 unfold d; case (_ =? _)%positive.
    -
 rewrite (proj1 Hldexp).
      rewrite round_generic; [|now apply valid_rnd_N|now simpl].
      apply (Rle_trans _ (bpow radix2 (mag radix2 xr - 1))).
      +
 apply bpow_le, Z.max_lub.
        *
 unfold Prec_gt_0 in prec_gt_0_; lia.
        *
 apply (Zplus_le_reg_r _ _ 1); ring_simplify.
          apply mag_ge_bpow.
          replace (_ - 1)%Z with emin by ring.
          now change xr with (B2R x'); apply abs_B2R_ge_emin.
      +
 rewrite <-(Rabs_pos_eq _ Px).
        now change xr with (B2R x'); apply bpow_mag_le.
    -
 rewrite (proj1 Hulp); apply ulp_le_id.
      +
 assert (B2R x' <> 0%R); [exact Nzxr|lra].
      +
 apply generic_format_B2R.
}
  assert (H : Rlt_bool
            (Rabs
               (round radix2 fexp
                  (round_mode mode_NE) (B2R x' - B2R d)))
            (bpow radix2 emax) = true); [|rewrite H in Hminus; clear H].
  {
 apply Rlt_bool_true.
    rewrite <-round_NE_abs; [|now apply FLT_exp_valid].
    rewrite Rabs_pos_eq; [|lra].
    apply (Rle_lt_trans _ (B2R x')).
    -
 apply round_le_generic;
        [now apply FLT_exp_valid|now apply valid_rnd_N| |lra].
      apply generic_format_B2R.
    -
 apply (Rle_lt_trans _ _ _ (Rle_abs _)), abs_B2R_lt_emax.
}
  rewrite (proj1 Hminus).
  rewrite (proj1 (proj2 Hminus)).
  rewrite (proj2 (proj2 Hminus)).
  split; [|split; [reflexivity|now case (Rcompare_spec _ _); [lra| |]]].
  unfold pred_pos, d.
  case (Pos.eqb_spec _ _); intro Hd; case (Req_bool_spec _ _); intro Hpred.
  +
 rewrite (proj1 Hldexp).
    rewrite (round_generic _ _ _ _ Fbpowxr).
    change xr with (B2R x').
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    *
 rewrite round_generic; [reflexivity|now apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid|apply generic_format_B2R|].
      change xr with (B2R x') in Nzxr; lra.
    *
 now unfold pred_pos; rewrite Req_bool_true.
  +
 exfalso; apply Hpred.
    assert (Hmx : IZR (Z.pos mx) = bpow radix2 (prec - 1)).
    {
 apply (Rmult_eq_reg_l 2); [|lra]; rewrite <-mult_IZR.
      change (2 * Z.pos mx)%Z with (Z.pos mx~0); rewrite Hd.
      rewrite shift_pos_correct, Z.mul_1_r.
      change (IZR (Z.pow_pos _ _)) with (bpow radix2 (Z.pos (Z.to_pos prec))).
      rewrite Z2Pos.id; [|exact prec_gt_0_].
      change 2%R with (bpow radix2 1); rewrite <-bpow_plus.
      f_equal; ring.
}
    unfold x' at 1; unfold B2R at 1; unfold F2R; simpl.
    rewrite Hmx, <-bpow_plus; f_equal.
    apply (Z.add_reg_l 1); ring_simplify; symmetry; apply mag_unique_pos.
    unfold F2R; simpl; rewrite Hmx, <-bpow_plus; split.
    *
 right; f_equal; ring.
    *
 apply bpow_lt; lia.
  +
 rewrite (proj1 Hulp).
    assert (H : ulp radix2 fexp (B2R x')
                = bpow radix2 (fexp (mag radix2 (B2R x') - 1)));
      [|rewrite H; clear H].
    {
 unfold ulp; rewrite Req_bool_false; [|now simpl].
      unfold cexp; f_equal.
      assert (H : (mag radix2 (B2R x') <= emin + prec)%Z).
      {
 assert (Hcm : canonical_mantissa mx ex = true).
        {
 now generalize Bx; unfold bounded; rewrite Bool.andb_true_iff.
}
        apply (canonical_canonical_mantissa false) in Hcm.
        revert Hcm; fold emin; unfold canonical, cexp; simpl.
        change (F2R _) with (B2R x'); intro Hex.
        apply Z.nlt_ge; intro H'; apply Hd.
        apply Pos2Z.inj_pos; rewrite shift_pos_correct, Z.mul_1_r.
        apply eq_IZR; change (IZR (Z.pow_pos _ _))
          with (bpow radix2 (Z.pos (Z.to_pos prec))).
        rewrite Z2Pos.id; [|exact prec_gt_0_].
        change (Z.pos mx~0) with (2 * Z.pos mx)%Z.
        rewrite Z.mul_comm, mult_IZR.
        apply (Rmult_eq_reg_r (bpow radix2 (ex - 1)));
          [|apply Rgt_not_eq, bpow_gt_0].
        change 2%R with (bpow radix2 1); rewrite Rmult_assoc, <-!bpow_plus.
        replace (1 + _)%Z with ex by ring.
        unfold B2R at 1, F2R in Hpred; simpl in Hpred; rewrite Hpred.
        change (F2R _) with (B2R x'); rewrite Hex.
        unfold fexp, FLT_exp; rewrite Z.max_l; [f_equal; ring|lia].
}
      now unfold fexp, FLT_exp; do 2 (rewrite Z.max_r; [|lia]).
}
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    *
 rewrite round_generic; [reflexivity|apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid| |change xr with (B2R x') in Nzxr; lra].
      apply generic_format_B2R.
    *
 now unfold pred_pos; rewrite Req_bool_true.
  +
 rewrite (proj1 Hulp).
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    *
 rewrite round_generic; [reflexivity|now apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid|apply generic_format_B2R|].
      change xr with (B2R x') in Nzxr; lra.
    *
 now unfold pred_pos; rewrite Req_bool_false.
}
assert (is_finite x = true /\ Bsign x = false) as [H4 H5].
{
 clear -Fx.
  destruct x as [| | |sx mx ex Hx] ; try elim Rlt_irrefl with (1 := Fx).
  repeat split.
  destruct sx.
  elim Rlt_not_le with (1 := Fx).
  now apply F2R_le_0.
  easy.
}
generalize (Bpred_correct x H4).
rewrite Rlt_bool_true ; cycle 1.
{
 apply Rlt_le_trans with 0%R.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  apply bpow_gt_0.
  apply pred_ge_0.
  now apply FLT_exp_valid.
  exact Fx.
  apply generic_format_B2R.
}
intros [H7 [H8 H9]].
apply eq_sym.
apply B2R_Bsign_inj ; try easy.
rewrite H7, H1.
apply pred_eq_pos.
now apply Rlt_le.
rewrite H9, H3.
rewrite is_finite_strict_B2R by now apply Rgt_not_eq.
now rewrite H5.
Qed.

Definition Bsucc' x :=
  match x with
  | B754_zero _ => Bldexp mode_NE Bone emin
  | B754_infinity false => x
  | B754_infinity true => Bopp Bmax_float
  | B754_nan => B754_nan
  | B754_finite false _ _ _ => Bplus mode_NE x (Bulp x)
  | B754_finite true _ _ _ => Bopp (Bpred_pos' (Bopp x))
  end.

Theorem Bsucc'_correct :
  (2 < emax)%Z ->
  forall x,
  is_finite x = true ->
  Bsucc' x = Bsucc x.
Proof using .
intros Hp x Fx.
destruct x as [sx|sx| |sx mx ex Bx] ; try easy.
{
 generalize (Bldexp_correct mode_NE Bone emin).
  rewrite Bone_correct, Rmult_1_l.
  rewrite round_generic.
  rewrite Rlt_bool_true.
  simpl.
  intros [H1 [H2 H3]].
  apply B2R_inj.
  apply is_finite_strict_B2R.
  rewrite H1.
  apply Rgt_not_eq.
  apply bpow_gt_0.
  easy.
  rewrite H1.
  apply eq_sym, F2R_bpow.
  rewrite Rabs_pos_eq by now apply bpow_ge_0.
  apply bpow_lt, emin_lt_emax.
  apply valid_rnd_N.
  apply generic_format_bpow.
  unfold fexp.
  rewrite Z.max_r.
  apply Z.le_refl.
  generalize (prec_gt_0 prec).
  lia.
}
set (x := B754_finite sx mx ex Bx).
assert (H:
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc' x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc' x) = true /\
    Bsign (Bsucc' x) = sx
  else
    B2SF (Bsucc' x) = S754_infinity false).
{
  assert (Hsucc : succ radix2 fexp 0 = bpow radix2 emin).
  {
 rewrite succ_0.
    now apply ulp_FLT_0.
}
  unfold Bsucc', x; destruct sx.
  +
 case Rlt_bool_spec; intro Hover.
    *
 rewrite B2R_Bopp; simpl (Bopp (B754_finite _ _ _ _)).
      rewrite is_finite_Bopp.
      set (ox := B754_finite false mx ex Bx).
      assert (Hpred := Bpred_correct ox eq_refl).
      rewrite Bpred_pos'_correct ; cycle 1.
        exact Hp.
        now apply F2R_gt_0.
      rewrite Rlt_bool_true in Hpred.
      rewrite (proj1 Hpred), (proj1 (proj2 Hpred)).
      split.
      rewrite <- succ_opp.
      simpl.
      now rewrite <- F2R_opp.
      apply (conj eq_refl).
      rewrite Bsign_Bopp, (proj2 (proj2 Hpred)).
      easy.
      generalize (proj1 (proj2 Hpred)).
      now case Bpred.
      apply Rlt_le_trans with 0%R.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar, bpow_gt_0.
      apply pred_ge_0.
      now apply FLT_exp_valid.
      now apply F2R_gt_0.
      apply generic_format_B2R.
    *
 exfalso; revert Hover; apply Rlt_not_le.
      apply (Rle_lt_trans _ (succ radix2 fexp 0)).
      {
 apply succ_le; [now apply FLT_exp_valid|apply generic_format_B2R|
                        apply generic_format_0|].
        unfold B2R, F2R; simpl; change (Z.neg mx) with (- Z.pos mx)%Z.
        rewrite opp_IZR, <-Ropp_mult_distr_l, <-Ropp_0; apply Ropp_le_contravar.
        now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0].
}
      rewrite Hsucc; apply bpow_lt.
      apply emin_lt_emax.
  +
 fold x.
    assert (Hulp := Bulp_correct x (eq_refl _)).
    assert (Hplus := Bplus_correct mode_NE x (Bulp x) (eq_refl _)).
    rewrite (proj1 (proj2 Hulp)) in Hplus; specialize (Hplus (eq_refl _)).
    assert (Px : (0 <= B2R x)%R).
    {
 now apply F2R_ge_0.
}
    assert (Hsucc' : (succ radix2 fexp (B2R x)
                      = B2R x + ulp radix2 fexp (B2R x))%R).
    {
 now unfold succ; rewrite (Rle_bool_true _ _ Px).
}
    rewrite (proj1 Hulp), <- Hsucc' in Hplus.
    rewrite round_generic in Hplus;
      [|apply valid_rnd_N| now apply generic_format_succ;
                           [apply FLT_exp_valid|apply generic_format_B2R]].
    rewrite Rabs_pos_eq in Hplus; [|apply (Rle_trans _ _ _ Px), succ_ge_id].
    revert Hplus; case Rlt_bool_spec; intros Hover Hplus.
    *
 split; [now simpl|split; [now simpl|]].
      rewrite (proj2 (proj2 Hplus)); case Rcompare_spec.
      {
 intro H; exfalso; revert H.
        apply Rle_not_lt, (Rle_trans _ _ _ Px), succ_ge_id.
}
      {
 intro H; exfalso; revert H; apply Rgt_not_eq, Rlt_gt.
        apply (Rlt_le_trans _ (B2R x)); [|apply succ_ge_id].
        now apply Rmult_lt_0_compat; [apply IZR_lt|apply bpow_gt_0].
}
      now simpl.
    *
 now rewrite (proj1 Hplus).
}
generalize (Bsucc_correct x Fx).
revert H.
case Rlt_bool_spec ; intros H.
intros [H1 [H2 H3]] [H4 [H5 H6]].
apply B2R_Bsign_inj ; try easy.
now rewrite H4.
rewrite H3, H6.
simpl.
now case sx.
intros H1 H2.
apply B2SF_inj.
now rewrite H1, H2.
Qed.

End Binary.

Arguments B754_zero {prec} {emax}.
Arguments B754_infinity {prec} {emax}.
Arguments B754_nan {prec} {emax}.
Arguments B754_finite {prec} {emax}.

Arguments SF2B {prec} {emax}.
Arguments SF2B' {prec} {emax}.
Arguments B2SF {prec} {emax}.
Arguments B2R {prec} {emax}.

Arguments is_finite_strict {prec} {emax}.
Arguments is_finite {prec} {emax}.
Arguments is_nan {prec} {emax}.

Arguments erase {prec} {emax}.
Arguments Bsign {prec} {emax}.
Arguments Bcompare {prec} {emax}.
Arguments Beqb {prec} {emax}.
Arguments Bltb {prec} {emax}.
Arguments Bleb {prec} {emax}.
Arguments Bopp {prec} {emax}.
Arguments Babs {prec} {emax}.
Arguments Bone {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bmax_float {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.

Arguments Bplus {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bminus {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bmult {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bfma {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bdiv {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bsqrt {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bnearbyint {prec} {emax} {prec_lt_emax_}.
Arguments Btrunc {prec} {emax}.

Arguments Bldexp {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bnormfr_mantissa {prec} {emax}.
Arguments Bfrexp {prec} {emax} {prec_gt_0_}.
Arguments Bulp {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bulp' {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bsucc {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bpred {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bpred_pos' {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.

End BinarySingleNaN.

End IEEE754.

End Flocq.

End Flocq_DOT_IEEE754_DOT_BinarySingleNaN.
Require Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Stdlib.Floats.Floats.
Require Stdlib.Lists.List.
Require Stdlib.Arith.PeanoNat.
Require Flocq.Pff.Pff.


Module Export Flocq_DOT_IEEE754_DOT_Binary.
Module Export Flocq.
Module Export IEEE754.
Module Export Binary.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz Stdlib.Floats.SpecFloat.
Import Flocq.Core.Core Flocq.Calc.Round Flocq.Calc.Bracket Flocq.Calc.Operations Flocq.Calc.Div Flocq.Calc.Sqrt Flocq_DOT_Prop_DOT_Relative.Flocq.AVOID_RESERVED_Prop.Relative Flocq.IEEE754.BinarySingleNaN.

Arguments BinarySingleNaN.B754_zero {prec emax}.
Arguments BinarySingleNaN.B754_infinity {prec emax}.
Arguments BinarySingleNaN.B754_nan {prec emax}.
Arguments BinarySingleNaN.B754_finite {prec emax}.

Section AnyRadix.

Inductive full_float :=
  | F754_zero (s : bool)
  | F754_infinity (s : bool)
  | F754_nan (s : bool) (m : positive)
  | F754_finite (s : bool) (m : positive) (e : Z).

Definition FF2SF x :=
  match x with
  | F754_zero s => S754_zero s
  | F754_infinity s => S754_infinity s
  | F754_nan _ _ => S754_nan
  | F754_finite s m e => S754_finite s m e
  end.

Definition FF2R beta x :=
  match x with
  | F754_finite s m e => F2R (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

Lemma SF2R_FF2SF :
  forall beta x,
  SF2R beta (FF2SF x) = FF2R beta x.
Proof.
now intros beta [s|s|s m|s m e].
Qed.

Definition SF2FF x :=
  match x with
  | S754_zero s => F754_zero s
  | S754_infinity s => F754_infinity s
  | S754_nan => F754_nan false xH
  | S754_finite s m e => F754_finite s m e
  end.

Lemma FF2SF_SF2FF :
  forall x,
  FF2SF (SF2FF x) = x.
Proof.
now intros [s|s| |s m e].
Qed.

Lemma FF2R_SF2FF :
  forall beta x,
  FF2R beta (SF2FF x) = SF2R beta x.
Proof.
now intros beta [s|s| |s m e].
Qed.

Definition is_nan_FF f :=
  match f with
  | F754_nan _ _ => true
  | _ => false
  end.

Lemma is_nan_SF2FF :
  forall x,
  is_nan_FF (SF2FF x) = is_nan_SF x.
Proof.
now intros [s|s| |s m e].
Qed.

Lemma is_nan_FF2SF :
  forall x,
  is_nan_SF (FF2SF x) = is_nan_FF x.
Proof.
now intros [s|s|s m|s m e].
Qed.

Lemma SF2FF_FF2SF :
  forall x,
  is_nan_FF x = false ->
  SF2FF (FF2SF x) = x.
Proof.
now intros [s|s|s m|s m e] H.
Qed.

Definition sign_FF x :=
  match x with
  | F754_nan s _ => s
  | F754_zero s => s
  | F754_infinity s => s
  | F754_finite s _ _ => s
  end.

Definition is_finite_FF f :=
  match f with
  | F754_finite _ _ _ => true
  | F754_zero _ => true
  | _ => false
  end.

Lemma is_finite_SF2FF :
  forall x,
  is_finite_FF (SF2FF x) = is_finite_SF x.
Proof.
now intros [| | |].
Qed.

Lemma sign_SF2FF :
  forall x,
  sign_FF (SF2FF x) = sign_SF x.
Proof.
now intros [| | |].
Qed.

End AnyRadix.

Section Binary.

Arguments exist {A} {P}.

Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Context (prec_lt_emax_ : Prec_lt_emax prec emax).

Notation emin := (emin prec emax) (only parsing).
Notation fexp := (fexp prec emax) (only parsing).
Instance fexp_correct : Valid_exp fexp := FLT_exp_valid emin prec.
Instance fexp_monotone : Monotone_exp fexp := FLT_exp_monotone emin prec.

Notation canonical_mantissa := (canonical_mantissa prec emax).

Notation bounded := (SpecFloat.bounded prec emax).

Definition nan_pl pl :=
  Zlt_bool (Zpos (digits2_pos pl)) prec.

Notation valid_binary_SF := (valid_binary prec emax).

Definition valid_binary x :=
  match x with
  | F754_finite _ m e => bounded m e
  | F754_nan _ pl => nan_pl pl
  | _ => true
  end.

Lemma valid_binary_SF2FF :
  forall x,
  is_nan_SF x = false ->
  valid_binary (SF2FF x) = valid_binary_SF x.
Proof using .
now intros [sx|sx| |sx mx ex] H.
Qed.

Inductive binary_float :=
  | B754_zero (s : bool)
  | B754_infinity (s : bool)
  | B754_nan (s : bool) (pl : positive) :
    nan_pl pl = true -> binary_float
  | B754_finite (s : bool) (m : positive) (e : Z) :
    bounded m e = true -> binary_float.

Definition B2BSN (x : binary_float) : BinarySingleNaN.binary_float prec emax :=
  match x with
  | B754_zero s => BinarySingleNaN.B754_zero s
  | B754_infinity s => BinarySingleNaN.B754_infinity s
  | B754_nan _ _ _ => BinarySingleNaN.B754_nan
  | B754_finite s m e H => BinarySingleNaN.B754_finite s m e H
  end.

Definition FF2B x :=
  match x as x return valid_binary x = true -> binary_float with
  | F754_finite s m e => B754_finite s m e
  | F754_infinity s => fun _ => B754_infinity s
  | F754_zero s => fun _ => B754_zero s
  | F754_nan b pl => fun H => B754_nan b pl H
  end.

Definition B2FF x :=
  match x with
  | B754_finite s m e _ => F754_finite s m e
  | B754_infinity s => F754_infinity s
  | B754_zero s => F754_zero s
  | B754_nan b pl _ => F754_nan b pl
  end.

Definition B2R f :=
  match f with
  | B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

Definition B2SF (x : binary_float) :=
  match x with
  | B754_finite s m e _ => S754_finite s m e
  | B754_infinity s => S754_infinity s
  | B754_zero s => S754_zero s
  | B754_nan _ _ _ => S754_nan
  end.

Lemma B2SF_B2BSN :
  forall x,
  BinarySingleNaN.B2SF (B2BSN x) = B2SF x.
Proof using .
now intros [sx|sx|sx px Px|sx mx ex Bx].
Qed.

Lemma B2SF_FF2B :
  forall x Bx,
  B2SF (FF2B x Bx) = FF2SF x.
Proof using .
now intros [sx|sx|sx px|sx mx ex] Bx.
Qed.

Lemma B2R_B2BSN :
  forall x, BinarySingleNaN.B2R (B2BSN x) = B2R x.
Proof using .
intros x.
now destruct x.
Qed.

Lemma FF2SF_B2FF :
  forall x,
  FF2SF (B2FF x) = B2SF x.
Proof using .
now intros [sx|sx|sx plx|sx mx ex].
Qed.

Theorem FF2R_B2FF :
  forall x,
  FF2R radix2 (B2FF x) = B2R x.
Proof using .
now intros [sx|sx|sx plx Hplx|sx mx ex Hx].
Qed.

Theorem B2FF_FF2B :
  forall x Hx,
  B2FF (FF2B x Hx) = x.
Proof using .
now intros [sx|sx|sx plx|sx mx ex] Hx.
Qed.

Theorem valid_binary_B2FF :
  forall x,
  valid_binary (B2FF x) = true.
Proof using .
now intros [sx|sx|sx plx Hplx|sx mx ex Hx].
Qed.

Theorem FF2B_B2FF :
  forall x H,
  FF2B (B2FF x) H = x.
Proof using .
intros [sx|sx|sx plx Hplx|sx mx ex Hx] H ; try easy.
apply f_equal, eqbool_irrelevance.
apply f_equal, eqbool_irrelevance.
Qed.

Theorem FF2B_B2FF_valid :
  forall x,
  FF2B (B2FF x) (valid_binary_B2FF x) = x.
Proof using .
intros x.
apply FF2B_B2FF.
Qed.

Theorem B2R_FF2B :
  forall x Hx,
  B2R (FF2B x Hx) = FF2R radix2 x.
Proof using .
now intros [sx|sx|sx plx|sx mx ex] Hx.
Qed.

Theorem match_FF2B :
  forall {T} fz fi fn ff x Hx,
  match FF2B x Hx return T with
  | B754_zero sx => fz sx
  | B754_infinity sx => fi sx
  | B754_nan b p _ => fn b p
  | B754_finite sx mx ex _ => ff sx mx ex
  end =
  match x with
  | F754_zero sx => fz sx
  | F754_infinity sx => fi sx
  | F754_nan b p => fn b p
  | F754_finite sx mx ex => ff sx mx ex
  end.
Proof using .
now intros T fz fi fn ff [sx|sx|sx plx|sx mx ex] Hx.
Qed.

Theorem canonical_canonical_mantissa :
  forall (sx : bool) mx ex,
  canonical_mantissa mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof using .
intros sx mx ex H.
now apply canonical_canonical_mantissa.
Qed.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof using .
intros [sx|sx|sx plx Hx |sx mx ex Hx] ; try apply generic_format_0.
simpl.
apply generic_format_canonical.
now apply canonical_bounded.
Qed.

Theorem FLT_format_B2R :
  forall x,
  FLT_format radix2 emin prec (B2R x).
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
intros x.
apply FLT_format_generic...
apply generic_format_B2R.
Qed.

Theorem B2FF_inj :
  forall x y : binary_float,
  B2FF x = B2FF y ->
  x = y.
Proof using .
intros [sx|sx|sx plx Hplx|sx mx ex Hx] [sy|sy|sy ply Hply|sy my ey Hy] ; try easy.

intros H.
now inversion H.

intros H.
now inversion H.

intros H.
inversion H.
clear H.
revert Hplx.
rewrite H2.
intros Hx.
apply f_equal, eqbool_irrelevance.

intros H.
inversion H.
clear H.
revert Hx.
rewrite H2, H3.
intros Hx.
apply f_equal, eqbool_irrelevance.
Qed.

Definition is_finite_strict f :=
  match f with
  | B754_finite _ _ _ _ => true
  | _ => false
  end.

Lemma is_finite_strict_B2BSN :
  forall x, BinarySingleNaN.is_finite_strict (B2BSN x) = is_finite_strict x.
Proof using .
intros x.
now destruct x.
Qed.

Theorem B2R_inj:
  forall x y : binary_float,
  is_finite_strict x = true ->
  is_finite_strict y = true ->
  B2R x = B2R y ->
  x = y.
Proof using .
intros [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy.
simpl.
intros _ _ Heq.
assert (Hs: sx = sy).

revert Heq.
clear.
case sx ; case sy ; try easy ;
  intros Heq ; apply False_ind ; revert Heq.
apply Rlt_not_eq.
apply Rlt_trans with R0.
now apply F2R_lt_0.
now apply F2R_gt_0.
apply Rgt_not_eq.
apply Rgt_trans with R0.
now apply F2R_gt_0.
now apply F2R_lt_0.
assert (mx = my /\ ex = ey).

refine (_ (canonical_unique _ fexp _ _ _ _ Heq)).
rewrite Hs.
now case sy ; intro H ; injection H ; split.
now apply canonical_bounded.
now apply canonical_bounded.

revert Hx.
rewrite Hs, (proj1 H), (proj2 H).
intros Hx.
apply f_equal.
apply eqbool_irrelevance.
Qed.

Definition Bsign x :=
  match x with
  | B754_nan s _ _ => s
  | B754_zero s => s
  | B754_infinity s => s
  | B754_finite s _ _ _ => s
  end.

Theorem Bsign_FF2B :
  forall x H,
  Bsign (FF2B x H) = sign_FF x.
Proof using .
now intros [sx|sx|sx plx|sx mx ex] H.
Qed.

Definition is_finite f :=
  match f with
  | B754_finite _ _ _ _ => true
  | B754_zero _ => true
  | _ => false
  end.

Lemma is_finite_B2BSN :
  forall x, BinarySingleNaN.is_finite (B2BSN x) = is_finite x.
Proof using .
intros x.
now destruct x.
Qed.

Theorem is_finite_FF2B :
  forall x Hx,
  is_finite (FF2B x Hx) = is_finite_FF x.
Proof using .
now intros [| | |].
Qed.

Theorem is_finite_B2FF :
  forall x,
  is_finite_FF (B2FF x) = is_finite x.
Proof using .
now intros [| | |].
Qed.

Theorem B2R_Bsign_inj:
  forall x y : binary_float,
    is_finite x = true ->
    is_finite y = true ->
    B2R x = B2R y ->
    Bsign x = Bsign y ->
    x = y.
Proof using .
intros.
destruct x, y; try (apply B2R_inj; now eauto).
-
 simpl in H2.
congruence.
-
 symmetry in H1.
apply Rmult_integral in H1.
  destruct H1.
apply (eq_IZR _ 0) in H1.
destruct s0; discriminate H1.
  simpl in H1.
pose proof (bpow_gt_0 radix2 e).
  rewrite H1 in H3.
apply Rlt_irrefl in H3.
destruct H3.
-
 apply Rmult_integral in H1.
  destruct H1.
apply (eq_IZR _ 0) in H1.
destruct s; discriminate H1.
  simpl in H1.
pose proof (bpow_gt_0 radix2 e).
  rewrite H1 in H3.
apply Rlt_irrefl in H3.
destruct H3.
Qed.

Definition is_nan f :=
  match f with
  | B754_nan _ _ _ => true
  | _ => false
  end.

Lemma is_nan_B2BSN :
  forall x,
  BinarySingleNaN.is_nan (B2BSN x) =  is_nan x.
Proof using .
now intros [s|s|s p H|s m e H].
Qed.

Theorem is_nan_FF2B :
  forall x Hx,
  is_nan (FF2B x Hx) = is_nan_FF x.
Proof using .
now intros [| | |].
Qed.

Theorem is_nan_B2FF :
  forall x,
  is_nan_FF (B2FF x) = is_nan x.
Proof using .
now intros [| |? []|].
Qed.

Definition get_nan_pl (x : binary_float) : positive :=
  match x with B754_nan _ pl _ => pl | _ => xH end.

Definition build_nan (x : { x | is_nan x = true }) : binary_float.
Proof.
apply (B754_nan (Bsign (proj1_sig x)) (get_nan_pl (proj1_sig x))).
destruct x as [x H].
assert (K: false = true -> nan_pl 1 = true) by (intros K ; now elim Bool.diff_false_true).
simpl.
revert H.
destruct x as [sx|sx|sx px Px|sx mx ex Bx]; try apply K.
intros _.
apply Px.
Defined.

Theorem build_nan_correct :
  forall x : { x | is_nan x = true },
  build_nan x = proj1_sig x.
Proof using .
intros [x H].
now destruct x.
Qed.

Theorem B2R_build_nan :
  forall x, B2R (build_nan x) = 0%R.
Proof using .
easy.
Qed.

Theorem is_finite_build_nan :
  forall x, is_finite (build_nan x) = false.
Proof using .
easy.
Qed.

Theorem is_nan_build_nan :
  forall x, is_nan (build_nan x) = true.
Proof using .
easy.
Qed.

Definition BSN2B (nan : {x : binary_float | is_nan x = true }) (x : BinarySingleNaN.binary_float prec emax) : binary_float :=
  match x with
  | BinarySingleNaN.B754_nan => build_nan nan
  | BinarySingleNaN.B754_zero s => B754_zero s
  | BinarySingleNaN.B754_infinity s => B754_infinity s
  | BinarySingleNaN.B754_finite s m e H => B754_finite s m e H
  end.

Lemma B2BSN_BSN2B :
  forall nan x,
  B2BSN (BSN2B nan x) = x.
Proof using .
now intros nan [s|s| |s m e H].
Qed.

Lemma B2R_BSN2B :
  forall nan x, B2R (BSN2B nan x) = BinarySingleNaN.B2R x.
Proof using .
now intros nan [s|s| |s m e H].
Qed.

Lemma is_finite_BSN2B :
  forall nan x, is_finite (BSN2B nan x) = BinarySingleNaN.is_finite x.
Proof using .
now intros nan [s|s| |s m e H].
Qed.

Lemma is_nan_BSN2B :
  forall nan x, is_nan (BSN2B nan x) = BinarySingleNaN.is_nan x.
Proof using .
now intros nan [s|s| |s m e H].
Qed.

Lemma Bsign_B2BSN :
  forall x, is_nan x = false -> BinarySingleNaN.Bsign (B2BSN x) = Bsign x.
Proof using .
now intros [s|s| |s m e H].
Qed.

Lemma Bsign_BSN2B :
  forall nan x, BinarySingleNaN.is_nan x = false ->
  Bsign (BSN2B nan x) = BinarySingleNaN.Bsign x.
Proof using .
now intros nan [s|s| |s m e H].
Qed.

Definition BSN2B' (x : BinarySingleNaN.binary_float prec emax) : BinarySingleNaN.is_nan x = false -> binary_float.
Proof.
destruct x as [sx|sx| |sx mx ex Bx] ; intros H.
exact (B754_zero sx).
exact (B754_infinity sx).
now elim Bool.diff_true_false.
exact (B754_finite sx mx ex Bx).
Defined.

Lemma B2BSN_BSN2B' :
  forall x Nx,
  B2BSN (BSN2B' x Nx) = x.
Proof using .
now intros [s|s| |s m e H] Nx.
Qed.

Lemma B2R_BSN2B' :
  forall x Nx,
  B2R (BSN2B' x Nx) = BinarySingleNaN.B2R x.
Proof using .
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Lemma B2FF_BSN2B' :
  forall x Nx,
  B2FF (BSN2B' x Nx) = SF2FF (BinarySingleNaN.B2SF x).
Proof using .
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Lemma Bsign_BSN2B' :
  forall x Nx,
  Bsign (BSN2B' x Nx) = BinarySingleNaN.Bsign x.
Proof using .
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Lemma is_finite_BSN2B' :
  forall x Nx,
  is_finite (BSN2B' x Nx) = BinarySingleNaN.is_finite x.
Proof using .
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Lemma is_nan_BSN2B' :
  forall x Nx,
  is_nan (BSN2B' x Nx) = false.
Proof using .
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Definition erase (x : binary_float) : binary_float.
Proof.
destruct x as [s|s|s pl H|s m e H].
-
 exact (B754_zero s).
-
 exact (B754_infinity s).
-
 apply (B754_nan s pl).
  destruct nan_pl.
  apply eq_refl.
  exact H.
-
 apply (B754_finite s m e).
  destruct bounded.
  apply eq_refl.
  exact H.
Defined.

Theorem erase_correct :
  forall x, erase x = x.
Proof using .
destruct x as [s|s|s pl H|s m e H] ; try easy ; simpl.
-
 apply f_equal, eqbool_irrelevance.
-
 apply f_equal, eqbool_irrelevance.
Qed.

Definition Bopp opp_nan x :=
  match x with
  | B754_nan _ _ _ => build_nan (opp_nan x)
  | B754_infinity sx => B754_infinity (negb sx)
  | B754_finite sx mx ex Hx => B754_finite (negb sx) mx ex Hx
  | B754_zero sx => B754_zero (negb sx)
  end.

Theorem Bopp_involutive :
  forall opp_nan x,
  is_nan x = false ->
  Bopp opp_nan (Bopp opp_nan x) = x.
Proof using .
now intros opp_nan [sx|sx|sx plx|sx mx ex Hx] ; simpl ; try rewrite Bool.negb_involutive.
Qed.

Theorem B2R_Bopp :
  forall opp_nan x,
  B2R (Bopp opp_nan x) = (- B2R x)%R.
Proof using .
intros opp_nan [sx|sx|sx plx Hplx|sx mx ex Hx]; apply sym_eq ; try apply Ropp_0.
simpl.
rewrite <- F2R_opp.
now case sx.
Qed.

Theorem is_finite_Bopp :
  forall opp_nan x,
  is_finite (Bopp opp_nan x) = is_finite x.
Proof using .
now intros opp_nan [| | |].
Qed.

Lemma Bsign_Bopp :
  forall opp_nan x, is_nan x = false -> Bsign (Bopp opp_nan x) = negb (Bsign x).
Proof using .
now intros opp_nan [s|s|s pl H|s m e H].
Qed.

Definition Babs abs_nan (x : binary_float) : binary_float :=
  match x with
  | B754_nan _ _ _ => build_nan (abs_nan x)
  | B754_infinity sx => B754_infinity false
  | B754_finite sx mx ex Hx => B754_finite false mx ex Hx
  | B754_zero sx => B754_zero false
  end.

Theorem B2R_Babs :
  forall abs_nan x,
  B2R (Babs abs_nan x) = Rabs (B2R x).
Proof using .
  intros abs_nan [sx|sx|sx plx Hx|sx mx ex Hx]; apply sym_eq ; try apply Rabs_R0.
  simpl.
rewrite <- F2R_abs.
now destruct sx.
Qed.

Theorem is_finite_Babs :
  forall abs_nan x,
  is_finite (Babs abs_nan x) = is_finite x.
Proof using .
  now intros abs_nan [| | |].
Qed.

Theorem Bsign_Babs :
  forall abs_nan x,
  is_nan x = false ->
  Bsign (Babs abs_nan x) = false.
Proof using .
  now intros abs_nan [| | |].
Qed.

Theorem Babs_idempotent :
  forall abs_nan (x: binary_float),
  is_nan x = false ->
  Babs abs_nan (Babs abs_nan x) = Babs abs_nan x.
Proof using .
  now intros abs_nan [sx|sx|sx plx|sx mx ex Hx].
Qed.

Theorem Babs_Bopp :
  forall abs_nan opp_nan x,
  is_nan x = false ->
  Babs abs_nan (Bopp opp_nan x) = Babs abs_nan x.
Proof using .
  now intros abs_nan opp_nan [| | |].
Qed.

Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2).

Theorem Bcompare_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bcompare f1 f2 = Some (Rcompare (B2R f1) (B2R f2)).
Proof using .
  intros f1 f2 H1 H2.
  unfold Bcompare.
  rewrite BinarySingleNaN.Bcompare_correct.
  now rewrite 2!B2R_B2BSN.
  now rewrite is_finite_B2BSN.
  now rewrite is_finite_B2BSN.
Qed.

Theorem Bcompare_swap :
  forall x y,
  Bcompare y x = match Bcompare x y with Some c => Some (CompOpp c) | None => None end.
Proof using .
  intros.
  apply BinarySingleNaN.Bcompare_swap.
Qed.

Theorem bounded_le_emax_minus_prec :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex)
   <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof using prec_gt_0_.
now apply BinarySingleNaN.bounded_le_emax_minus_prec.
Qed.

Theorem bounded_lt_emax :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R.
Proof using .
now apply bounded_lt_emax.
Qed.

Theorem bounded_ge_emin :
  forall mx ex,
  bounded mx ex = true ->
  (bpow radix2 emin <= F2R (Float radix2 (Zpos mx) ex))%R.
Proof using .
now apply bounded_ge_emin.
Qed.

Theorem abs_B2R_le_emax_minus_prec :
  forall x,
  (Rabs (B2R x) <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof using prec_gt_0_.
intros x.
rewrite <- B2R_B2BSN.
now apply abs_B2R_le_emax_minus_prec.
Qed.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof using .
intros x.
rewrite <- B2R_B2BSN.
now apply abs_B2R_lt_emax.
Qed.

Theorem abs_B2R_ge_emin :
  forall x,
  is_finite_strict x = true ->
  (bpow radix2 emin <= Rabs (B2R x))%R.
Proof using .
intros x.
rewrite <- is_finite_strict_B2BSN.
rewrite <- B2R_B2BSN.
now apply abs_B2R_ge_emin.
Qed.

Theorem bounded_canonical_lt_emax :
  forall mx ex,
  canonical radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R ->
  bounded mx ex = true.
Proof using prec_gt_0_ prec_lt_emax_.
intros mx ex.
now apply bounded_canonical_lt_emax.
Qed.

Notation shr_fexp := (shr_fexp prec emax) (only parsing).

Theorem shr_fexp_truncate :
  forall m e l,
  (0 <= m)%Z ->
  shr_fexp m e l =
  let '(m', e', l') := truncate radix2 fexp (m, e, l) in (shr_record_of_loc m' l', e').
Proof using prec_gt_0_.
intros m e l.
now apply shr_fexp_truncate.
Qed.

Definition binary_overflow m s :=
  SF2FF (binary_overflow prec emax m s).

Lemma eq_binary_overflow_FF2SF :
  forall x m s,
  FF2SF x = BinarySingleNaN.binary_overflow prec emax m s ->
  x = binary_overflow m s.
Proof using .
intros x m s H.
unfold binary_overflow.
rewrite <- H.
apply eq_sym, SF2FF_FF2SF.
rewrite <- is_nan_FF2SF, H.
apply is_nan_binary_overflow.
Qed.

Definition binary_round_aux mode sx mx ex lx :=
  SF2FF (binary_round_aux prec emax mode sx mx ex lx).

Theorem binary_round_aux_correct' :
  forall mode x mx ex lx,
  (x <> 0)%R ->
  inbetween_float radix2 mx ex (Rabs x) lx ->
  (ex <= cexp radix2 fexp x)%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) mx ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_FF z = true /\ sign_FF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof using prec_gt_0_ prec_lt_emax_.
intros mode x mx ex lx Px Bx Ex.
generalize (binary_round_aux_correct' prec emax _ _ mode x mx ex lx Px Bx Ex).
unfold binary_round_aux.
destruct (Rlt_bool (Rabs _) _).
-
 now destruct BinarySingleNaN.binary_round_aux as [sz|sz| |sz mz ez].
-
 intros [_ ->].
  split.
  rewrite valid_binary_SF2FF by apply is_nan_binary_overflow.
  now apply binary_overflow_correct.
  easy.
Qed.

Theorem binary_round_aux_correct :
  forall mode x mx ex lx,
  inbetween_float radix2 (Zpos mx) ex (Rabs x) lx ->
  (ex <= fexp (Zdigits radix2 (Zpos mx) + ex))%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) (Zpos mx) ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_FF z = true /\ sign_FF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof using prec_gt_0_ prec_lt_emax_.
intros mode x mx ex lx Bx Ex.
generalize (binary_round_aux_correct prec emax _ _ mode x mx ex lx Bx Ex).
unfold binary_round_aux.
destruct (Rlt_bool (Rabs _) _).
-
 now destruct BinarySingleNaN.binary_round_aux as [sz|sz| |sz mz ez].
-
 intros [_ ->].
  split.
  rewrite valid_binary_SF2FF by apply is_nan_binary_overflow.
  now apply binary_overflow_correct.
  easy.
Qed.

Definition Bmult mult_nan m x y :=
  BSN2B (mult_nan x y) (Bmult m (B2BSN x) (B2BSN y)).

Theorem Bmult_correct :
  forall mult_nan m x y,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x * B2R y))) (bpow radix2 emax) then
    B2R (Bmult mult_nan m x y) = round radix2 fexp (round_mode m) (B2R x * B2R y) /\
    is_finite (Bmult mult_nan m x y) = andb (is_finite x) (is_finite y) /\
    (is_nan (Bmult mult_nan m x y) = false ->
      Bsign (Bmult mult_nan m x y) = xorb (Bsign x) (Bsign y))
  else
    B2FF (Bmult mult_nan m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof using .
intros mult_nan mode x y.
generalize (Bmult_correct prec emax _ _ mode (B2BSN x) (B2BSN y)).
replace (BinarySingleNaN.Bmult _ _ _) with (B2BSN (Bmult mult_nan mode x y)) by apply B2BSN_BSN2B.
intros H.
destruct x as [sx|sx|sx plx Hplx|sx mx ex Hx] ;
  destruct y as [sy|sy|sy ply Hply|sy my ey Hy] ;
  try ( rewrite ?Rmult_0_r, ?Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ try easy | apply bpow_gt_0 | now auto with typeclass_instances ]).
revert H.
rewrite 2!B2R_B2BSN.
destruct Rlt_bool.
-
 now destruct Bmult.
-
 intros H.
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

Definition shl_align_fexp mx ex :=
  shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex)).

Lemma shl_align_fexp_correct :
  forall mx ex,
  let (mx', ex') := shl_align_fexp mx ex in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') /\
  (ex' <= fexp (Zdigits radix2 (Zpos mx') + ex'))%Z.
Proof using .
intros mx ex.
apply shl_align_fexp_correct.
Qed.

Definition binary_round m sx mx ex :=
  SF2FF (binary_round prec emax m sx mx ex).

Theorem binary_round_correct :
  forall m sx mx ex,
  let z := binary_round m sx mx ex in
  valid_binary z = true /\
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) x)) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode m) x /\
    is_finite_FF z = true /\
    sign_FF z = sx
  else
    z = binary_overflow m sx.
Proof using prec_gt_0_ prec_lt_emax_.
intros mode sx mx ex.
generalize (binary_round_correct prec emax _ _ mode sx mx ex).
simpl.
unfold binary_round.
destruct Rlt_bool.
-
 now destruct BinarySingleNaN.binary_round.
-
 intros [H1 ->].
  split.
  rewrite valid_binary_SF2FF by apply is_nan_binary_overflow.
  now apply binary_overflow_correct.
  easy.
Qed.

Definition binary_normalize mode m e szero :=
  BSN2B' _ (is_nan_binary_normalize prec emax _ _ mode m e szero).

Theorem binary_normalize_correct :
  forall m mx ex szero,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (F2R (Float radix2 mx ex)))) (bpow radix2 emax) then
    B2R (binary_normalize m mx ex szero) = round radix2 fexp (round_mode m) (F2R (Float radix2 mx ex)) /\
    is_finite (binary_normalize m mx ex szero) = true /\
    Bsign (binary_normalize m mx ex szero) =
      match Rcompare (F2R (Float radix2 mx ex)) 0 with
        | Eq => szero
        | Lt => true
        | Gt => false
      end
  else
    B2FF (binary_normalize m mx ex szero) = binary_overflow m (Rlt_bool (F2R (Float radix2 mx ex)) 0).
Proof using .
intros mode mx ex szero.
generalize (binary_normalize_correct prec emax _ _ mode mx ex szero).
replace (BinarySingleNaN.binary_normalize _ _ _ _ _ _ _ _) with (B2BSN (binary_normalize mode mx ex szero)) by apply B2BSN_BSN2B'.
simpl.
destruct Rlt_bool.
-
 now destruct binary_normalize.
-
 intros H.
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

Definition Bplus plus_nan m x y :=
  BSN2B (plus_nan x y) (Bplus m (B2BSN x) (B2BSN y)).

Theorem Bplus_correct :
  forall plus_nan m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x + B2R y))) (bpow radix2 emax) then
    B2R (Bplus plus_nan m x y) = round radix2 fexp (round_mode m) (B2R x + B2R y) /\
    is_finite (Bplus plus_nan m x y) = true /\
    Bsign (Bplus plus_nan m x y) =
      match Rcompare (B2R x + B2R y) 0 with
        | Eq => match m with mode_DN => orb (Bsign x) (Bsign y)
                                 | _ => andb (Bsign x) (Bsign y) end
        | Lt => true
        | Gt => false
      end
  else
    (B2FF (Bplus plus_nan m x y) = binary_overflow m (Bsign x) /\ Bsign x = Bsign y).
Proof using .
Proof with auto with typeclass_instances.
intros plus_nan mode x y Fx Fy.
rewrite <- is_finite_B2BSN in Fx, Fy.
generalize (Bplus_correct prec emax _ _ mode _ _ Fx Fy).
replace (BinarySingleNaN.Bplus _ _ _) with (B2BSN (Bplus plus_nan mode x y)) by apply B2BSN_BSN2B.
rewrite 2!B2R_B2BSN.
rewrite (Bsign_B2BSN x) by (clear -Fx ; now destruct x).
rewrite (Bsign_B2BSN y) by (clear -Fy ; now destruct y).
destruct Rlt_bool.
-
 now destruct Bplus.
-
 intros [H1 H2].
  refine (conj _ H2).
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

Definition Bminus minus_nan m x y :=
  BSN2B (minus_nan x y) (Bminus m (B2BSN x) (B2BSN y)).

Theorem Bminus_correct :
  forall minus_nan m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x - B2R y))) (bpow radix2 emax) then
    B2R (Bminus minus_nan m x y) = round radix2 fexp (round_mode m) (B2R x - B2R y) /\
    is_finite (Bminus minus_nan m x y) = true /\
    Bsign (Bminus minus_nan m x y) =
      match Rcompare (B2R x - B2R y) 0 with
        | Eq => match m with mode_DN => orb (Bsign x) (negb (Bsign y))
                                 | _ => andb (Bsign x) (negb (Bsign y)) end
        | Lt => true
        | Gt => false
      end
  else
    (B2FF (Bminus minus_nan m x y) = binary_overflow m (Bsign x) /\ Bsign x = negb (Bsign y)).
Proof using .
Proof with auto with typeclass_instances.
intros minus_nan mode x y Fx Fy.
rewrite <- is_finite_B2BSN in Fx, Fy.
generalize (Bminus_correct prec emax _ _ mode _ _ Fx Fy).
replace (BinarySingleNaN.Bminus _ _ _) with (B2BSN (Bminus minus_nan mode x y)) by apply B2BSN_BSN2B.
rewrite 2!B2R_B2BSN.
rewrite (Bsign_B2BSN x) by (clear -Fx ; now destruct x).
rewrite (Bsign_B2BSN y) by (clear -Fy ; now destruct y).
destruct Rlt_bool.
-
 now destruct Bminus.
-
 intros [H1 H2].
  refine (conj _ H2).
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

Definition Bfma_szero m (x y z : binary_float) :=
  Bfma_szero prec emax m (B2BSN x) (B2BSN y) (B2BSN z).

Definition Bfma fma_nan m (x y z: binary_float) :=
  BSN2B (fma_nan x y z) (Bfma m (B2BSN x) (B2BSN y) (B2BSN z)).

Theorem Bfma_correct:
  forall fma_nan m x y z,
  is_finite x = true ->
  is_finite y = true ->
  is_finite z = true ->
  let res := (B2R x * B2R y + B2R z)%R in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) res)) (bpow radix2 emax) then
    B2R (Bfma fma_nan m x y z) = round radix2 fexp (round_mode m) res /\
    is_finite (Bfma fma_nan m x y z) = true /\
    Bsign (Bfma fma_nan m x y z) =
      match Rcompare res 0 with
        | Eq => Bfma_szero m x y z
        | Lt => true
        | Gt => false
      end
  else
    B2FF (Bfma fma_nan m x y z) = binary_overflow m (Rlt_bool res 0).
Proof using .
intros fma_nan mode x y z Fx Fy Fz.
rewrite <- is_finite_B2BSN in Fx, Fy, Fz.
generalize (Bfma_correct prec emax _ _ mode _ _ _ Fx Fy Fz).
replace (BinarySingleNaN.Bfma _ _ _ _) with (B2BSN (Bfma fma_nan mode x y z)) by apply B2BSN_BSN2B.
rewrite 3!B2R_B2BSN.
cbv zeta.
destruct Rlt_bool.
-
 now destruct Bfma.
-
 intros H.
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

Definition Bdiv div_nan m x y :=
  BSN2B (div_nan x y) (Bdiv m (B2BSN x) (B2BSN y)).

Theorem Bdiv_correct :
  forall div_nan m x y,
  B2R y <> 0%R ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x / B2R y))) (bpow radix2 emax) then
    B2R (Bdiv div_nan m x y) = round radix2 fexp (round_mode m) (B2R x / B2R y) /\
    is_finite (Bdiv div_nan m x y) = is_finite x /\
    (is_nan (Bdiv div_nan m x y) = false ->
      Bsign (Bdiv div_nan m x y) = xorb (Bsign x) (Bsign y))
  else
    B2FF (Bdiv div_nan m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof using .
intros div_nan mode x y Zy.
rewrite <- B2R_B2BSN in Zy.
generalize (Bdiv_correct prec emax _ _ mode (B2BSN x) _ Zy).
replace (BinarySingleNaN.Bdiv _ _ _) with (B2BSN (Bdiv div_nan mode x y)) by apply B2BSN_BSN2B.
unfold Rdiv.
destruct y as [sy|sy|sy ply|sy my ey Hy] ; try now elim Zy.
destruct x as [sx|sx|sx plx Hx|sx mx ex Hx] ;
  try ( simpl ; rewrite Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ simpl ; try easy ; now rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan | apply bpow_gt_0 | auto with typeclass_instances ] ).
destruct Rlt_bool.
-
 now destruct Bdiv.
-
 intros H.
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

Definition Bsqrt sqrt_nan m x :=
  BSN2B (sqrt_nan x) (Bsqrt m (B2BSN x)).

Theorem Bsqrt_correct :
  forall sqrt_nan m x,
  B2R (Bsqrt sqrt_nan m x) = round radix2 fexp (round_mode m) (sqrt (B2R x)) /\
  is_finite (Bsqrt sqrt_nan m x) = match x with B754_zero _ => true | B754_finite false _ _ _ => true | _ => false end /\
  (is_nan (Bsqrt sqrt_nan m x) = false -> Bsign (Bsqrt sqrt_nan m x) = Bsign x).
Proof using .
intros sqrt_nan mode x.
generalize (Bsqrt_correct prec emax _ _ mode (B2BSN x)).
replace (BinarySingleNaN.Bsqrt _ _) with (B2BSN (Bsqrt sqrt_nan mode x)) by apply B2BSN_BSN2B.
intros H.
destruct x as [sx|[|]|sx plx Hplx|sx mx ex Hx] ; try easy.
now destruct Bsqrt.
Qed.

Definition Bnearbyint nearbyint_nan m x :=
  BSN2B (nearbyint_nan x) (Bnearbyint m (B2BSN x)).

Theorem Bnearbyint_correct :
  forall nearbyint_nan md x,
  B2R (Bnearbyint nearbyint_nan md x) = round radix2 (FIX_exp 0) (round_mode md) (B2R x) /\
  is_finite (Bnearbyint nearbyint_nan md x) = is_finite x /\
  (is_nan (Bnearbyint nearbyint_nan md x) = false -> Bsign (Bnearbyint nearbyint_nan md x) = Bsign x).
Proof using .
intros nearbyint_nan mode x.
generalize (Bnearbyint_correct prec emax _ mode (B2BSN x)).
replace (BinarySingleNaN.Bnearbyint _ _) with (B2BSN (Bnearbyint nearbyint_nan mode x)) by apply B2BSN_BSN2B.
intros H.
destruct x as [sx|[|]|sx plx Hplx|sx mx ex Hx] ; try easy.
now destruct Bnearbyint.
Qed.

Definition Btrunc x := Btrunc (B2BSN x).

Theorem Btrunc_correct :
  forall x,
  IZR (Btrunc x) = round radix2 (FIX_exp 0) Ztrunc (B2R x).
Proof using prec_lt_emax_.
  intros x.
  rewrite <-B2R_B2BSN.
  now apply Btrunc_correct.
Qed.

Definition Bone :=
  BSN2B' _ (@is_nan_Bone prec emax _ _).

Theorem Bone_correct : B2R Bone = 1%R.
Proof using .
unfold Bone.
rewrite B2R_BSN2B'.
apply Bone_correct.
Qed.

Lemma is_finite_Bone : is_finite Bone = true.
Proof using .
unfold Bone.
rewrite is_finite_BSN2B'.
apply is_finite_Bone.
Qed.

Lemma Bsign_Bone : Bsign Bone = false.
Proof using .
unfold Bone.
rewrite Bsign_BSN2B'.
apply Bsign_Bone.
Qed.

Definition Bmax_float :=
  BSN2B' Bmax_float eq_refl.

Definition Bnormfr_mantissa x :=
  Bnormfr_mantissa (B2BSN x).

Definition lift x y (Ny : @BinarySingleNaN.is_nan prec emax y = is_nan x) : binary_float.
Proof.
destruct (is_nan x).
exact x.
now apply (BSN2B' y).
Defined.

Lemma B2BSN_lift :
  forall x y Ny,
  B2BSN (lift x y Ny) = y.
Proof using .
intros x y Ny.
unfold lift.
destruct x as [sx|sx|sx px Px|sx mx ex Bx] ; simpl ; try apply B2BSN_BSN2B'.
now destruct y.
Qed.

Definition Bldexp (mode : mode) (x : binary_float) (e : Z) : binary_float.
Proof.
apply (lift x (Bldexp mode (B2BSN x) e)).
rewrite <- is_nan_B2BSN.
apply is_nan_Bldexp.
Defined.

Theorem Bldexp_correct :
  forall m (f : binary_float) e,
  if Rlt_bool
       (Rabs (round radix2 fexp (round_mode m) (B2R f * bpow radix2 e)))
       (bpow radix2 emax) then
    (B2R (Bldexp m f e)
     = round radix2 fexp (round_mode m) (B2R f * bpow radix2 e))%R /\
    is_finite (Bldexp m f e) = is_finite f /\
    Bsign (Bldexp m f e) = Bsign f
  else
    B2FF (Bldexp m f e) = binary_overflow m (Bsign f).
Proof using .
intros mode x e.
generalize (Bldexp_correct prec emax _ _ mode (B2BSN x) e).
replace (BinarySingleNaN.Bldexp _ _ _) with (B2BSN (Bldexp mode x e)) by apply B2BSN_lift.
rewrite B2R_B2BSN.
destruct Rlt_bool.
-
 destruct x as [sx|sx|sx px Px|sx mx ex Bx] ; try easy.
  now destruct Bldexp.
-
 intros H.
  apply eq_binary_overflow_FF2SF.
  rewrite B2SF_B2BSN in H.
  rewrite FF2SF_B2FF, H.
  destruct x as [sx|sx|sx px Px|sx mx ex Bx] ; simpl in H ; try easy.
  contradict H.
  unfold BinarySingleNaN.binary_overflow.
  now destruct overflow_to_inf.
Qed.

Section Bfrexp.

Hypothesis Hemax : (2 < emax)%Z.

Definition Bfrexp (x : binary_float) : binary_float * Z.
Proof.
set (y := Bfrexp (B2BSN x)).
refine (pair _ (snd y)).
apply (lift x (fst y)).
rewrite <- is_nan_B2BSN.
apply is_nan_Bfrexp.
Defined.

Theorem Bfrexp_correct :
  forall f,
  is_finite_strict f = true ->
  let x := B2R f in
  let z := fst (Bfrexp f) in
  let e := snd (Bfrexp f) in
  (/2 <= Rabs (B2R z) < 1)%R /\
  (x = B2R z * bpow radix2 e)%R /\
  e = mag radix2 x.
Proof using Hemax.
intros x Fx.
rewrite <- is_finite_strict_B2BSN in Fx.
generalize (Bfrexp_correct prec emax _ (B2BSN x) Fx).
simpl.
rewrite <- B2R_B2BSN.
rewrite B2BSN_lift.
destruct BinarySingleNaN.Bfrexp as [z e].
rewrite B2R_B2BSN.
now intros [H1 [H2 H3]].
Qed.

End Bfrexp.

Definition Bulp (x : binary_float) : binary_float.
Proof.
apply (lift x (Bulp (B2BSN x))).
rewrite <- is_nan_B2BSN.
apply is_nan_Bulp.
Defined.

Theorem Bulp_correct :
  forall x,
  is_finite x = true ->
  B2R (Bulp x) = ulp radix2 fexp (B2R x) /\
  is_finite (Bulp x) = true /\
  Bsign (Bulp x) = false.
Proof using .
intros x Fx.
rewrite <- is_finite_B2BSN in Fx.
generalize (Bulp_correct prec emax _ _ _ Fx).
replace (BinarySingleNaN.Bulp (B2BSN x)) with (B2BSN (Bulp x)) by apply B2BSN_lift.
rewrite 2!B2R_B2BSN.
now destruct Bulp.
Qed.

Definition Bsucc (x : binary_float) : binary_float.
Proof.
apply (lift x (Bsucc (B2BSN x))).
rewrite <- is_nan_B2BSN.
apply is_nan_Bsucc.
Defined.

Lemma Bsucc_correct :
  forall x,
  is_finite x = true ->
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc x) = true /\
    (Bsign (Bsucc x) = Bsign x && is_finite_strict x)%bool
  else
    B2FF (Bsucc x) = F754_infinity false.
Proof using .
intros x Fx.
rewrite <- is_finite_B2BSN in Fx.
generalize (Bsucc_correct prec emax _ _ _ Fx).
replace (BinarySingleNaN.Bsucc (B2BSN x)) with (B2BSN (Bsucc x)) by apply B2BSN_lift.
rewrite 2!B2R_B2BSN.
destruct Rlt_bool.
-
 rewrite (Bsign_B2BSN x) by now destruct x.
  rewrite is_finite_strict_B2BSN.
  now destruct Bsucc.
-
 now destruct Bsucc as [|[|]| |].
Qed.

Definition Bpred (x : binary_float) : binary_float.
Proof.
apply (lift x (Bpred (B2BSN x))).
rewrite <- is_nan_B2BSN.
apply is_nan_Bpred.
Defined.

Lemma Bpred_correct :
  forall x,
  is_finite x = true ->
  if Rlt_bool (- bpow radix2 emax) (pred radix2 fexp (B2R x)) then
    B2R (Bpred x) = pred radix2 fexp (B2R x) /\
    is_finite (Bpred x) = true /\
    (Bsign (Bpred x) = Bsign x || negb (is_finite_strict x))%bool
  else
    B2FF (Bpred x) = F754_infinity true.
Proof using .
intros x Fx.
rewrite <- is_finite_B2BSN in Fx.
generalize (Bpred_correct prec emax _ _ _ Fx).
replace (BinarySingleNaN.Bpred (B2BSN x)) with (B2BSN (Bpred x)) by apply B2BSN_lift.
rewrite 2!B2R_B2BSN.
destruct Rlt_bool.
-
 rewrite (Bsign_B2BSN x) by now destruct x.
  rewrite is_finite_strict_B2BSN.
  now destruct Bpred.
-
 now destruct Bpred as [|[|]| |].
Qed.

End Binary.

End Binary.

End IEEE754.

End Flocq.

End Flocq_DOT_IEEE754_DOT_Binary.


Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia Stdlib.Floats.SpecFloat.
Import Flocq.Core.Core Flocq.IEEE754.BinarySingleNaN Flocq.IEEE754.Binary.

Section Binary_Bits.

Arguments exist {A} {P}.
Arguments B754_zero {prec} {emax}.
Arguments B754_infinity {prec} {emax}.
Arguments B754_nan {prec} {emax}.
Arguments B754_finite {prec} {emax}.

Variable mw ew : Z.

Definition join_bits (s : bool) m e :=
  (Z.shiftl ((if s then Zpower 2 ew else 0) + e) mw + m)%Z.

Lemma join_bits_range :
  forall s m e,
  (0 <= m < 2^mw)%Z ->
  (0 <= e < 2^ew)%Z ->
  (0 <= join_bits s m e < 2 ^ (mw + ew + 1))%Z.
Proof using .
intros s m e Hm He.
assert (0 <= mw)%Z as Hmw.
  destruct mw as [|mw'|mw'] ; try easy.
  clear -Hm ; simpl in Hm ; lia.
assert (0 <= ew)%Z as Hew.
  destruct ew as [|ew'|ew'] ; try easy.
  clear -He ; simpl in He ; lia.
unfold join_bits.
rewrite Z.shiftl_mul_pow2 by easy.
split.
-
 apply (Zplus_le_compat 0 _ 0) with (2 := proj1 Hm).
  rewrite <- (Zmult_0_l (2^mw)).
  apply Zmult_le_compat_r.
  case s.
  clear -He ; lia.
  now rewrite Zmult_0_l.
  clear -Hm ; lia.
-
 apply Z.lt_le_trans with (((if s then 2 ^ ew else 0) + e + 1) * 2 ^ mw)%Z.
  rewrite (Zmult_plus_distr_l _ 1).
  apply Zplus_lt_compat_l.
  now rewrite Zmult_1_l.
  rewrite <- (Zplus_assoc mw), (Zplus_comm mw), Zpower_plus.
  apply Zmult_le_compat_r.
  rewrite Zpower_plus by easy.
  change (2^1)%Z with 2%Z.
  case s ; clear -He ; lia.
  clear -Hm ; lia.
  clear -Hew ; lia.
  easy.
Qed.

Definition split_bits x :=
  let mm := Zpower 2 mw in
  let em := Zpower 2 ew in
  (Zle_bool (mm * em) x, Zmod x mm, Zmod (Z.div x mm) em)%Z.

Theorem split_join_bits :
  forall s m e,
  (0 <= m < Zpower 2 mw)%Z ->
  (0 <= e < Zpower 2 ew)%Z ->
  split_bits (join_bits s m e) = (s, m, e).
Proof using .
intros s m e Hm He.
assert (0 <= mw)%Z as Hmw.
  destruct mw as [|mw'|mw'] ; try easy.
  clear -Hm ; simpl in Hm ; lia.
assert (0 <= ew)%Z as Hew.
  destruct ew as [|ew'|ew'] ; try easy.
  clear -He ; simpl in He ; lia.
unfold split_bits, join_bits.
rewrite Z.shiftl_mul_pow2 by easy.
apply f_equal2 ; [apply f_equal2|].
-
 case s.
  +
 apply Zle_bool_true.
    apply Zle_0_minus_le.
    ring_simplify.
    apply Zplus_le_0_compat.
    apply Zmult_le_0_compat.
    apply He.
    clear -Hm ; lia.
    apply Hm.
  +
 apply Zle_bool_false.
    apply Zplus_lt_reg_l with (2^mw * (-e))%Z.
    replace (2 ^ mw * - e + ((0 + e) * 2 ^ mw + m))%Z with (m * 1)%Z by ring.
    rewrite <- Zmult_plus_distr_r.
    apply Z.lt_le_trans with (2^mw * 1)%Z.
    now apply Zmult_lt_compat_r.
    apply Zmult_le_compat_l.
    clear -He ; lia.
    clear -Hm ; lia.
-
 rewrite Zplus_comm.
  rewrite Z_mod_plus_full.
  now apply Zmod_small.
-
 rewrite Z_div_plus_full_l by (clear -Hm ; lia).
  rewrite Zdiv_small with (1 := Hm).
  rewrite Zplus_0_r.
  case s.
  +
 replace (2^ew + e)%Z with (e + 1 * 2^ew)%Z by ring.
    rewrite Z_mod_plus_full.
    now apply Zmod_small.
  +
 now apply Zmod_small.
Qed.

Hypothesis Hmw : (0 < mw)%Z.
Hypothesis Hew : (0 < ew)%Z.

Let prec := (mw + 1)%Z.
Let emax := Zpower 2 (ew - 1).
Notation emin := (emin prec emax) (only parsing).
Notation fexp := (fexp prec emax) (only parsing).
Notation binary_float := (binary_float prec emax) (only parsing).

Let Hprec : (0 < prec)%Z.
Proof.
unfold prec.
apply Zle_lt_succ.
now apply Zlt_le_weak.
Qed.

Let Hm_gt_0 : (0 < 2^mw)%Z.
Proof.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
Qed.

Let He_gt_0 : (0 < 2^ew)%Z.
Proof.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
Qed.

Hypothesis Hmax : (prec < emax)%Z.

Theorem join_split_bits :
  forall x,
  (0 <= x < Zpower 2 (mw + ew + 1))%Z ->
  let '(s, m, e) := split_bits x in
  join_bits s m e = x.
Proof using He_gt_0 Hm_gt_0.
intros x Hx.
unfold split_bits, join_bits.
rewrite Z.shiftl_mul_pow2 by now apply Zlt_le_weak.
pattern x at 4 ; rewrite Z.div_mod with x (2^mw)%Z.
apply (f_equal (fun v => (v + _)%Z)).
rewrite Zmult_comm.
apply f_equal.
pattern (x / (2^mw))%Z at 2 ; rewrite Z.div_mod with (x / (2^mw))%Z (2^ew)%Z.
apply (f_equal (fun v => (v + _)%Z)).
replace (x / 2 ^ mw / 2 ^ ew)%Z with (if Zle_bool (2 ^ mw * 2 ^ ew) x then 1 else 0)%Z.
case Zle_bool.
now rewrite Zmult_1_r.
now rewrite Zmult_0_r.
rewrite Zdiv_Zdiv.
apply sym_eq.
case Zle_bool_spec ; intros Hs.
apply Zle_antisym.
cut (x / (2^mw * 2^ew) < 2)%Z.
clear ; lia.
apply Zdiv_lt_upper_bound.
now apply Zmult_lt_0_compat.
rewrite <- Zpower_exp ; try ( apply Z.le_ge ; apply Zlt_le_weak ; assumption ).
change 2%Z with (Zpower 2 1) at 1.
rewrite <- Zpower_exp.
now rewrite Zplus_comm.
discriminate.
apply Z.le_ge.
now apply Zplus_le_0_compat ; apply Zlt_le_weak.
apply Zdiv_le_lower_bound.
now apply Zmult_lt_0_compat.
now rewrite Zmult_1_l.
apply Zdiv_small.
now split.
now apply Zlt_le_weak.
now apply Zlt_le_weak.
now apply Zgt_not_eq.
now apply Zgt_not_eq.
Qed.

Theorem split_bits_inj :
  forall x y,
  (0 <= x < Zpower 2 (mw + ew + 1))%Z ->
  (0 <= y < Zpower 2 (mw + ew + 1))%Z ->
  split_bits x = split_bits y ->
  x = y.
Proof using He_gt_0 Hm_gt_0.
intros x y Hx Hy.
generalize (join_split_bits x Hx) (join_split_bits y Hy).
destruct (split_bits x) as ((sx, mx), ex).
destruct (split_bits y) as ((sy, my), ey).
intros Jx Jy H.
revert Jx Jy.
inversion_clear H.
intros Jx Jy.
now rewrite <- Jx.
Qed.

Definition bits_of_binary_float (x : binary_float) :=
  match x with
  | B754_zero sx => join_bits sx 0 0
  | B754_infinity sx => join_bits sx 0 (Zpower 2 ew - 1)
  | B754_nan sx plx _ => join_bits sx (Zpos plx) (Zpower 2 ew - 1)
  | B754_finite sx mx ex _ =>
    let m := (Zpos mx - Zpower 2 mw)%Z in
    if Zle_bool 0 m then
      join_bits sx m (ex - emin + 1)
    else
      join_bits sx (Zpos mx) 0
  end.

Definition split_bits_of_binary_float (x : binary_float) :=
  match x with
  | B754_zero sx => (sx, 0, 0)%Z
  | B754_infinity sx => (sx, 0, Zpower 2 ew - 1)%Z
  | B754_nan sx plx _ => (sx, Zpos plx, Zpower 2 ew - 1)%Z
  | B754_finite sx mx ex _ =>
    let m := (Zpos mx - Zpower 2 mw)%Z in
    if Zle_bool 0 m then
      (sx, m, ex - emin + 1)%Z
    else
      (sx, Zpos mx, 0)%Z
  end.

Theorem split_bits_of_binary_float_correct :
  forall x,
  split_bits (bits_of_binary_float x) = split_bits_of_binary_float x.
Proof using He_gt_0 Hm_gt_0.
intros [sx|sx|sx plx Hplx|sx mx ex Hx] ;
  try ( simpl ; apply split_join_bits ; split ; try apply Z.le_refl ; try apply Zlt_pred ; trivial ; lia ).
simpl.
apply split_join_bits; split; try lia.
destruct (digits2_Pnat_correct plx).
unfold nan_pl in Hplx.
rewrite Zpos_digits2_pos, <- Z_of_nat_S_digits2_Pnat in Hplx.
rewrite Zpower_nat_Z in H0.
eapply Z.lt_le_trans.
apply H0.
change 2%Z with (radix_val radix2).
apply Zpower_le.
rewrite Z.ltb_lt in Hplx.
unfold prec in *.
lia.

unfold bits_of_binary_float, split_bits_of_binary_float.
assert (Hf: (emin <= ex /\ Zdigits radix2 (Zpos mx) <= prec)%Z).
destruct (andb_prop _ _ Hx) as (Hx', _).
unfold canonical_mantissa in Hx'.
rewrite Zpos_digits2_pos in Hx'.
generalize (Zeq_bool_eq _ _ Hx').
unfold fexp, FLT_exp, emin.
clear ; lia.
case Zle_bool_spec ; intros H ;
  [ apply -> Z.le_0_sub in H | apply -> Z.lt_sub_0 in H ] ;
  apply split_join_bits ; try now split.

split.
clear -He_gt_0 H ; lia.
cut (Zpos mx < 2 * 2^mw)%Z.
clear ; lia.
replace (2 * 2^mw)%Z with (2^prec)%Z.
apply (Zpower_gt_Zdigits radix2 _ (Zpos mx)).
apply Hf.
unfold prec.
rewrite Zplus_comm.
apply Zpower_exp ; apply Z.le_ge.
discriminate.
now apply Zlt_le_weak.

split.
generalize (proj1 Hf).
clear ; lia.
destruct (andb_prop _ _ Hx) as (_, Hx').
unfold emin.
replace (2^ew)%Z with (2 * emax)%Z.
generalize (Zle_bool_imp_le _ _ Hx').
clear ; lia.
apply sym_eq.
rewrite (Zsucc_pred ew).
unfold Z.succ.
rewrite Zplus_comm.
apply Zpower_exp ; apply Z.le_ge.
discriminate.
now apply Zlt_0_le_0_pred.
Qed.

Theorem bits_of_binary_float_range:
  forall x, (0 <= bits_of_binary_float x < 2^(mw+ew+1))%Z.
Proof using He_gt_0 Hm_gt_0.
unfold bits_of_binary_float.
intros [sx|sx|sx pl pl_range|sx mx ex H].
-
 apply join_bits_range ; now split.
-
 apply join_bits_range.
  now split.
  clear -He_gt_0 ; lia.
-
 apply Z.ltb_lt in pl_range.
  apply join_bits_range.
  split.
  easy.
  apply (Zpower_gt_Zdigits radix2 _ (Zpos pl)).
  apply Z.lt_succ_r.
  now rewrite <- Zdigits2_Zdigits.
  clear -He_gt_0 ; lia.
-
 unfold bounded in H.
  apply Bool.andb_true_iff in H ; destruct H as [A B].
  apply Z.leb_le in B.
  unfold canonical_mantissa, fexp, FLT_exp in A.
apply Zeq_bool_eq in A.
  case Zle_bool_spec ; intros H.
  +
 apply join_bits_range.
    *
 split.
      clear -H ; lia.
      rewrite Zpos_digits2_pos in A.
      cut (Zpos mx < 2 ^ prec)%Z.
      unfold prec.
      rewrite Zpower_plus by (clear -Hmw ; lia).
      change (2^1)%Z with 2%Z.
      clear ; lia.
      apply (Zpower_gt_Zdigits radix2 _ (Zpos mx)).
      unfold emin in A.
      clear -A ; lia.
    *
 split.
      unfold emin in A |- * ; clear -A ; lia.
      replace ew with ((ew - 1) + 1)%Z by ring.
      rewrite Zpower_plus by (clear - Hew ; lia).
      unfold emin, emax in *.
      change (2^1)%Z with 2%Z.
      clear -B ; lia.
  +
 apply -> Z.lt_sub_0 in H.
    apply join_bits_range ; now split.
Qed.

Definition binary_float_of_bits_aux x :=
  let '(sx, mx, ex) := split_bits x in
  if Zeq_bool ex 0 then
    match mx with
    | Z0 => F754_zero sx
    | Zpos px => F754_finite sx px emin
    | Zneg _ => F754_nan false xH
    end
  else if Zeq_bool ex (Zpower 2 ew - 1) then
    match mx with
      | Z0 => F754_infinity sx
      | Zpos plx => F754_nan sx plx
      | Zneg _ => F754_nan false xH
    end
  else
    match (mx + Zpower 2 mw)%Z with
    | Zpos px => F754_finite sx px (ex + emin - 1)
    | _ => F754_nan false xH
    end.

Lemma binary_float_of_bits_aux_correct :
  forall x,
  valid_binary prec emax (binary_float_of_bits_aux x) = true.
Proof using Hew Hm_gt_0 Hmax Hprec.
intros x.
unfold binary_float_of_bits_aux, split_bits.
assert (Hnan: nan_pl prec 1 = true).
  apply Z.ltb_lt.
  simpl.
unfold prec.
  clear -Hmw ; lia.
case Zeq_bool_spec ; intros He1.
case_eq (x mod 2^mw)%Z ; try easy.

intros px Hm.
assert (Zdigits radix2 (Zpos px) <= mw)%Z.
apply Zdigits_le_Zpower.
simpl.
rewrite <- Hm.
eapply Z_mod_lt.
now apply Z.lt_gt.
apply bounded_canonical_lt_emax ; try assumption.
unfold canonical, cexp.
fold emin.
rewrite mag_F2R_Zdigits.
2: discriminate.
unfold Fexp, FLT_exp.
apply sym_eq.
apply Zmax_right.
clear -H Hprec.
unfold prec ; lia.
apply Rnot_le_lt.
intros H0.
refine (_ (mag_le radix2 _ _ _ H0)).
rewrite mag_bpow.
rewrite mag_F2R_Zdigits.
2: discriminate.
unfold emin, prec.
apply Zlt_not_le.
cut (0 < emax)%Z.
clear -H Hew ; lia.
apply (Zpower_gt_0 radix2).
clear -Hew ; lia.
apply bpow_gt_0.
case Zeq_bool_spec ; intros He2.
case_eq (x mod 2 ^ mw)%Z; try easy.

intros plx Eqplx.
apply Z.ltb_lt.
rewrite Zpos_digits2_pos.
assert (forall a b, a <= b -> a < b+1)%Z by (intros; lia).
apply H.
clear H.
apply Zdigits_le_Zpower.
simpl.
rewrite <- Eqplx.
edestruct Z_mod_lt; eauto.
change 2%Z with (radix_val radix2).
apply Z.lt_gt, Zpower_gt_0.
lia.
case_eq (x mod 2^mw + 2^mw)%Z ; try easy.

intros px Hm.
assert (prec = Zdigits radix2 (Zpos px)).

rewrite Zdigits_mag.
2: discriminate.
apply sym_eq.
apply mag_unique.
rewrite <- abs_IZR.
unfold Z.abs.
replace (prec - 1)%Z with mw by ( unfold prec ; ring ).
rewrite <- IZR_Zpower with (1 := Zlt_le_weak _ _ Hmw).
rewrite <- IZR_Zpower.
2: now apply Zlt_le_weak.
rewrite <- Hm.
split.
apply IZR_le.
change (radix2^mw)%Z with (0 + 2^mw)%Z.
apply Zplus_le_compat_r.
eapply Z_mod_lt.
now apply Z.lt_gt.
apply IZR_lt.
unfold prec.
rewrite Zpower_exp.
2: now apply Z.le_ge ; apply Zlt_le_weak.
2: discriminate.
rewrite <- Zplus_diag_eq_mult_2.
apply Zplus_lt_compat_r.
eapply Z_mod_lt.
now apply Z.lt_gt.

apply bounded_canonical_lt_emax ; try assumption.
unfold canonical, cexp.
rewrite mag_F2R_Zdigits.
2: discriminate.
unfold Fexp, fexp, FLT_exp.
rewrite <- H.
set (ex := ((x / 2^mw) mod 2^ew)%Z).
replace (prec + (ex + emin - 1) - prec)%Z with (ex + emin - 1)%Z by ring.
apply sym_eq.
apply Zmax_left.
revert He1.
fold ex.
cut (0 <= ex)%Z.
unfold emin.
clear ; intros H1 H2 ; lia.
eapply Z_mod_lt.
apply Z.lt_gt.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
apply Rnot_le_lt.
intros H0.
refine (_ (mag_le radix2 _ _ _ H0)).
rewrite mag_bpow.
rewrite mag_F2R_Zdigits.
2: discriminate.
rewrite <- H.
apply Zlt_not_le.
unfold emin.
apply Zplus_lt_reg_r with (emax - 1)%Z.
ring_simplify.
revert He2.
set (ex := ((x / 2^mw) mod 2^ew)%Z).
cut (ex < 2^ew)%Z.
replace (2^ew)%Z with (2 * emax)%Z.
clear ; intros H1 H2 ; lia.
replace ew with (1 + (ew - 1))%Z by ring.
rewrite Zpower_exp.
apply refl_equal.
discriminate.
clear -Hew ; lia.
eapply Z_mod_lt.
apply Z.lt_gt.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
apply bpow_gt_0.
Qed.

Definition binary_float_of_bits x :=
  FF2B prec emax _ (binary_float_of_bits_aux_correct x).

Theorem binary_float_of_bits_of_binary_float :
  forall x,
  binary_float_of_bits (bits_of_binary_float x) = x.
Proof using .
intros x.
apply B2FF_inj.
unfold binary_float_of_bits.
rewrite B2FF_FF2B.
unfold binary_float_of_bits_aux.
rewrite split_bits_of_binary_float_correct.
destruct x as [sx|sx|sx plx Hplx|sx mx ex Bx].
apply refl_equal.

simpl.
rewrite Zeq_bool_false.
now rewrite Zeq_bool_true.
cut (1 < 2^ew)%Z.
clear ; lia.
now apply (Zpower_gt_1 radix2).

simpl.
rewrite Zeq_bool_false.
rewrite Zeq_bool_true; auto.
cut (1 < 2^ew)%Z.
clear ; lia.
now apply (Zpower_gt_1 radix2).

unfold split_bits_of_binary_float.
case Zle_bool_spec ; intros Hm.

rewrite Zeq_bool_false.
rewrite Zeq_bool_false.
now ring_simplify (Zpos mx - 2 ^ mw + 2 ^ mw)%Z (ex - emin + 1 + emin - 1)%Z.
destruct (andb_prop _ _ Bx) as (_, H1).
generalize (Zle_bool_imp_le _ _ H1).
unfold emin.
replace (2^ew)%Z with (2 * emax)%Z.
clear ; lia.
replace ew with (1 + (ew - 1))%Z by ring.
rewrite Zpower_exp.
apply refl_equal.
discriminate.
clear -Hew ; lia.
destruct (andb_prop _ _ Bx) as (H1, _).
generalize (Zeq_bool_eq _ _ H1).
rewrite Zpos_digits2_pos.
unfold FLT_exp, emin.
generalize (Zdigits radix2 (Zpos mx)).
clear.
unfold fexp, emin.
intros ; lia.

rewrite Zeq_bool_true.
2: apply refl_equal.
simpl.
apply f_equal.
destruct (andb_prop _ _ Bx) as (H1, _).
generalize (Zeq_bool_eq _ _ H1).
rewrite Zpos_digits2_pos.
unfold FLT_exp, emin, prec.
apply -> Z.lt_sub_0 in Hm.
generalize (Zdigits_le_Zpower radix2 _ (Zpos mx) Hm).
generalize (Zdigits radix2 (Zpos mx)).
clear.
unfold fexp, emin.
intros ; lia.
Qed.

Theorem bits_of_binary_float_of_bits :
  forall x,
  (0 <= x < 2^(mw+ew+1))%Z ->
  bits_of_binary_float (binary_float_of_bits x) = x.
Proof using .
intros x Hx.
unfold binary_float_of_bits, bits_of_binary_float.
set (Cx := binary_float_of_bits_aux_correct x).
clearbody Cx.
rewrite match_FF2B.
revert Cx.
generalize (join_split_bits x Hx).
unfold binary_float_of_bits_aux.
case_eq (split_bits x).
intros (sx, mx) ex Sx.
assert (Bm: (0 <= mx < 2^mw)%Z).
inversion_clear Sx.
apply Z_mod_lt.
now apply Z.lt_gt.
case Zeq_bool_spec ; intros He1.

case_eq mx.
intros Hm Jx _.
now rewrite He1 in Jx.
intros px Hm Jx _.
rewrite Zle_bool_false.
now rewrite <- He1.
apply <- Z.lt_sub_0.
now rewrite <- Hm.
intros px Hm _ _.
apply False_ind.
apply Zle_not_lt with (1 := proj1 Bm).
now rewrite Hm.
case Zeq_bool_spec ; intros He2.

case_eq mx; intros Hm.
now rewrite He2.
now rewrite He2.
intros ; lia.

case_eq (mx + 2 ^ mw)%Z.
intros Hm.
apply False_ind.
clear -Bm Hm ; lia.
intros p Hm Jx Cx.
rewrite <- Hm.
rewrite Zle_bool_true.
now ring_simplify (mx + 2^mw - 2^mw)%Z (ex + emin - 1 - emin + 1)%Z.
now ring_simplify.
intros p Hm.
apply False_ind.
clear -Bm Hm ; lia.
Qed.

End Binary_Bits.

Section B32_Bits.

Arguments B754_nan {prec} {emax}.

Definition binary32 := binary_float 24 128.

Let Hprec : (0 < 24)%Z.
Proof.
apply refl_equal.
Qed.

Let Hprec_emax : (24 < 128)%Z.
Proof.
apply refl_equal.
Qed.

Let Hemax : (3 <= 128)%Z.
Proof.
intros H.
discriminate H.
Qed.

Definition default_nan_pl32 : { nan : binary32 | is_nan 24 128 nan = true } :=
  exist _ (@B754_nan 24 128 false (iter_nat xO 22 xH) (refl_equal true)) (refl_equal true).

Definition unop_nan_pl32 (f : binary32) : { nan : binary32 | is_nan 24 128 nan = true } :=
  match f as f with
  | B754_nan s pl Hpl => exist _ (B754_nan s pl Hpl) (refl_equal true)
  | _ => default_nan_pl32
  end.

Definition binop_nan_pl32 (f1 f2 : binary32) : { nan : binary32 | is_nan 24 128 nan = true } :=
  match f1, f2 with
  | B754_nan s1 pl1 Hpl1, _ => exist _ (B754_nan s1 pl1 Hpl1) (refl_equal true)
  | _, B754_nan s2 pl2 Hpl2 => exist _ (B754_nan s2 pl2 Hpl2) (refl_equal true)
  | _, _ => default_nan_pl32
  end.

Definition ternop_nan_pl32 (f1 f2 f3 : binary32) : { nan : binary32 | is_nan 24 128 nan = true } :=
  match f1, f2, f3 with
  | B754_nan s1 pl1 Hpl1, _, _ => exist _ (B754_nan s1 pl1 Hpl1) (refl_equal true)
  | _, B754_nan s2 pl2 Hpl2, _ => exist _ (B754_nan s2 pl2 Hpl2) (refl_equal true)
  | _, _, B754_nan s3 pl3 Hpl3 => exist _ (B754_nan s3 pl3 Hpl3) (refl_equal true)
  | _, _, _ => default_nan_pl32
  end.

Definition b32_erase : binary32 -> binary32 := erase 24 128.
Definition b32_opp : binary32 -> binary32 := Bopp 24 128 unop_nan_pl32.
Definition b32_abs : binary32 -> binary32 := Babs 24 128 unop_nan_pl32.
Definition b32_pred : binary32 -> binary32 := Bpred _ _ Hprec Hprec_emax.
Definition b32_succ : binary32 -> binary32 := Bsucc _ _ Hprec Hprec_emax.
Definition b32_sqrt : mode -> binary32 -> binary32 := Bsqrt  _ _ Hprec Hprec_emax unop_nan_pl32.

Definition b32_plus :  mode -> binary32 -> binary32 -> binary32 := Bplus  _ _ Hprec Hprec_emax binop_nan_pl32.
Definition b32_minus : mode -> binary32 -> binary32 -> binary32 := Bminus _ _ Hprec Hprec_emax binop_nan_pl32.
Definition b32_mult :  mode -> binary32 -> binary32 -> binary32 := Bmult  _ _ Hprec Hprec_emax binop_nan_pl32.
Definition b32_div :   mode -> binary32 -> binary32 -> binary32 := Bdiv   _ _ Hprec Hprec_emax binop_nan_pl32.

Definition b32_fma :   mode -> binary32 -> binary32 -> binary32 -> binary32 := Bfma _ _ Hprec Hprec_emax ternop_nan_pl32.

Definition b32_compare : binary32 -> binary32 -> option comparison := Bcompare 24 128.
Definition b32_of_bits : Z -> binary32 := binary_float_of_bits 23 8 (refl_equal _) (refl_equal _) (refl_equal _).
Definition bits_of_b32 : binary32 -> Z := bits_of_binary_float 23 8.

End B32_Bits.

Section B64_Bits.

Arguments B754_nan {prec} {emax}.

Definition binary64 := binary_float 53 1024.

Let Hprec : (0 < 53)%Z.
Proof.
apply refl_equal.
Qed.

Let Hprec_emax : (53 < 1024)%Z.
Proof.
apply refl_equal.
Qed.

Let Hemax : (3 <= 1024)%Z.
Proof.
intros H.
discriminate H.
Qed.

Definition default_nan_pl64 : { nan : binary64 | is_nan 53 1024 nan = true } :=
  exist _ (@B754_nan 53 1024 false (iter_nat xO 51 xH) (refl_equal true)) (refl_equal true).

Definition unop_nan_pl64 (f : binary64) : { nan : binary64 | is_nan 53 1024 nan = true } :=
  match f as f with
  | B754_nan s pl Hpl => exist _ (B754_nan s pl Hpl) (refl_equal true)
  | _ => default_nan_pl64
  end.

Definition binop_nan_pl64 (f1 f2 : binary64) : { nan : binary64 | is_nan 53 1024 nan = true } :=
  match f1, f2 with
  | B754_nan s1 pl1 Hpl1, _ => exist _ (B754_nan s1 pl1 Hpl1) (refl_equal true)
  | _, B754_nan s2 pl2 Hpl2 => exist _ (B754_nan s2 pl2 Hpl2) (refl_equal true)
  | _, _ => default_nan_pl64
  end.

Definition ternop_nan_pl64 (f1 f2 f3 : binary64) : { nan : binary64 | is_nan 53 1024 nan = true } :=
  match f1, f2, f3 with
  | B754_nan s1 pl1 Hpl1, _, _ => exist _ (B754_nan s1 pl1 Hpl1) (refl_equal true)
  | _, B754_nan s2 pl2 Hpl2, _ => exist _ (B754_nan s2 pl2 Hpl2) (refl_equal true)
  | _, _, B754_nan s3 pl3 Hpl3 => exist _ (B754_nan s3 pl3 Hpl3) (refl_equal true)
  | _, _, _ => default_nan_pl64
  end.

Definition b64_erase : binary64 -> binary64 := erase 53 1024.
Definition b64_opp : binary64 -> binary64 := Bopp 53 1024 unop_nan_pl64.
Definition b64_abs : binary64 -> binary64 := Babs 53 1024 unop_nan_pl64.
Definition b64_pred : binary64 -> binary64 := Bpred _ _ Hprec Hprec_emax.
Definition b64_succ : binary64 -> binary64 := Bsucc _ _ Hprec Hprec_emax.
Definition b64_sqrt : mode -> binary64 -> binary64 := Bsqrt _ _ Hprec Hprec_emax unop_nan_pl64.

Definition b64_plus  : mode -> binary64 -> binary64 -> binary64 := Bplus  _ _ Hprec Hprec_emax binop_nan_pl64.
Definition b64_minus : mode -> binary64 -> binary64 -> binary64 := Bminus _ _ Hprec Hprec_emax binop_nan_pl64.
Definition b64_mult  : mode -> binary64 -> binary64 -> binary64 := Bmult  _ _ Hprec Hprec_emax binop_nan_pl64.
Definition b64_div   : mode -> binary64 -> binary64 -> binary64 := Bdiv   _ _ Hprec Hprec_emax binop_nan_pl64.

Definition b64_fma :   mode -> binary64 -> binary64 -> binary64 -> binary64 := Bfma _ _ Hprec Hprec_emax ternop_nan_pl64.

Definition b64_compare : binary64 -> binary64 -> option comparison := Bcompare 53 1024.
Definition b64_of_bits : Z -> binary64 := binary_float_of_bits 52 11 (refl_equal _) (refl_equal _) (refl_equal _).
Definition bits_of_b64 : binary64 -> Z := bits_of_binary_float 52 11.

End B64_Bits.


Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.Floats.Floats Stdlib.Floats.SpecFloat.
Import Flocq.Core.Zaux Flocq.IEEE754.BinarySingleNaN.

Definition Prim2B (x : float) : binary_float prec emax :=
  SF2B (Prim2SF x) (Prim2SF_valid x).

Definition B2Prim (x : binary_float prec emax) : float :=
  SF2Prim (B2SF x).

Lemma B2Prim_Prim2B : forall x, B2Prim (Prim2B x) = x.
Proof.
intros x.
unfold Prim2B, B2Prim.
now rewrite B2SF_SF2B, SF2Prim_Prim2SF.
Qed.

Lemma Prim2B_B2Prim : forall x, Prim2B (B2Prim x) = x.
Proof.
intro x.
unfold Prim2B, B2Prim.
apply B2SF_inj.
rewrite B2SF_SF2B.
apply Prim2SF_SF2Prim.
apply valid_binary_B2SF.
Qed.

Lemma Prim2B_inj : forall x y, Prim2B x = Prim2B y -> x = y.
Proof.
intros x y Heq.
generalize (f_equal B2Prim Heq).
now rewrite 2!B2Prim_Prim2B.
Qed.

Lemma B2Prim_inj : forall x y, B2Prim x = B2Prim y -> x = y.
Proof.
intros x y Heq.
generalize (f_equal Prim2B Heq).
now rewrite 2!Prim2B_B2Prim.
Qed.

Lemma B2SF_Prim2B : forall x, B2SF (Prim2B x) = Prim2SF x.
Proof.
intros x.
apply SF2Prim_inj.
-
 rewrite SF2Prim_Prim2SF.
  apply B2Prim_Prim2B.
-
 apply valid_binary_B2SF.
-
 apply Prim2SF_valid.
Qed.

Lemma Prim2SF_B2Prim : forall x, Prim2SF (B2Prim x) = B2SF x.
Proof.
intro x; unfold B2Prim.
now rewrite Prim2SF_SF2Prim; [ | apply valid_binary_B2SF].
Qed.

Local Instance Hprec : FLX.Prec_gt_0 prec := eq_refl _.

Local Instance Hmax : Prec_lt_emax prec emax := eq_refl _.

Theorem opp_equiv : forall x, Prim2B (- x) = Bopp (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite opp_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B as [sx|sx| |sx mx ex Bx].
Qed.

Theorem abs_equiv : forall x, Prim2B (abs x) = Babs (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite abs_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B as [sx|sx| |sx mx ex Bx].
Qed.

Theorem compare_equiv :
  forall x y,
  (x ?= y)%float = flatten_cmp_opt (Bcompare (Prim2B x) (Prim2B y)).
Proof.
intros x y.
rewrite compare_spec.
rewrite <-!B2SF_Prim2B.
now case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By].
Qed.

Lemma round_nearest_even_equiv s m l :
  round_nearest_even m l = choice_mode mode_NE s m l.
Proof.
case l; [reflexivity|intro c].
case c; [ | reflexivity..].
now simpl; unfold Round.cond_incr; case Z.even.
Qed.

Lemma binary_round_aux_equiv sx mx ex lx :
  SpecFloat.binary_round_aux prec emax sx mx ex lx
  = binary_round_aux prec emax mode_NE sx mx ex lx.
Proof.
unfold SpecFloat.binary_round_aux, binary_round_aux.
set (mrse' := shr_fexp _ _ _).
case mrse'; intros mrs' e'; simpl.
now rewrite (round_nearest_even_equiv sx).
Qed.

Theorem mul_equiv :
  forall x y,
  Prim2B (x * y) = Bmult mode_NE (Prim2B x) (Prim2B y).
Proof.
intros x y.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite mul_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By]; [now trivial.. | ].
simpl.
rewrite B2SF_SF2B.
apply binary_round_aux_equiv.
Qed.

Lemma binary_round_equiv s m e :
  SpecFloat.binary_round prec emax s m e =
  binary_round prec emax mode_NE s m e.
Proof.
unfold SpecFloat.binary_round, binary_round, shl_align_fexp.
set (mez := shl_align _ _ _); case mez as [mz ez].
apply binary_round_aux_equiv.
Qed.

Lemma binary_normalize_equiv m e szero :
  SpecFloat.binary_normalize prec emax m e szero
  = B2SF (binary_normalize prec emax Hprec Hmax mode_NE m e szero).
Proof.
case m as [ | p | p].
-
 now simpl.
-
 simpl; rewrite B2SF_SF2B; apply binary_round_equiv.
-
 simpl; rewrite B2SF_SF2B; apply binary_round_equiv.
Qed.

Theorem add_equiv :
  forall x y,
  Prim2B (x + y) = Bplus mode_NE (Prim2B x) (Prim2B y).
Proof.
intros x y.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite add_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By];
  [now (trivial || simpl; now case sx, sy).. | ].
apply binary_normalize_equiv.
Qed.

Theorem sub_equiv :
  forall x y,
  Prim2B (x - y) = Bminus mode_NE (Prim2B x) (Prim2B y).
Proof.
intros x y.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite sub_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By];
  [now (trivial || simpl; now case sx, sy).. | ].
simpl.
unfold Zminus.
rewrite <- cond_Zopp_negb.
apply binary_normalize_equiv.
Qed.

Theorem div_equiv :
  forall x y,
  Prim2B (x / y) = Bdiv mode_NE (Prim2B x) (Prim2B y).
Proof.
intros x y.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite div_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx];
  case (Prim2B y) as [sy|sy| |sy my ey By];
  [now (trivial || simpl; case Bool.eqb).. | ].
simpl.
rewrite B2SF_SF2B.
set (melz := SFdiv_core_binary _ _ _ _ _ _).
case melz as [[mz ez] lz].
apply binary_round_aux_equiv.
Qed.

Theorem sqrt_equiv :
  forall x, Prim2B (sqrt x) = Bsqrt mode_NE (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite sqrt_spec.
rewrite <-B2SF_Prim2B.
case Prim2B as [sx|sx| |sx mx ex Bx]; [now (trivial || case sx).. | ].
case sx; [reflexivity | ].
simpl.
rewrite B2SF_SF2B.
set (melz := SFsqrt_core_binary _ _ _ _).
case melz as [[mz ez] lz].
apply binary_round_aux_equiv.
Qed.

Theorem normfr_mantissa_equiv :
  forall x,
  to_Z (normfr_mantissa x) = Z.of_N (Bnormfr_mantissa (Prim2B x)).
Proof.
intro x.
rewrite normfr_mantissa_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B.
Qed.

Theorem ldexp_equiv :
  forall x e,
  Prim2B (Z.ldexp x e) = Bldexp mode_NE (Prim2B x) e.
Proof.
intros x e.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite Z_ldexp_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx]; [now trivial.. | ].
simpl.
rewrite B2SF_SF2B.
apply binary_round_equiv.
Qed.

Theorem ldshiftexp_equiv :
  forall x e,
  Prim2B (ldshiftexp x e) = Bldexp mode_NE (Prim2B x) (to_Z e - shift).
Proof.
intros x e.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite ldshiftexp_spec.
rewrite <-!B2SF_Prim2B.
case (Prim2B x) as [sx|sx| |sx mx ex Bx]; [now trivial.. | ].
simpl.
rewrite B2SF_SF2B.
apply binary_round_equiv.
Qed.

Theorem frexp_equiv :
  forall x : float,
  let (m, e) := Z.frexp x in
  (Prim2B m, e) = Bfrexp (Prim2B x).
Proof.
intro x.
generalize (Z_frexp_spec x).
destruct Z.frexp as [f e].
rewrite <-(B2SF_Prim2B x).
replace (SFfrexp _ _ _)
  with (let (f, e) := Bfrexp (Prim2B x) in
        (B2SF f, e)).
-
 case Bfrexp; intros f' e' [= H ->]; f_equal.
  now apply B2SF_inj; rewrite B2SF_Prim2B.
-
 case (Prim2B x) as [s|s| |s m e' Hme] ; try easy.
  simpl.
  rewrite B2SF_SF2B.
  unfold Ffrexp_core_binary, prec.
  change (digits2_pos m) with (Digits.digits2_pos m).
  rewrite <-?Pos2Z.inj_leb.
  now destruct Pos.leb.
Qed.

Theorem frshiftexp_equiv :
  forall x : float,
  let (m, e) := frshiftexp x in
  (Prim2B m, (to_Z e - shift)%Z) = Bfrexp (Prim2B x).
Proof.
intro x.
generalize (frexp_equiv x).
unfold Z.frexp.
now case frshiftexp.
Qed.

Theorem infinity_equiv : infinity = B2Prim (B754_infinity false).
Proof.
now compute.
Qed.

Theorem neg_infinity_equiv : neg_infinity = B2Prim (B754_infinity true).
Proof.
now compute.
Qed.

Theorem nan_equiv : nan = B2Prim B754_nan.
Proof.
now compute.
Qed.

Theorem zero_equiv : zero = B2Prim (B754_zero false).
Proof.
now compute.
Qed.

Theorem neg_zero_equiv : neg_zero = B2Prim (B754_zero true).
Proof.
now compute.
Qed.

Theorem one_equiv : one = B2Prim Bone.
Proof.
now compute.
Qed.

Theorem two_equiv : two = B2Prim (Bplus mode_NE Bone Bone).
Proof.
now compute.
Qed.

Theorem ulp_equiv :
  forall x, Prim2B (ulp x) = Bulp' (Prim2B x).
Proof.
intro x.
unfold ulp, Bulp'.
rewrite one_equiv, ldexp_equiv, Prim2B_B2Prim.
generalize (frexp_equiv x).
case Z.frexp; intros f e.
destruct Bfrexp as [f' e'].
now intros [= _ <-].
Qed.

Theorem next_up_equiv :
  forall x, Prim2B (next_up x) = Bsucc (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite next_up_spec.
rewrite <-B2SF_Prim2B.
assert (Hsndfrexp : forall x : binary_float prec emax, snd (SFfrexp prec emax (B2SF x)) = snd (Bfrexp x)).
{
 intro x'.
  generalize (Z_frexp_spec (B2Prim x')).
  generalize (frexp_equiv (B2Prim x')).
  case Z.frexp; intros f' e'.
  rewrite Prim2B_B2Prim, Prim2SF_B2Prim.
  intros H H'; generalize (f_equal snd H'); generalize (f_equal snd H); simpl.
  now intros ->.
}
assert (Hldexp : forall x e, SFldexp prec emax (B2SF x) e = B2SF (Bldexp mode_NE x e)).
{
 intros x' e'.
  rewrite <-(Prim2B_B2Prim x'), B2SF_Prim2B, <-Z_ldexp_spec.
  now rewrite <-B2SF_Prim2B, ldexp_equiv.
}
assert (Hulp : forall x, SFulp prec emax (B2SF x) = B2SF (Bulp' x)).
{
 intro x'.
  unfold SFulp, Bulp'.
  now rewrite Hsndfrexp, <-Hldexp.
}
assert (Hpred_pos : forall x, (0 < B2R x)%R -> SFpred_pos prec emax (B2SF x) = B2SF (Bpred_pos' x)).
{
 intros x' Fx'.
  unfold SFpred_pos, Bpred_pos'.
  rewrite Hsndfrexp.
  set (fe := fexp _ _ _).
  change (SFone _ _) with (B2SF Bone).
  rewrite Hldexp, Hulp.
  case x' as [sx|sx| |sx mx ex Bx]; try easy.
  unfold B2SF at 1.
  set (y := Bldexp _ _ _).
  set (z := Bulp' _).
  fold (shift_pos (Z.to_pos prec) 1).
  case Pos.eqb.
  -
 rewrite <-(Prim2B_B2Prim (B754_finite _ _ _ _)).
    rewrite <-(Prim2B_B2Prim y).
    now rewrite <-sub_equiv, !B2SF_Prim2B, sub_spec.
  -
 rewrite <-(Prim2B_B2Prim (B754_finite _ _ _ _)).
    rewrite <-(Prim2B_B2Prim z).
    now rewrite <-sub_equiv, !B2SF_Prim2B, sub_spec.
}
case Prim2B as [sx|sx| |sx mx ex Bx]; [reflexivity|now case sx|reflexivity| ].
rewrite <- Bsucc'_correct by easy.
unfold SF64succ, SFsucc, B2SF at 1, Bsucc'.
case sx.
-
 unfold B2SF at 1, SFopp at 2.
  rewrite <-(Prim2B_B2Prim (Bpred_pos' _)).
  rewrite <- opp_equiv, B2SF_Prim2B, opp_spec, Prim2SF_B2Prim.
  rewrite <- Hpred_pos.
  easy.
  now apply Float_prop.F2R_gt_0.
-
 rewrite Hulp.
  rewrite Bulp'_correct by easy.
  rewrite <-(Prim2B_B2Prim (B754_finite _ _ _ _)).
  rewrite <-(Prim2B_B2Prim (Bulp _)).
  rewrite <-add_equiv, !B2SF_Prim2B, add_spec, !Prim2SF_B2Prim.
  now unfold SF64add.
Qed.

Theorem next_down_equiv :
  forall x, Prim2B (next_down x) = Bpred (Prim2B x).
Proof.
intro x.
apply B2Prim_inj.
rewrite B2Prim_Prim2B.
apply Prim2SF_inj.
rewrite Prim2SF_B2Prim.
rewrite next_down_spec.
rewrite <-B2SF_Prim2B.
unfold Bpred.
rewrite <-(Prim2B_B2Prim (Bopp (Prim2B x))).
rewrite <-next_up_equiv, <-opp_equiv, !B2SF_Prim2B, opp_spec, next_up_spec.
unfold SF64pred, SFpred, SF64succ.
do 2 f_equal.
now rewrite <-opp_equiv, B2Prim_Prim2B, opp_spec.
Qed.

Theorem is_nan_equiv :
  forall x, PrimFloat.is_nan x = is_nan (Prim2B x).
Proof.
intro x.
unfold PrimFloat.is_nan.
rewrite eqb_spec.
rewrite <-B2SF_Prim2B.
case Prim2B as [sx|sx| |sx mx ex Bx]; [reflexivity|now case sx|reflexivity| ].
simpl.
rewrite Bool.negb_false_iff.
unfold SFeqb, SFcompare.
rewrite Z.compare_refl, Pos.compare_refl.
now case sx.
Qed.

Theorem is_zero_equiv :
  forall x,
  is_zero x = match Prim2B x with B754_zero _ => true | _ => false end.
Proof.
intro x.
unfold is_zero.
rewrite eqb_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B as [sx|sx| |sx mx ex Bx]; try reflexivity; case sx.
Qed.

Theorem is_infinity_equiv :
  forall x,
  is_infinity x = match Prim2B x with B754_infinity _ => true | _ => false end.
Proof.
intro x.
unfold is_infinity.
rewrite eqb_spec.
rewrite <-B2SF_Prim2B.
rewrite B2SF_Prim2B, abs_spec.
rewrite <-B2SF_Prim2B.
now case Prim2B.
Qed.

Theorem get_sign_equiv : forall x, get_sign x = Bsign (Prim2B x).
Proof.
intro x.
unfold get_sign.
rewrite is_zero_equiv.
rewrite ltb_spec.
rewrite <-(B2Prim_Prim2B x).
case (Prim2B x) as [sx|sx| |sx mx ex Bx]; rewrite Prim2B_B2Prim.
-
 now rewrite div_spec; case sx.
-
 now case sx.
-
 now simpl.
-
 now rewrite Prim2SF_B2Prim; case sx.
Qed.

Theorem is_finite_equiv :
  forall x, PrimFloat.is_finite x = is_finite (Prim2B x).
Proof.
intro x.
unfold PrimFloat.is_finite.
rewrite is_nan_equiv, is_infinity_equiv.
now case (Prim2B x) as [sx|sx| |sx mx ex Bx].
Qed.

Theorem of_int63_equiv :
  forall i,
  Prim2B (of_uint63 i)
  = binary_normalize prec emax Hprec Hmax mode_NE (to_Z i) 0 false.
Proof.
intro i.
apply B2SF_inj.
rewrite B2SF_Prim2B.
rewrite of_uint63_spec.
apply binary_normalize_equiv.
Qed.

Theorem eqb_equiv :
  forall x y,
  eqb x y = Beqb (Prim2B x) (Prim2B y).
Proof.
intros x y.
rewrite eqb_spec.
unfold Beqb.
now rewrite !B2SF_Prim2B.
Qed.

Theorem ltb_equiv :
  forall x y,
  ltb x y = Bltb (Prim2B x) (Prim2B y).
Proof.
intros x y.
rewrite ltb_spec.
unfold Bltb.
now rewrite !B2SF_Prim2B.
Qed.

Theorem leb_equiv :
  forall x y,
  leb x y = Bleb (Prim2B x) (Prim2B y).
Proof.
intros x y.
rewrite leb_spec.
unfold Bleb.
now rewrite !B2SF_Prim2B.
Qed.


Module Export Flocq_DOT_Prop_DOT_Plus_error.
Module Export Flocq.
Module Export AVOID_RESERVED_Prop.
Module Export Plus_error.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Core Flocq.Calc.Operations Flocq_DOT_Prop_DOT_Relative.Flocq.AVOID_RESERVED_Prop.Relative.

Section Fprop_plus_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Section round_repr_same_exp.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma round_repr_same_exp :
  forall m e,
  exists m',
  round beta fexp rnd (F2R (Float beta m e)) = F2R (Float beta m' e).
Proof using valid_rnd.
Proof with auto with typeclass_instances.
intros m e.
set (e' := cexp beta fexp (F2R (Float beta m e))).
unfold round, scaled_mantissa.
fold e'.
destruct (Zle_or_lt e' e) as [He|He].
exists m.
unfold F2R at 2.
simpl.
rewrite Rmult_assoc, <- bpow_plus.
rewrite <- IZR_Zpower by lia.
rewrite <- mult_IZR, Zrnd_IZR...
unfold F2R.
simpl.
rewrite mult_IZR.
rewrite Rmult_assoc.
rewrite IZR_Zpower by lia.
rewrite <- bpow_plus.
apply (f_equal (fun v => IZR m * bpow v)%R).
ring.
exists ((rnd (IZR m * bpow (e - e'))) * Zpower beta (e' - e))%Z.
unfold F2R.
simpl.
rewrite mult_IZR.
rewrite IZR_Zpower by lia.
rewrite 2!Rmult_assoc.
rewrite <- 2!bpow_plus.
apply (f_equal (fun v => _ * bpow v)%R).
ring.
Qed.

End round_repr_same_exp.

Context { monotone_exp : Monotone_exp fexp }.
Notation format := (generic_format beta fexp).

Variable choice : Z -> bool.

Lemma plus_error_aux :
  forall x y,
  (cexp beta fexp x <= cexp beta fexp y)%Z ->
  format x -> format y ->
  format (round beta fexp (Znearest choice) (x + y) - (x + y))%R.
Proof using monotone_exp valid_exp.
intros x y.
set (ex := cexp beta fexp x).
set (ey := cexp beta fexp y).
intros He Hx Hy.
destruct (Req_dec (round beta fexp (Znearest choice) (x + y) - (x + y)) R0) as [H0|H0].
rewrite H0.
apply generic_format_0.
set (mx := Ztrunc (scaled_mantissa beta fexp x)).
set (my := Ztrunc (scaled_mantissa beta fexp y)).

assert (Hxy: (x + y)%R = F2R (Float beta (mx + my * beta ^ (ey - ex)) ex)).
rewrite Hx, Hy.
fold mx my ex ey.
rewrite <- F2R_plus.
unfold Fplus.
simpl.
now rewrite Zle_imp_le_bool with (1 := He).

rewrite Hxy.
destruct (round_repr_same_exp (Znearest choice) (mx + my * beta ^ (ey - ex)) ex) as (mxy, Hxy').
rewrite Hxy'.
assert (H: (F2R (Float beta mxy ex) - F2R (Float beta (mx + my * beta ^ (ey - ex)) ex))%R =
  F2R (Float beta (mxy - (mx + my * beta ^ (ey - ex))) ex)).
now rewrite <- F2R_minus, Fminus_same_exp.
rewrite H.
apply generic_format_F2R.
intros _.
apply monotone_exp.
rewrite <- H, <- Hxy', <- Hxy.
apply mag_le_abs.
exact H0.
pattern x at 3 ; replace x with (-(y - (x + y)))%R by ring.
rewrite Rabs_Ropp.
now apply (round_N_pt beta _ choice (x + y)).
Qed.

Theorem plus_error :
  forall x y,
  format x -> format y ->
  format (round beta fexp (Znearest choice) (x + y) - (x + y))%R.
Proof using monotone_exp valid_exp.
intros x y Hx Hy.
destruct (Zle_or_lt (cexp beta fexp x) (cexp beta fexp y)).
now apply plus_error_aux.
rewrite Rplus_comm.
apply plus_error_aux ; try easy.
now apply Zlt_le_weak.
Qed.

End Fprop_plus_error.

Section Fprop_plus_zero.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { exp_not_FTZ : Exp_not_FTZ fexp }.
Notation format := (generic_format beta fexp).

Section round_plus_eq_zero_aux.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma round_plus_neq_0_aux :
  forall x y,
  (cexp beta fexp x <= cexp beta fexp y)%Z ->
  format x -> format y ->
  (0 < x + y)%R ->
  round beta fexp rnd (x + y) <> 0%R.
Proof using exp_not_FTZ valid_exp valid_rnd.
Proof with auto with typeclass_instances.
intros x y He Hx Hy Hxy.
destruct (mag beta (x + y)) as (exy, Hexy).
simpl.
specialize (Hexy (Rgt_not_eq _ _ Hxy)).
destruct (Zle_or_lt exy (fexp exy)) as [He'|He'].

assert (H: (x + y)%R = F2R (Float beta (Ztrunc (x * bpow (- fexp exy)) +
  Ztrunc (y * bpow (- fexp exy))) (fexp exy))).
rewrite (subnormal_exponent beta fexp exy x He' Hx) at 1.
rewrite (subnormal_exponent beta fexp exy y He' Hy) at 1.
now rewrite <- F2R_plus, Fplus_same_exp.
rewrite H.
rewrite round_generic...
rewrite <- H.
now apply Rgt_not_eq.
apply generic_format_F2R.
intros _.
rewrite <- H.
unfold cexp.
rewrite mag_unique with (1 := Hexy).
apply Z.le_refl.

intros H.
elim Rle_not_lt with (1 := round_le beta _ rnd _ _ (proj1 Hexy)).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hxy)).
rewrite H.
rewrite round_generic...
apply bpow_gt_0.
apply generic_format_bpow.
apply Zlt_succ_le.
now rewrite (Zsucc_pred exy) in He'.
Qed.

End round_plus_eq_zero_aux.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_plus_neq_0 :
  forall x y,
  format x -> format y ->
  (x + y <> 0)%R ->
  round beta fexp rnd (x + y) <> 0%R.
Proof using exp_not_FTZ valid_exp valid_rnd.
Proof with auto with typeclass_instances.
intros x y Hx Hy Hxy.
destruct (Rle_or_lt 0 (x + y)) as [H1|H1].

destruct (Zle_or_lt (cexp beta fexp x) (cexp beta fexp y)) as [H2|H2].
apply round_plus_neq_0_aux...
lra.
rewrite Rplus_comm.
apply round_plus_neq_0_aux ; try easy.
now apply Zlt_le_weak.
lra.

rewrite <- (Ropp_involutive (x + y)), Ropp_plus_distr.
rewrite round_opp.
apply Ropp_neq_0_compat.
destruct (Zle_or_lt (cexp beta fexp (-x)) (cexp beta fexp (-y))) as [H2|H2].
apply round_plus_neq_0_aux; try apply generic_format_opp...
lra.
rewrite Rplus_comm.
apply round_plus_neq_0_aux; try apply generic_format_opp...
now apply Zlt_le_weak.
lra.
Qed.

Theorem round_plus_eq_0 :
  forall x y,
  format x -> format y ->
  round beta fexp rnd (x + y) = 0%R ->
  (x + y = 0)%R.
Proof using exp_not_FTZ valid_exp valid_rnd.
Proof with auto with typeclass_instances.
intros x y Fx Fy H.
destruct (Req_dec (x + y) 0) as [H'|H'].
exact H'.
contradict H.
now apply round_plus_neq_0.
Qed.

End Fprop_plus_zero.

Section Fprop_plus_FLT.
Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Theorem FLT_format_plus_small: forall x y,
  generic_format beta (FLT_exp emin prec) x ->
  generic_format beta (FLT_exp emin prec) y ->
   (Rabs (x+y) <= bpow (prec+emin))%R ->
    generic_format beta (FLT_exp emin prec) (x+y).
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
intros x y Fx Fy H.
apply generic_format_FLT_FIX...
rewrite Zplus_comm; assumption.
apply generic_format_FIX_FLT, FIX_format_generic in Fx.
apply generic_format_FIX_FLT, FIX_format_generic in Fy.
destruct Fx as [nx H1x H2x].
destruct Fy as [ny H1y H2y].
apply generic_format_FIX.
exists (Float beta (Fnum nx+Fnum ny)%Z emin).
rewrite H1x,H1y; unfold F2R; simpl.
rewrite H2x, H2y.
rewrite plus_IZR; ring.
easy.
Qed.

Variable choice : Z -> bool.

Lemma FLT_plus_error_N_ex : forall x y,
  generic_format beta (FLT_exp emin prec) x ->
  generic_format beta (FLT_exp emin prec) y ->
  exists eps,
  (Rabs eps <= u_ro beta prec / (1 + u_ro beta prec))%R /\
  round beta (FLT_exp emin prec) (Znearest choice) (x + y)
  = ((x + y) * (1 + eps))%R.
Proof using prec_gt_0_.
intros x y Fx Fy.
assert (Pb := u_rod1pu_ro_pos beta prec).
destruct (Rle_or_lt (bpow (emin + prec - 1)) (Rabs (x + y))) as [M|M].
{
 destruct (relative_error_N_FLX'_ex beta prec prec_gt_0_ choice (x + y))
    as (d, (Bd, Hd)).
  now exists d; split; [exact Bd|]; rewrite <- Hd; apply round_FLT_FLX.
}
exists 0%R; rewrite Rabs_R0; split; [exact Pb|]; rewrite Rplus_0_r, Rmult_1_r.
apply round_generic; [apply valid_rnd_N|].
apply FLT_format_plus_small; [exact Fx|exact Fy|].
apply Rlt_le, (Rlt_le_trans _ _ _ M), bpow_le; lia.
Qed.

Lemma FLT_plus_error_N_round_ex : forall x y,
  generic_format beta (FLT_exp emin prec) x ->
  generic_format beta (FLT_exp emin prec) y ->
  exists eps,
  (Rabs eps <= u_ro beta prec)%R /\
  (x + y
   = round beta (FLT_exp emin prec) (Znearest choice) (x + y) * (1 + eps))%R.
Proof using prec_gt_0_.
intros x y Fx Fy.
now apply relative_error_N_round_ex_derive, FLT_plus_error_N_ex.
Qed.

End Fprop_plus_FLT.

Section Fprop_plus_mult_ulp.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.
Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Notation format := (generic_format beta fexp).
Notation cexp := (cexp beta fexp).

Lemma ex_shift :
  forall x e, format x -> (e <= cexp x)%Z ->
  exists m, (x = IZR m * bpow e)%R.
Proof using .
Proof with auto with typeclass_instances.
intros x e Fx He.
exists (Ztrunc (scaled_mantissa beta fexp x)*Zpower beta (cexp x -e))%Z.
rewrite Fx at 1; unfold F2R; simpl.
rewrite mult_IZR, Rmult_assoc.
f_equal.
rewrite IZR_Zpower by lia.
rewrite <- bpow_plus; f_equal; ring.
Qed.

Lemma mag_minus1 :
  forall z, z <> 0%R ->
  (mag beta z - 1)%Z = mag beta (z / IZR beta).
Proof using .
intros z Hz.
unfold Zminus.
rewrite <- mag_mult_bpow by easy.
now rewrite bpow_opp, bpow_1.
Qed.

Theorem round_plus_F2R :
  forall x y, format x -> format y -> (x <> 0)%R ->
  exists m,
  round beta fexp rnd (x+y) = F2R (Float beta m (cexp (x / IZR beta))).
Proof using monotone_exp valid_exp valid_rnd.
Proof with auto with typeclass_instances.
intros x y Fx Fy Zx.
case (Zle_or_lt (mag beta (x/IZR beta)) (mag beta y)); intros H1.
pose (e:=cexp (x / IZR beta)).
destruct (ex_shift x e) as (nx, Hnx); try exact Fx.
apply monotone_exp.
rewrite <- (mag_minus1 x Zx); lia.
destruct (ex_shift y e) as (ny, Hny); try assumption.
apply monotone_exp...
destruct (round_repr_same_exp beta fexp rnd (nx+ny) e) as (n,Hn).
exists n.
fold e.
rewrite <- Hn; f_equal.
rewrite Hnx, Hny; unfold F2R; simpl; rewrite plus_IZR; ring.
unfold F2R; simpl.

destruct (ex_shift (round beta fexp rnd (x + y)) (cexp (x/IZR beta))) as (n,Hn).
apply generic_format_round...
apply Z.le_trans with (cexp (x+y)).
apply monotone_exp.
rewrite <- mag_minus1 by easy.
rewrite <- (mag_abs beta (x+y)).

assert (U: (Rabs (x+y) = Rabs x + Rabs y)%R \/ (y <> 0 /\ Rabs (x+y) = Rabs x - Rabs y)%R).
assert (V: forall x y, (Rabs y <= Rabs x)%R ->
   (Rabs (x+y) = Rabs x + Rabs y)%R \/ (y <> 0 /\ Rabs (x+y) = Rabs x - Rabs y)%R).
clear; intros x y.
case (Rle_or_lt 0 y); intros Hy.
case Hy; intros Hy'.
case (Rle_or_lt 0 x); intros Hx.
intros _; rewrite (Rabs_pos_eq y) by easy.
rewrite (Rabs_pos_eq x) by easy.
left; apply Rabs_pos_eq.
now apply Rplus_le_le_0_compat.
rewrite (Rabs_pos_eq y) by easy.
rewrite (Rabs_left x) by easy.
intros H; right; split.
now apply Rgt_not_eq.
rewrite Rabs_left1.
ring.
apply Rplus_le_reg_l with (-x)%R; ring_simplify; assumption.
intros _; left.
now rewrite <- Hy', Rabs_R0, 2!Rplus_0_r.
case (Rle_or_lt 0 x); intros Hx.
rewrite (Rabs_left y) by easy.
rewrite (Rabs_pos_eq x) by easy.
intros H; right; split.
now apply Rlt_not_eq.
rewrite Rabs_pos_eq.
ring.
apply Rplus_le_reg_l with (-y)%R; ring_simplify; assumption.
intros _; left.
rewrite (Rabs_left y) by easy.
rewrite (Rabs_left x) by easy.
rewrite Rabs_left1.
ring.
lra.
apply V; left.
apply lt_mag with beta.
now apply Rabs_pos_lt.
rewrite <- mag_minus1 in H1; try assumption.
rewrite 2!mag_abs; lia.

destruct U as [U|U].
rewrite U; apply Z.le_trans with (mag beta x).
lia.
rewrite <- mag_abs.
apply mag_le.
now apply Rabs_pos_lt.
apply Rplus_le_reg_l with (-Rabs x)%R; ring_simplify.
apply Rabs_pos.
destruct U as (U',U); rewrite U.
rewrite <- mag_abs.
apply mag_minus_lb.
now apply Rabs_pos_lt.
now apply Rabs_pos_lt.
rewrite 2!mag_abs.
assert (mag beta y < mag beta x - 1)%Z.
now rewrite (mag_minus1 x Zx).
lia.
apply cexp_round_ge...
apply round_plus_neq_0...
contradict H1; apply Zle_not_lt.
rewrite <- (mag_minus1 x Zx).
replace y with (-x)%R.
rewrite mag_opp; lia.
lra.
now exists n.
Qed.

Context {exp_not_FTZ : Exp_not_FTZ fexp}.

Theorem round_plus_ge_ulp :
  forall x y, format x -> format y ->
  round beta fexp rnd (x+y) <> 0%R ->
  (ulp beta fexp (x/IZR beta) <= Rabs (round beta fexp rnd (x+y)))%R.
Proof using exp_not_FTZ monotone_exp valid_exp valid_rnd.
Proof with auto with typeclass_instances.
intros x y Fx Fy KK.
case (Req_dec x 0); intros Zx.

rewrite Zx, Rplus_0_l.
rewrite round_generic...
unfold Rdiv; rewrite Rmult_0_l.
rewrite Fy.
unfold F2R; simpl; rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow _)) by apply bpow_ge_0.
case (Z.eq_dec (Ztrunc (scaled_mantissa beta fexp y)) 0); intros Hm.
contradict KK.
rewrite Zx, Fy, Hm; unfold F2R; simpl.
rewrite Rplus_0_l, Rmult_0_l.
apply round_0...
apply Rle_trans with (1*bpow (cexp y))%R.
rewrite Rmult_1_l.
rewrite <- ulp_neq_0.
apply ulp_ge_ulp_0...
intros K; apply Hm.
rewrite K, scaled_mantissa_0.
apply Ztrunc_IZR.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- abs_IZR.
apply IZR_le.
apply (Zlt_le_succ 0).
now apply Z.abs_pos.

destruct (round_plus_F2R x y Fx Fy Zx) as (m,Hm).
case (Z.eq_dec m 0); intros Zm.
contradict KK.
rewrite Hm, Zm.
apply F2R_0.
rewrite Hm, <- F2R_Zabs.
rewrite ulp_neq_0.
rewrite <- (Rmult_1_l (bpow _)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le.
apply (Zlt_le_succ 0).
now apply Z.abs_pos.
apply Rmult_integral_contrapositive_currified with (1 := Zx).
apply Rinv_neq_0_compat.
apply Rgt_not_eq, radix_pos.
Qed.

End Fprop_plus_mult_ulp.

Section Fprop_plus_ge_ulp.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.
Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Theorem round_FLT_plus_ge :
  forall x y e,
  generic_format beta (FLT_exp emin prec) x -> generic_format beta (FLT_exp emin prec) y ->
  (bpow (e + prec) <= Rabs x)%R ->
  round beta (FLT_exp emin prec) rnd (x + y) <> 0%R ->
  (bpow e <= Rabs (round beta (FLT_exp emin prec) rnd (x + y)))%R.
Proof using prec_gt_0_ valid_rnd.
Proof with auto with typeclass_instances.
intros x y e Fx Fy He KK.
assert (Zx: x <> 0%R).
  contradict He.
  apply Rlt_not_le; rewrite He, Rabs_R0.
  apply bpow_gt_0.
apply Rle_trans with (ulp beta (FLT_exp emin prec) (x/IZR beta)).
2: apply round_plus_ge_ulp...
rewrite ulp_neq_0.
unfold cexp.
rewrite <- mag_minus1; try assumption.
unfold FLT_exp; apply bpow_le.
apply Z.le_trans with (2:=Z.le_max_l _ _).
destruct (mag beta x) as (n,Hn); simpl.
cut (e + prec < n)%Z.
lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=He).
now apply Hn.
apply Rmult_integral_contrapositive_currified; try assumption.
apply Rinv_neq_0_compat.
apply Rgt_not_eq.
apply radix_pos.
Qed.

Lemma round_FLT_plus_ge' :
  forall x y e,
  generic_format beta (FLT_exp emin prec) x -> generic_format beta (FLT_exp emin prec) y ->
  (x <> 0%R -> (bpow (e+prec) <= Rabs x)%R) ->
  (x = 0%R -> y <> 0%R -> (bpow e <= Rabs y)%R) ->
  round beta (FLT_exp emin prec) rnd (x+y) <> 0%R ->
  (bpow e <= Rabs (round beta (FLT_exp emin prec) rnd (x+y)))%R.
Proof using prec_gt_0_ valid_rnd.
Proof with auto with typeclass_instances.
intros x y e Fx Fy H1 H2 H3.
case (Req_dec x 0); intros H4.
case (Req_dec y 0); intros H5.
contradict H3.
rewrite H4, H5, Rplus_0_l; apply round_0...
rewrite H4, Rplus_0_l.
rewrite round_generic...
apply round_FLT_plus_ge; try easy.
now apply H1.
Qed.

Theorem round_FLX_plus_ge :
  forall x y e,
  generic_format beta (FLX_exp prec) x -> generic_format beta (FLX_exp prec) y ->
  (bpow (e+prec) <= Rabs x)%R ->
  (round beta (FLX_exp prec) rnd (x+y) <> 0)%R ->
  (bpow e <= Rabs (round beta (FLX_exp prec) rnd (x+y)))%R.
Proof using prec_gt_0_ valid_rnd.
Proof with auto with typeclass_instances.
intros x y e Fx Fy He KK.
assert (Zx: x <> 0%R).
  contradict He.
  apply Rlt_not_le; rewrite He, Rabs_R0.
  apply bpow_gt_0.
apply Rle_trans with (ulp beta (FLX_exp prec) (x/IZR beta)).
2: apply round_plus_ge_ulp...
rewrite ulp_neq_0.
unfold cexp.
rewrite <- mag_minus1 by easy.
unfold FLX_exp; apply bpow_le.
destruct (mag beta x) as (n,Hn); simpl.
cut (e + prec < n)%Z.
lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=He).
now apply Hn.
apply Rmult_integral_contrapositive_currified; try assumption.
apply Rinv_neq_0_compat.
apply Rgt_not_eq.
apply radix_pos.
Qed.

End Fprop_plus_ge_ulp.

Section Fprop_plus_le_ops.

Variable beta : radix.
Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Variable choice : Z -> bool.

Lemma plus_error_le_l :
  forall x y,
  generic_format beta fexp x -> generic_format beta fexp y ->
  (Rabs (round beta fexp (Znearest choice) (x + y) - (x + y)) <= Rabs x)%R.
Proof using valid_exp.
intros x y Fx Fy.
apply (Rle_trans _ (Rabs (y - (x + y)))); [now apply round_N_pt|].
rewrite Rabs_minus_sym; right; f_equal; ring.
Qed.

Lemma plus_error_le_r :
  forall x y,
  generic_format beta fexp x -> generic_format beta fexp y ->
  (Rabs (round beta fexp (Znearest choice) (x + y) - (x + y)) <= Rabs y)%R.
Proof using valid_exp.
now intros x y Fx Fy; rewrite Rplus_comm; apply plus_error_le_l.
Qed.

End Fprop_plus_le_ops.

End Plus_error.

End AVOID_RESERVED_Prop.

End Flocq.

End Flocq_DOT_Prop_DOT_Plus_error.


Module Export Flocq_DOT_Prop_DOT_Mult_error.
Module Export Flocq.
Module Export AVOID_RESERVED_Prop.
Module Export Mult_error.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Lia.
Import Flocq.Core.Core Flocq.Calc.Operations Flocq_DOT_Prop_DOT_Plus_error.Flocq.AVOID_RESERVED_Prop.Plus_error.

Section Fprop_mult_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (cexp beta (FLX_exp prec)).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma mult_error_FLX_aux:
  forall x y,
  format x -> format y ->
  (round beta (FLX_exp prec) rnd (x * y) - (x * y) <> 0)%R ->
  exists f:float beta,
    (F2R f = round beta (FLX_exp prec) rnd (x * y) - (x * y))%R
    /\ (cexp (F2R f) <= Fexp f)%Z
    /\ (Fexp f = cexp x + cexp y)%Z.
Proof using prec_gt_0_ valid_rnd.
Proof with auto with typeclass_instances.
intros x y Hx Hy Hz.
set (f := (round beta (FLX_exp prec) rnd (x * y))).
destruct (Req_dec (x * y) 0) as [Hxy0|Hxy0].
contradict Hz.
rewrite Hxy0.
rewrite round_0...
ring.
destruct (mag beta (x * y)) as (exy, Hexy).
specialize (Hexy Hxy0).
destruct (mag beta (f - x * y)) as (er, Her).
specialize (Her Hz).
destruct (mag beta x) as (ex, Hex).
assert (Hx0: (x <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_l.
specialize (Hex Hx0).
destruct (mag beta y) as (ey, Hey).
assert (Hy0: (y <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_r.
specialize (Hey Hy0).

assert (Hc1: (cexp (x * y)%R - prec <= cexp x + cexp y)%Z).
unfold cexp, FLX_exp.
rewrite mag_unique with (1 := Hex).
rewrite mag_unique with (1 := Hey).
rewrite mag_unique with (1 := Hexy).
cut (exy - 1 < ex + ey)%Z.
lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := proj1 Hexy).
rewrite Rabs_mult.
rewrite bpow_plus.
apply Rmult_le_0_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Hex.
apply Hey.

assert (Hc2: (cexp x + cexp y <= cexp (x * y)%R)%Z).
unfold cexp, FLX_exp.
rewrite mag_unique with (1 := Hex).
rewrite mag_unique with (1 := Hey).
rewrite mag_unique with (1 := Hexy).
cut ((ex - 1) + (ey - 1) < exy)%Z.
generalize (prec_gt_0 prec).
clear ; lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 Hexy).
rewrite Rabs_mult.
rewrite bpow_plus.
apply Rmult_le_compat.
apply bpow_ge_0.
apply bpow_ge_0.
apply Hex.
apply Hey.

assert (Hr: ((F2R (Float beta (- (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) *
  Ztrunc (scaled_mantissa beta (FLX_exp prec) y)) + rnd (scaled_mantissa beta (FLX_exp prec) (x * y)) *
  beta ^ (cexp (x * y)%R - (cexp x + cexp y))) (cexp x + cexp y))) = f - x * y)%R).
rewrite Hx at 6.
rewrite Hy at 6.
rewrite <- F2R_mult.
simpl.
unfold f, round, Rminus.
rewrite <- F2R_opp, Rplus_comm, <- F2R_plus.
unfold Fplus.
simpl.
now rewrite Zle_imp_le_bool with (1 := Hc2).

exists (Float beta (- (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) *
  Ztrunc (scaled_mantissa beta (FLX_exp prec) y)) + rnd (scaled_mantissa beta (FLX_exp prec) (x * y)) *
  beta ^ (cexp (x * y)%R - (cexp x + cexp y))) (cexp x + cexp y)).
split;[assumption|split].
rewrite Hr.
simpl.
clear Hr.
apply Z.le_trans with (cexp (x * y)%R - prec)%Z.
unfold cexp, FLX_exp.
apply Zplus_le_compat_r.
rewrite mag_unique with (1 := Hexy).
apply mag_le_bpow with (1 := Hz).
replace (bpow (exy - prec)) with (ulp beta (FLX_exp prec) (x * y)).
apply error_lt_ulp...
rewrite ulp_neq_0; trivial.
unfold cexp.
now rewrite mag_unique with (1 := Hexy).
apply Hc1.
reflexivity.
Qed.

Theorem mult_error_FLX :
  forall x y,
  format x -> format y ->
  format (round beta (FLX_exp prec) rnd (x * y) - (x * y))%R.
Proof using prec_gt_0_ valid_rnd.
intros x y Hx Hy.
destruct (Req_dec (round beta (FLX_exp prec) rnd (x * y) - x * y) 0) as [Hr0|Hr0].
rewrite Hr0.
apply generic_format_0.
destruct (mult_error_FLX_aux x y Hx Hy Hr0) as ((m,e),(H1,(H2,H3))).
rewrite <- H1.
now apply generic_format_F2R.
Qed.

Lemma mult_bpow_exact_FLX :
  forall x e,
  format x ->
  format (x * bpow e)%R.
Proof using .
intros x e Fx.
destruct (Req_dec x 0) as [Zx|Nzx].
{
 rewrite Zx, Rmult_0_l; apply generic_format_0.
}
rewrite Fx.
set (mx := Ztrunc _); set (ex := cexp _).
pose (f := {| Fnum := mx; Fexp := ex + e |} : float beta).
apply (generic_format_F2R' _ _ _ f).
{
 now unfold F2R; simpl; rewrite bpow_plus, Rmult_assoc.
}
intro Nzmx; unfold mx, ex; rewrite <- Fx.
unfold f, ex; simpl; unfold cexp; rewrite (mag_mult_bpow _ _ _ Nzx).
unfold FLX_exp; lia.
Qed.

End Fprop_mult_error.

Section Fprop_mult_error_FLT.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation cexp := (cexp beta (FLT_exp emin prec)).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem mult_error_FLT :
  forall x y,
  format x -> format y ->
  (x * y <> 0 -> bpow (emin + 2*prec - 1) <= Rabs (x * y))%R ->
  format (round beta (FLT_exp emin prec) rnd (x * y) - (x * y))%R.
Proof using prec_gt_0_ valid_rnd.
Proof with auto with typeclass_instances.
intros x y Hx Hy Hxy.
set (f := (round beta (FLT_exp emin prec) rnd (x * y))).
destruct (Req_dec (f - x * y) 0) as [Hr0|Hr0].
rewrite Hr0.
apply generic_format_0.
destruct (Req_dec (x * y) 0) as [Hxy'|Hxy'].
unfold f.
rewrite Hxy'.
rewrite round_0...
ring_simplify (0 - 0)%R.
apply generic_format_0.
specialize (Hxy Hxy').
destruct (mult_error_FLX_aux beta prec rnd x y) as ((m,e),(H1,(H2,H3))).
now apply generic_format_FLX_FLT with emin.
now apply generic_format_FLX_FLT with emin.
rewrite <- (round_FLT_FLX beta emin).
assumption.
apply Rle_trans with (2:=Hxy).
apply bpow_le.
generalize (prec_gt_0 prec).
clear ; lia.
rewrite <- (round_FLT_FLX beta emin) in H1.
2:apply Rle_trans with (2:=Hxy).
2:apply bpow_le ; generalize (prec_gt_0 prec) ; clear ; lia.
unfold f; rewrite <- H1.
apply generic_format_F2R.
intros _.
simpl in H2, H3.
unfold cexp, FLT_exp.
case (Zmax_spec (mag beta (F2R (Float beta m e)) - prec) emin);
  intros (M1,M2); rewrite M2.
apply Z.le_trans with (2:=H2).
unfold cexp, FLX_exp.
apply Z.le_refl.
rewrite H3.
unfold cexp, FLX_exp.
assert (Hxy0:(x*y <> 0)%R).
contradict Hr0.
unfold f.
rewrite Hr0.
rewrite round_0...
ring.
assert (Hx0: (x <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_l.
assert (Hy0: (y <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_r.
destruct (mag beta x) as (ex,Ex) ; simpl.
specialize (Ex Hx0).
destruct (mag beta y) as (ey,Ey) ; simpl.
specialize (Ey Hy0).
cut (emin + 2 * prec -1 < ex + ey)%Z.
lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (1:=Hxy).
rewrite Rabs_mult, bpow_plus.
apply Rmult_le_0_lt_compat; try apply Rabs_pos.
apply Ex.
apply Ey.
Qed.

Lemma F2R_ge: forall (y:float beta),
   (F2R y <> 0)%R -> (bpow (Fexp y) <= Rabs (F2R y))%R.
Proof using .
intros (ny,ey).
rewrite <- F2R_Zabs; unfold F2R; simpl.
case (Zle_lt_or_eq 0 (Z.abs ny)).
apply Z.abs_nonneg.
intros Hy _.
rewrite <- (Rmult_1_l (bpow _)) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le; lia.
intros H1 H2; contradict H2.
replace ny with 0%Z.
simpl; ring.
now apply sym_eq, Z.abs_0_iff, sym_eq.
Qed.

Theorem mult_error_FLT_ge_bpow :
  forall x y e,
  format x -> format y ->
  (bpow (e+2*prec-1) <= Rabs (x * y))%R ->
  (round beta (FLT_exp emin prec) rnd (x * y) - (x * y) <> 0)%R ->
  (bpow e <= Rabs (round beta (FLT_exp emin prec) rnd (x * y) - (x * y)))%R.
Proof using valid_rnd.
Proof with auto with typeclass_instances.
intros x y e.
set (f := (round beta (FLT_exp emin prec) rnd (x * y))).
intros Fx Fy H1.
unfold f; rewrite Fx, Fy, <- F2R_mult.
simpl Fmult.
destruct (round_repr_same_exp beta (FLT_exp emin prec)
 rnd (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x) *
             Ztrunc (scaled_mantissa beta (FLT_exp emin prec) y))
      (cexp x + cexp y)) as (n,Hn).
rewrite Hn; clear Hn.
rewrite <- F2R_minus, Fminus_same_exp.
intros K.
eapply Rle_trans with (2:=F2R_ge _ K).
simpl (Fexp _).
apply bpow_le.
unfold cexp, FLT_exp.
destruct (mag beta x) as (ex,Hx).
destruct (mag beta y) as (ey,Hy).
simpl; apply Z.le_trans with ((ex-prec)+(ey-prec))%Z.
2: apply Zplus_le_compat; apply Z.le_max_l.
cut (e + 2*prec -1< ex+ey)%Z.
lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=H1).
rewrite Rabs_mult, bpow_plus.
apply Rmult_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Hx.
intros K'; contradict H1; apply Rlt_not_le.
rewrite K', Rmult_0_l, Rabs_R0; apply bpow_gt_0.
apply Hy.
intros K'; contradict H1; apply Rlt_not_le.
rewrite K', Rmult_0_r, Rabs_R0; apply bpow_gt_0.
Qed.

Lemma mult_bpow_exact_FLT :
  forall x e,
  format x ->
  (emin + prec - mag beta x <= e)%Z ->
  format (x * bpow e)%R.
Proof using .
intros x e Fx He.
destruct (Req_dec x 0) as [Zx|Nzx].
{
 rewrite Zx, Rmult_0_l; apply generic_format_0.
}
rewrite Fx.
set (mx := Ztrunc _); set (ex := cexp _).
pose (f := {| Fnum := mx; Fexp := ex + e |} : float beta).
apply (generic_format_F2R' _ _ _ f).
{
 now unfold F2R; simpl; rewrite bpow_plus, Rmult_assoc.
}
intro Nzmx; unfold mx, ex; rewrite <- Fx.
unfold f, ex; simpl; unfold cexp; rewrite (mag_mult_bpow _ _ _ Nzx).
unfold FLT_exp; rewrite Z.max_l by lia; rewrite <- Z.add_max_distr_r.
set (n := (_ - _ + _)%Z); apply (Z.le_trans _ n); [unfold n; lia|].
apply Z.le_max_l.
Qed.

Lemma mult_bpow_pos_exact_FLT :
  forall x e,
  format x ->
  (0 <= e)%Z ->
  format (x * bpow e)%R.
Proof using .
intros x e Fx He.
destruct (Req_dec x 0) as [Zx|Nzx].
{
 rewrite Zx, Rmult_0_l; apply generic_format_0.
}
rewrite Fx.
set (mx := Ztrunc _); set (ex := cexp _).
pose (f := {| Fnum := mx; Fexp := ex + e |} : float beta).
apply (generic_format_F2R' _ _ _ f).
{
 now unfold F2R; simpl; rewrite bpow_plus, Rmult_assoc.
}
intro Nzmx; unfold mx, ex; rewrite <- Fx.
unfold f, ex; simpl; unfold cexp; rewrite (mag_mult_bpow _ _ _ Nzx).
unfold FLT_exp; rewrite <-Z.add_max_distr_r.
replace (_ - _ + e)%Z with (mag beta x + e - prec)%Z; [ |ring].
apply Z.max_le_compat_l; lia.
Qed.

End Fprop_mult_error_FLT.

End Mult_error.

End AVOID_RESERVED_Prop.

End Flocq.

End Flocq_DOT_Prop_DOT_Mult_error.


Module Export Flocq_DOT_Prop_DOT_Sterbenz.
Module Export Flocq.
Module Export AVOID_RESERVED_Prop.
Module Export Sterbenz.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Generic_fmt Flocq.Calc.Operations.

Section Fprop_Sterbenz.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.
Notation format := (generic_format beta fexp).

Theorem generic_format_plus :
  forall x y,
  format x -> format y ->
  (Rabs (x + y) <= bpow (Z.min (mag beta x) (mag beta y)))%R ->
  format (x + y)%R.
Proof using monotone_exp valid_exp.
intros x y Fx Fy Hxy.
destruct (Req_dec (x + y) 0) as [Zxy|Zxy].
rewrite Zxy.
apply generic_format_0.
destruct (Req_dec x R0) as [Zx|Zx].
now rewrite Zx, Rplus_0_l.
destruct (Req_dec y R0) as [Zy|Zy].
now rewrite Zy, Rplus_0_r.
destruct Hxy as [Hxy|Hxy].
revert Hxy.
destruct (mag beta x) as (ex, Ex).
simpl.
specialize (Ex Zx).
destruct (mag beta y) as (ey, Ey).
simpl.
specialize (Ey Zy).
intros Hxy.
set (fx := Float beta (Ztrunc (scaled_mantissa beta fexp x)) (fexp ex)).
assert (Hx: x = F2R fx).
rewrite Fx at 1.
unfold cexp.
now rewrite mag_unique with (1 := Ex).
set (fy := Float beta (Ztrunc (scaled_mantissa beta fexp y)) (fexp ey)).
assert (Hy: y = F2R fy).
rewrite Fy at 1.
unfold cexp.
now rewrite mag_unique with (1 := Ey).
rewrite Hx, Hy.
rewrite <- F2R_plus.
apply generic_format_F2R.
intros _.
case_eq (Fplus fx fy).
intros mxy exy Pxy; simpl.
rewrite <- Pxy, F2R_plus, <- Hx, <- Hy.
unfold cexp.
replace exy with (fexp (Z.min ex ey)).
apply monotone_exp.
now apply mag_le_bpow.
replace exy with (Fexp (Fplus fx fy)) by exact (f_equal Fexp Pxy).
rewrite Fexp_Fplus.
simpl.
clear -monotone_exp.
apply sym_eq.
destruct (Zmin_spec ex ey) as [(H1,H2)|(H1,H2)] ; rewrite H2.
apply Z.min_l.
now apply monotone_exp.
apply Z.min_r.
apply monotone_exp.
apply Zlt_le_weak.
now apply Z.gt_lt.
apply generic_format_abs_inv.
rewrite Hxy.
apply generic_format_bpow.
apply valid_exp.
case (Zmin_spec (mag beta x) (mag beta y)); intros (H1,H2);
   rewrite H2; now apply mag_generic_gt.
Qed.

Theorem generic_format_plus_weak :
  forall x y,
  format x -> format y ->
  (Rabs (x + y) <= Rmin (Rabs x) (Rabs y))%R ->
  format (x + y)%R.
Proof using monotone_exp valid_exp.
intros x y Fx Fy Hxy.
destruct (Req_dec x R0) as [Zx|Zx].
now rewrite Zx, Rplus_0_l.
destruct (Req_dec y R0) as [Zy|Zy].
now rewrite Zy, Rplus_0_r.
apply generic_format_plus ; try assumption.
apply Rle_trans with (1 := Hxy).
unfold Rmin.
destruct (Rle_dec (Rabs x) (Rabs y)) as [Hxy'|Hxy'].
rewrite Z.min_l.
destruct (mag beta x) as (ex, Hx).
apply Rlt_le; now apply Hx.
now apply mag_le_abs.
rewrite Z.min_r.
destruct (mag beta y) as (ex, Hy).
apply Rlt_le; now apply Hy.
apply mag_le_abs.
exact Zy.
apply Rlt_le.
now apply Rnot_le_lt.
Qed.

Lemma sterbenz_aux :
  forall x y, format x -> format y ->
  (y <= x <= 2 * y)%R ->
  format (x - y)%R.
Proof using monotone_exp valid_exp.
intros x y Hx Hy (Hxy1, Hxy2).
unfold Rminus.
apply generic_format_plus_weak.
exact Hx.
now apply generic_format_opp.
rewrite Rabs_pos_eq.
rewrite Rabs_Ropp.
rewrite Rmin_comm.
assert (Hy0: (0 <= y)%R).
apply Rplus_le_reg_r with y.
apply Rle_trans with x.
now rewrite Rplus_0_l.
now replace (y + y)%R with (2 * y)%R by ring.
rewrite Rabs_pos_eq with (1 := Hy0).
rewrite Rabs_pos_eq.
unfold Rmin.
destruct (Rle_dec y x) as [Hyx|Hyx].
apply Rplus_le_reg_r with y.
now ring_simplify.
now elim Hyx.
now apply Rle_trans with y.
now apply Rle_0_minus.
Qed.

Theorem sterbenz :
  forall x y, format x -> format y ->
  (y / 2 <= x <= 2 * y)%R ->
  format (x - y)%R.
Proof using monotone_exp valid_exp.
intros x y Hx Hy (Hxy1, Hxy2).
destruct (Rle_or_lt x y) as [Hxy|Hxy].
rewrite <- Ropp_minus_distr.
apply generic_format_opp.
apply sterbenz_aux ; try easy.
split.
exact Hxy.
apply Rcompare_not_Lt_inv.
rewrite <- Rcompare_half_r.
now apply Rcompare_not_Lt.
apply sterbenz_aux ; try easy.
split.
now apply Rlt_le.
exact Hxy2.
Qed.

End Fprop_Sterbenz.

End Sterbenz.

End AVOID_RESERVED_Prop.

End Flocq.

End Flocq_DOT_Prop_DOT_Sterbenz.

Module Export Flocq.
Module Export Pff.
Module Export Pff2FlocqAux.

Import Stdlib.micromega.Lia.
Import Flocq.Pff.Pff Flocq.Core.Core.

Section RND_Closest_c.

Variable b : Fbound.
Variable beta : radix.
Variable p : nat.

Coercion FtoRradix := FtoR beta.
Hypothesis pGreaterThanOne : 1 < p.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat beta p.

Variable choice: Z -> bool.

Definition RND_Closest (r : R) :=
   let ru := RND_Max b beta p r in
   let rd := RND_Min b beta p r in
  match Rle_dec (Rabs (ru - r)) (Rabs (rd - r)) with
  | left H =>
      match
        Rle_lt_or_eq_dec (Rabs (ru - r)) (Rabs (rd - r)) H
      with
      | left _ => ru
      | right _ =>
          match choice (Zfloor (scaled_mantissa beta (FLT_exp (- dExp b) p) r)) with
          | true => ru
          | false => rd
          end
      end
  | right _ => rd
  end.

Theorem RND_Closest_canonic :
 forall r : R, Fcanonic beta b (RND_Closest r).
Proof using pGivesBound pGreaterThanOne.
intros r; unfold RND_Closest in |- *.
case (Rle_dec _ _ ); intros H1.
case (Rle_lt_or_eq_dec _ _ H1); intros H2.
apply RND_Max_canonic; try easy; apply radix_gt_1.
case (choice _).
now apply RND_Max_canonic; try easy; apply radix_gt_1.
now apply RND_Min_canonic; try easy; apply radix_gt_1.
now apply RND_Min_canonic; try easy; apply radix_gt_1.
Qed.

Theorem RND_Closest_correct :
 forall r : R, Closest b beta r (RND_Closest r).
Proof using pGivesBound pGreaterThanOne.
intros r.
generalize (radix_gt_1 beta); intros M.
split.
apply FcanonicBound with beta; apply RND_Closest_canonic.
intros f H3; fold FtoRradix.

cut (RND_Min b beta p r <= r)%R; [ intros V1 | idtac ].
2: apply (RND_Min_correct b beta p) with (r:=r); easy.
cut (r <= RND_Max b beta p r)%R; [ intros V2 | idtac ].
2: apply (RND_Max_correct b beta p) with (r:=r); easy.
cut (forall v w : R, (v <= w)%R -> (0 <= w - v)%R); [ intros V3 | idtac ].
2: intros v w H; apply Rplus_le_reg_l with v; ring_simplify; auto with real.
cut (forall v w : R, (v <= w)%R -> (v - w <= 0)%R); [ intros V4 | idtac ].
2: intros v w H; apply Rplus_le_reg_l with w; ring_simplify; auto with real.

unfold RND_Closest; case (Rle_dec _ _); intros H1.
case (Rle_lt_or_eq_dec _ _ H1); intros H2.

rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H4.
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H1); apply Ropp_le_contravar;
 unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Min_correct b beta p) with (r:=r); easy.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Max_correct b beta p) with (r:=r); try easy.
now apply Rlt_le.

case (choice _).
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H5.
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H1); apply Ropp_le_contravar;
 unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Min_correct b beta p) with (r:=r); easy.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Max_correct b beta p) with (r:=r); try easy.
now apply Rlt_le.

rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite <- H2.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
case (Rle_or_lt f r); intros H5.
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
apply Rle_trans with (1 := H1); apply Ropp_le_contravar;
 unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Min_correct b beta p) with (r:=r); easy.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
unfold Rminus in |- *; apply Rplus_le_compat_r.
apply (RND_Max_correct b beta p) with (r:=r); try easy.
now apply Rlt_le.

apply Rnot_le_lt in H1.
rewrite Rabs_left1 in H1; [ idtac | apply V4; auto with real ].
rewrite Rabs_right in H1; [ idtac | apply Rle_ge; apply V3; auto with real ].
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
case (Rle_or_lt f r); intros H4.
rewrite Rabs_left1; [ idtac | apply V4; auto with real ].
apply Ropp_le_contravar, Rplus_le_compat_r.
apply (RND_Min_correct b beta p) with (r:=r); easy.
rewrite Rabs_right; [ idtac | apply Rle_ge; apply V3; auto with real ].
left; apply Rlt_le_trans with (1:=H1).
apply Rplus_le_compat_r.
apply (RND_Max_correct b beta p) with (r:=r); try easy.
now left.
Qed.

End RND_Closest_c.

Section Bounds.

Variable beta : radix.
Variable p E:Z.
Hypothesis precisionNotZero : (1 < p)%Z.

Definition make_bound := Bound
      (Z.to_pos (Zpower beta p))
      (Z.abs_N E).

Lemma make_bound_Emin: (E <= 0)%Z ->
        ((Z_of_N (dExp (make_bound)))=-E)%Z.
Proof using .
simpl.
rewrite Zabs2N.id_abs.
now apply Z.abs_neq.
Qed.

Lemma make_bound_p:
        Zpos (vNum (make_bound))=(Zpower_nat beta (Z.abs_nat p)).
Proof using precisionNotZero.
unfold make_bound, vNum; simpl.
rewrite Z2Pos.id.
apply Zpower_nat_Zpower.
lia.
generalize (Zpower_gt_0 beta); simpl.
intros T; apply T.
lia.
Qed.

Lemma FtoR_F2R: forall (f:Pff.float) (g: float beta), Pff.Fnum f = Fnum g -> Pff.Fexp f = Fexp g ->
  FtoR beta f = F2R g.
Proof using .
intros f g H1 H2; unfold FtoR, F2R.
rewrite H1, H2.
now rewrite bpow_powerRZ.
Qed.

End Bounds.
Section b_Bounds.

Definition bsingle := make_bound radix2 24 (-149)%Z.

Lemma psGivesBound: Zpos (vNum bsingle) = Zpower_nat 2 24.
Proof.
unfold bsingle; apply make_bound_p.
lia.
Qed.

Definition bdouble := make_bound radix2 53 1074.

Lemma pdGivesBound: Zpos (vNum bdouble) = Zpower_nat 2 53.
Proof.
unfold bdouble; apply make_bound_p.
lia.
Qed.

End b_Bounds.
Section Equiv.

Variable beta: radix.
Variable b : Fbound.
Variable p : Z.

Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat beta (Z.abs_nat p).
Hypothesis precisionNotZero : (1 < p)%Z.

Lemma pff_format_is_format: forall f, Fbounded b f ->
  (generic_format beta (FLT_exp (-dExp b) p) (FtoR beta f)).
Proof using pGivesBound precisionNotZero.
intros f Hf.
apply generic_format_FLT; auto with zarith.
exists (Float beta (Pff.Fnum f) (Pff.Fexp f)).
unfold F2R, FtoR; simpl.
rewrite bpow_powerRZ.
reflexivity.
destruct Hf.
apply Z.lt_le_trans with (1:=H).
rewrite pGivesBound.
rewrite Zpower_Zpower_nat; auto with zarith.
now destruct Hf.
Qed.

Lemma format_is_pff_format': forall r,
   (generic_format beta (FLT_exp (-dExp b) p) r) ->
    Fbounded b (Pff.Float (Ztrunc (scaled_mantissa beta (FLT_exp (-dExp b) p) r))
                            (cexp beta (FLT_exp (-dExp b) p) r)).
Proof using pGivesBound precisionNotZero.
intros x; unfold generic_format.
set (ex := cexp beta (FLT_exp (-dExp b) p) x).
set (mx := Ztrunc (scaled_mantissa beta (FLT_exp (-dExp b) p) x)).
intros Hx; repeat split ; simpl.
apply lt_IZR.
rewrite pGivesBound, IZR_Zpower_nat.
apply Rmult_lt_reg_r with (bpow beta ex).
apply bpow_gt_0.
rewrite <- bpow_plus.
rewrite inj_abs; try lia.
change (F2R (Float beta (Z.abs mx) ex) < bpow beta (p + ex))%R.
rewrite F2R_Zabs.
rewrite <- Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
unfold cexp in ex.
destruct (mag beta x) as (ex', He).
simpl in ex.
specialize (He Hx0).
apply Rlt_le_trans with (1 := proj2 He).
apply bpow_le.
cut (ex' - p <= ex)%Z.
lia.
unfold ex, FLT_exp.
apply Z.le_max_l.
apply Z.le_max_r.
Qed.

Lemma format_is_pff_format: forall r,
  (generic_format beta (FLT_exp (-dExp b) p) r)
  -> exists f, FtoR beta f = r /\ Fbounded b f.
Proof using pGivesBound precisionNotZero.
intros r Hr.
eexists; split.
2: apply (format_is_pff_format' _ Hr).
rewrite Hr at 3; unfold FtoR, F2R; simpl.
now rewrite bpow_powerRZ.
Qed.

Lemma format_is_pff_format_can: forall r,
  (generic_format beta (FLT_exp (-dExp b) p) r)
  -> exists f, FtoR beta f = r /\ Fcanonic beta b f.
Proof using pGivesBound precisionNotZero.
intros r Hr.
destruct (format_is_pff_format r Hr) as (f,(Hf1,Hf2)).
exists (Fnormalize beta b (Z.abs_nat p) f); split.
rewrite <- Hf1; apply FnormalizeCorrect.
apply radix_gt_1.
apply FnormalizeCanonic; try assumption.
apply radix_gt_1.
lia.
Qed.

Lemma equiv_RNDs_aux: forall z, Z.even z = true -> Even z.
Proof using .
intros z; unfold Z.even, Even.
case z.
intros; exists 0%Z; auto with zarith.
intros p0; case p0.
intros p1 H; contradict H; auto.
intros p1 _.
exists (Zpos p1); auto with zarith.
intros H; contradict H; auto.
intros p0; case p0.
intros p1 H; contradict H; auto.
intros p1 _.
exists (Zneg p1); auto with zarith.
intros H; contradict H; auto.
Qed.

Lemma pff_canonic_is_canonic: forall f, Fcanonic beta b f -> FtoR beta f <> 0 ->
  canonical beta (FLT_exp (- dExp b) p)
    (Float beta (Pff.Fnum f) (Pff.Fexp f)).
Proof using pGivesBound precisionNotZero.
intros f Hf1 Hf2; unfold canonical; simpl.
assert (K:(F2R (Float beta (Pff.Fnum f) (Pff.Fexp f)) = FtoR beta f)).
  unfold FtoR, F2R; simpl.
  now rewrite bpow_powerRZ.
unfold cexp, FLT_exp.
rewrite K.
destruct (mag beta (FtoR beta f)) as (e, He).
simpl; destruct Hf1.

destruct H as (H1,H2).
cut (Pff.Fexp f = e-p)%Z.
intros V; rewrite V.
apply sym_eq; apply Zmax_left.
rewrite <- V; destruct H1; auto with zarith.
cut (e = Pff.Fexp f + p)%Z.
lia.
apply trans_eq with (mag beta (FtoR beta f)).
apply sym_eq; apply mag_unique.
apply He; assumption.
apply mag_unique.
rewrite <- K; unfold F2R; simpl.
rewrite Rabs_mult.
rewrite (Rabs_right (bpow beta (Pff.Fexp f))).
2: apply Rle_ge; apply bpow_ge_0.
split.
replace (Pff.Fexp f + p - 1)%Z with ((p-1)+Pff.Fexp f)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.

apply Rmult_le_reg_l with (IZR beta).
apply IZR_lt.
apply radix_gt_0.
rewrite <- bpow_plus_1.
replace (p-1+1)%Z with (Z_of_nat (Z.abs_nat p)).
rewrite <- IZR_Zpower_nat.
simpl; rewrite <- pGivesBound.
rewrite Rabs_Zabs.
rewrite <- mult_IZR.
apply IZR_le.
rewrite <- (Z.abs_eq (beta)).
rewrite <- Zabs.Zabs_Zmult.
assumption.
apply Zlt_le_weak; apply radix_gt_0.
rewrite inj_abs; try ring.
lia.

rewrite Zplus_comm, bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- (inj_abs p) by lia.
rewrite <- IZR_Zpower_nat.
simpl; rewrite <- pGivesBound.
rewrite Rabs_Zabs.
apply IZR_lt.
destruct H1; assumption.

destruct H as (H1,(H2,H3)).
rewrite H2.
apply sym_eq; apply Zmax_right.
cut ((e-1) < p-dExp b)%Z.
lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (Rabs (FtoR beta f)).
apply He; auto.
apply Rlt_le_trans with (FtoR beta (firstNormalPos beta b (Z.abs_nat p))).
rewrite <- Fabs_correct.
2: apply radix_gt_0.
apply FsubnormalLtFirstNormalPos with (3 := pGivesBound).
apply radix_gt_1.
lia.
apply FsubnormFabs; auto with zarith.
apply radix_gt_1.
split; [idtac|split]; assumption.
rewrite Fabs_correct; auto with real zarith.
apply Rabs_pos.
apply radix_gt_0.
unfold firstNormalPos, FtoR, nNormMin.
simpl.
replace (IZR (Zpower_nat beta (Peano.pred (Z.abs_nat p)))) with (bpow beta (p-1)).
rewrite <- (bpow_powerRZ _).
rewrite <- bpow_plus.
apply bpow_le.
lia.
replace (p-1)%Z with (Z_of_nat (Peano.pred (Z.abs_nat p))).
rewrite <- IZR_Zpower_nat.
reflexivity.
rewrite inj_pred; lia.
Qed.

Lemma pff_round_NE_is_round: forall (r:R),
   (FtoR beta (RND_EvenClosest b beta (Z.abs_nat p) r)
     =  round beta (FLT_exp (-dExp b) p) rndNE r).
Proof using pGivesBound precisionNotZero.
intros.
assert (Rnd_NE_pt beta (FLT_exp (-dExp b) p) r
         (round beta (FLT_exp (-dExp b) p) rndNE r)).
apply round_NE_pt; auto with zarith.
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
apply exists_NE_FLT.
now right.
unfold Rnd_NE_pt, Rnd_NG_pt, Rnd_N_pt, NE_prop in H.
destruct H as ((H1,H2),H3).
destruct (format_is_pff_format _ H1) as (f,(Hf1,Hf2)).
rewrite <- Hf1.
apply sym_eq.
eapply (EvenClosestUniqueP b beta (Z.abs_nat p)).
apply radix_gt_1.
lia.
exact pGivesBound.
split.

split; auto; intros g Hg.
rewrite Hf1.
apply H2.
apply pff_format_is_format; auto.

case (Req_dec (FtoR beta (Fnormalize beta b (Z.abs_nat p) f))  0%R); intros L.
left.
unfold FNeven, Feven, Even.
exists 0%Z.
rewrite Zmult_0_r.
apply eq_IZR.
apply Rmult_eq_reg_l with (powerRZ beta (Pff.Fexp (Fnormalize beta b (Z.abs_nat p) f)))%R.
rewrite Rmult_0_r.
rewrite <- L; unfold FtoR; simpl; ring.
apply powerRZ_NOR; auto with zarith real.
apply Rgt_not_eq.
apply IZR_lt; apply radix_gt_0.
destruct H3.

destruct H as (g,(Hg1,(Hg2,Hg3))).
left.
unfold FNeven, Feven.
apply equiv_RNDs_aux.
replace (Pff.Fnum (Fnormalize beta b (Z.abs_nat p) f)) with (Fnum g); try assumption.
replace g with (Float beta (Pff.Fnum (Fnormalize beta b (Z.abs_nat p) f)) (Pff.Fexp (Fnormalize beta b (Z.abs_nat p) f))).
easy.
apply canonical_unique with (FLT_exp (- dExp b) p).
2: assumption.
apply pff_canonic_is_canonic.
apply FnormalizeCanonic.
2-3: lia.
2: auto with real.
apply radix_gt_1.
exact L.
rewrite <- Hg1, <- Hf1.
rewrite <- FnormalizeCorrect with beta b (Z.abs_nat p) f; auto with zarith.
unfold F2R, FtoR; simpl.
rewrite bpow_powerRZ.
reflexivity.
apply radix_gt_1.

right; intros q (Hq1,Hq2).
rewrite Hf1.
apply H.
split.
apply pff_format_is_format; auto.
intros g Hg.
destruct (format_is_pff_format _ Hg) as (v,(Hv1,Hv2)).
rewrite <- Hv1.
apply Hq2; auto.
apply RND_EvenClosest_correct with (3 := pGivesBound).
apply radix_gt_1.
lia.
Qed.

Lemma round_NE_is_pff_round: forall (r:R),
   exists f:Pff.float, (Fcanonic beta b f /\ (EvenClosest b beta (Z.abs_nat p) r f) /\
    FtoR beta f =  round beta (FLT_exp (-dExp b) p) rndNE r).
Proof using pGivesBound precisionNotZero.
intros r.
exists (RND_EvenClosest b beta (Z.abs_nat p) r).
split.
apply RND_EvenClosest_canonic with (3 := pGivesBound).
apply radix_gt_1.
lia.
split.
apply RND_EvenClosest_correct with (3 := pGivesBound).
apply radix_gt_1.
lia.
apply pff_round_NE_is_round.
Qed.

Lemma pff_round_UP_is_round: forall (r:R),
  FtoR beta (RND_Max b beta (Z.abs_nat p) r)
             = round beta (FLT_exp (- dExp b) p) Zceil r.
Proof using pGivesBound precisionNotZero.
Proof with auto with typeclass_instances.
intros r.
generalize (radix_gt_1 beta); intros M.
assert (K:Valid_exp (FLT_exp (- dExp b) p)).
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
destruct (format_is_pff_format_can (round beta (FLT_exp (- dExp b) p) Zceil r)) as (fu,(Hfu1,Hfu2)).
apply generic_format_round...
rewrite <- Hfu1.
apply MaxUniqueP with b r.
apply RND_Max_correct; try assumption.
apply Nat2Z.inj_lt; rewrite inj_abs; simpl; lia.
split.
apply FcanonicBound with (1:=Hfu2).
assert (T:Rnd_UP_pt (generic_format beta (FLT_exp (- dExp b) p)) r
             (round beta (FLT_exp (- dExp b) p) Zceil r)).
apply round_UP_pt...
destruct T as (T1,(T2,T3)).
split.
rewrite Hfu1; apply T2.
intros g Hg1 Hg2.
rewrite Hfu1; apply T3; try assumption.
now apply pff_format_is_format.
Qed.

Lemma pff_round_DN_is_round: forall (r:R),
  FtoR beta (RND_Min b beta (Z.abs_nat p) r)
             = round beta (FLT_exp (- dExp b) p) Zfloor r.
Proof using pGivesBound precisionNotZero.
Proof with auto with typeclass_instances.
intros r.
generalize (radix_gt_1 beta); intros M.
assert (K:Valid_exp (FLT_exp (- dExp b) p)).
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
destruct (format_is_pff_format_can (round beta (FLT_exp (- dExp b) p) Zfloor r)) as (fd,(Hfd1,Hfd2)).
apply generic_format_round...
rewrite <- Hfd1.
apply MinUniqueP with b r.
apply RND_Min_correct; try assumption.
apply Nat2Z.inj_lt; rewrite inj_abs; simpl; lia.
split.
apply FcanonicBound with (1:=Hfd2).
assert (T:Rnd_DN_pt (generic_format beta (FLT_exp (- dExp b) p)) r
             (round beta (FLT_exp (- dExp b) p) Zfloor r)).
apply round_DN_pt...
destruct T as (T1,(T2,T3)).
split.
rewrite Hfd1; apply T2.
intros g Hg1 Hg2.
rewrite Hfd1; apply T3; try assumption.
now apply pff_format_is_format.
Qed.

Lemma pff_round_N_is_round: forall choice, forall (r:R),
   (FtoR beta (RND_Closest b beta (Z.abs_nat p) choice r)
     =  round beta (FLT_exp (-dExp b) p) (Znearest choice) r).
Proof using pGivesBound precisionNotZero.
Proof with auto with typeclass_instances.
generalize (radix_gt_1 beta); intros M.
intros choice r; apply sym_eq.
assert (K:Valid_exp (FLT_exp (- dExp b) p)).
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
unfold RND_Closest, FtoRradix.
rewrite pff_round_DN_is_round.
rewrite pff_round_UP_is_round.
case (Rle_dec _ _); intros H1.
case (Rle_lt_or_eq_dec _ _ H1); intros H2.

rewrite pff_round_UP_is_round.
apply round_N_eq_UP...
rewrite Rabs_right in H2;[idtac| apply Rle_ge, Rle_0_minus, round_UP_pt; easy].
rewrite Rabs_left1 in H2;[idtac| apply Rle_minus, round_DN_pt; easy].
apply Rmult_lt_reg_r with 2%R; try apply Rlt_0_2.
unfold Rdiv; rewrite Rmult_assoc, Rinv_l.
2: apply Rgt_not_eq, Rlt_0_2.
apply Rplus_lt_reg_l with (-round beta (FLT_exp (- dExp b) p) Zfloor r - r)%R.
apply Rle_lt_trans with (round beta (FLT_exp (- dExp b) p) Zceil r - r)%R;[right;ring|idtac].
apply Rlt_le_trans with (1:=H2).
right; ring.

rewrite round_N_middle.
rewrite inj_abs by lia.
case (choice _).
apply sym_eq, pff_round_UP_is_round.
apply sym_eq, pff_round_DN_is_round.
rewrite Rabs_right in H2;[idtac| apply Rle_ge, Rle_0_minus, round_UP_pt; easy].
rewrite Rabs_left1 in H2;[idtac| apply Rle_minus, round_DN_pt; easy].
rewrite H2; ring.

rewrite pff_round_DN_is_round.
apply round_N_eq_DN...
apply Rnot_le_lt in H1.
rewrite Rabs_left1 in H1;[idtac| apply Rle_minus, round_DN_pt; easy].
rewrite Rabs_right in H1;[idtac| apply Rle_ge, Rle_0_minus, round_UP_pt; easy].
apply Rmult_lt_reg_r with 2%R; try apply Rlt_0_2.
unfold Rdiv; rewrite Rmult_assoc, Rinv_l.
2: apply Rgt_not_eq, Rlt_0_2.
apply Rplus_lt_reg_l with (-round beta (FLT_exp (- dExp b) p) Zfloor r - r)%R.
apply Rle_lt_trans with (-(round beta (FLT_exp (- dExp b) p) Zfloor r - r))%R;[right;ring|idtac].
apply Rlt_le_trans with (1:=H1).
right; ring.
Qed.

Lemma round_N_is_pff_round: forall choice, forall (r:R),
   exists f:Pff.float, (Fcanonic beta b f /\ (Closest b beta r f) /\
    FtoR beta f =  round beta (FLT_exp (-dExp b) p) (Znearest choice) r).
Proof using pGivesBound precisionNotZero.
intros choice r.
assert (1 < Z.abs_nat p).
apply Nat2Z.inj_lt; simpl.
rewrite inj_abs; lia.
exists (RND_Closest b beta (Z.abs_nat p) choice r); split.
apply RND_Closest_canonic; easy.
split.
apply RND_Closest_correct; easy.
apply pff_round_N_is_round.
Qed.

Lemma pff_round_is_round_N: forall r f, Closest b beta r f ->
    exists (choice:Z->bool),
      FtoR beta f = round beta (FLT_exp (-dExp b) p) (Znearest choice) r.
Proof using pGivesBound precisionNotZero.
Proof with auto with typeclass_instances.
intros r f Hf.
generalize (radix_gt_1 beta); intros M.
assert (M':1 < Z.abs_nat p).
apply Nat2Z.inj_lt; simpl.
rewrite inj_abs; lia.
pose (d := round beta (FLT_exp (-dExp b) p) Zfloor r).
pose (u := round beta (FLT_exp (-dExp b) p) Zceil r).
case (Rle_or_lt ((d+u)/2) r); intros L.
destruct L as [L|L].

exists (fun _ => true).
rewrite <- pff_round_N_is_round.
apply trans_eq with (FtoR beta (RND_Max b beta (Z.abs_nat p) r)).
apply ClosestMaxEq with b r (RND_Min b beta (Z.abs_nat p) r); try assumption.
apply RND_Min_correct; assumption.
apply RND_Max_correct; assumption.
rewrite pff_round_DN_is_round; fold d.
rewrite pff_round_UP_is_round; fold u.
apply Rmult_lt_reg_r with (/2)%R.
apply pos_half_prf.
apply Rlt_le_trans with (1:=L).
right; simpl; field.
rewrite pff_round_N_is_round.
rewrite pff_round_UP_is_round; fold u.
apply sym_eq, round_N_eq_UP...
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.

case (ClosestMinOrMax b beta r f); try assumption; intros LL.
exists (fun _ => false).
rewrite round_N_middle.
rewrite <- pff_round_DN_is_round.
apply (MinUniqueP b beta r); try assumption.
apply RND_Min_correct; assumption.
fold d; fold u; rewrite <- L; field.
exists (fun _ => true).
rewrite round_N_middle.
rewrite <- pff_round_UP_is_round.
apply (MaxUniqueP b beta r); try assumption.
apply RND_Max_correct; assumption.
fold d; fold u; rewrite <- L; field.

exists (fun _ => true).
rewrite <- pff_round_N_is_round.
apply trans_eq with (FtoR beta (RND_Min b beta (Z.abs_nat p) r)).
apply ClosestMinEq with b r (RND_Max b beta (Z.abs_nat p) r); try assumption.
apply RND_Min_correct; assumption.
apply RND_Max_correct; assumption.
rewrite pff_round_DN_is_round; fold d.
rewrite pff_round_UP_is_round; fold u.
apply Rmult_lt_reg_r with (/2)%R.
apply pos_half_prf.
apply Rle_lt_trans with (2:=L).
right; simpl; field.
rewrite pff_round_N_is_round.
rewrite pff_round_DN_is_round; fold d.
apply sym_eq, round_N_eq_DN...
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
Qed.

Lemma FloatFexp_gt:  forall e f, Fbounded b f ->
  (bpow beta (e+p) <= Rabs (FtoR beta f))%R ->
       (e < Pff.Fexp f)%Z.
Proof using pGivesBound precisionNotZero.
intros e f Ff H1.
apply lt_bpow with beta.
apply Rmult_lt_reg_r with (bpow beta p).
apply bpow_gt_0.
rewrite <- bpow_plus.
apply Rle_lt_trans with (1:=H1).
rewrite <- Fabs_correct.
2: apply radix_gt_0.
unfold Fabs, FtoR; simpl; rewrite Rmult_comm.
rewrite bpow_powerRZ.
apply Rmult_lt_compat_l.
apply powerRZ_lt.
apply IZR_lt, radix_gt_0.
destruct Ff as (T1,T2).
rewrite bpow_powerRZ.
replace p with (Z.of_nat (Z.abs_nat p)).
rewrite <- Zpower_nat_Z_powerRZ.
apply IZR_lt.
now rewrite <- pGivesBound.
rewrite inj_abs; lia.
Qed.

Lemma CanonicGeNormal:  forall f, Fcanonic beta b f ->
  (bpow beta (-dExp b+p-1) <= Rabs (FtoR beta f))%R ->
       (Fnormal beta b f)%Z.
Proof using pGivesBound precisionNotZero.
intros f Cf H1.
case Cf; trivial.
intros (H2,(H3,H4)).
contradict H1; apply Rlt_not_le.
rewrite <- Fabs_correct.
2: apply radix_gt_0.
unfold FtoR, Fabs; simpl.
rewrite H3, <- bpow_powerRZ.
apply Rlt_le_trans with (bpow beta (p-1)*bpow beta (-dExp b))%R.
2: rewrite <- bpow_plus.
2: right; f_equal; ring.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Rmult_lt_reg_l with (IZR beta).
apply IZR_lt, radix_gt_0.
rewrite <- mult_IZR.
apply Rlt_le_trans with (IZR (Z.pos (vNum b))).
apply IZR_lt.
rewrite <- (Z.abs_eq beta).
now rewrite <- Zabs_Zmult.
apply Zlt_le_weak, radix_gt_0.
rewrite pGivesBound.
rewrite IZR_Zpower_nat.
rewrite <- bpow_1.
rewrite <- bpow_plus.
apply bpow_le.
rewrite inj_abs; lia.
Qed.

Lemma Fulp_ulp_aux:  forall f, Fcanonic beta b f ->
   Fulp b beta (Z.abs_nat p) f
    = ulp beta (FLT_exp (-dExp b) p) (FtoR beta f).
Proof using pGivesBound precisionNotZero.
intros f H.
case (Req_dec (FtoR beta f) 0); intros Zf.

rewrite Zf, ulp_FLT_small.
2: unfold Prec_gt_0; lia.
2: rewrite Rabs_R0; apply bpow_gt_0.
rewrite Fulp_zero.
apply sym_eq, bpow_powerRZ.
apply is_Fzero_rep2 with beta; try assumption.
apply radix_gt_1.

rewrite ulp_neq_0; try assumption.
replace (FtoR beta f) with (F2R (Float beta (Pff.Fnum f) (Pff.Fexp f))).
rewrite <- pff_canonic_is_canonic; try assumption.
simpl; rewrite CanonicFulp; try assumption.
unfold FtoR; simpl; rewrite bpow_powerRZ; ring.
apply radix_gt_1.
replace 1 with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
unfold F2R, FtoR; simpl.
rewrite bpow_powerRZ; easy.
Qed.

Lemma Fulp_ulp:  forall f, Fbounded b f ->
   Fulp b beta (Z.abs_nat p) f
    = ulp beta (FLT_exp (-dExp b) p) (FtoR beta f).
Proof using pGivesBound precisionNotZero.
intros f H.
assert (Y1: (1 < beta)%Z) by apply radix_gt_1.
assert (Y2:Z.abs_nat p <> 0).
apply sym_not_eq, Nat.lt_neq.
replace 0 with (Z.abs_nat 0) by easy.
apply Zabs_nat_lt; lia.
rewrite FulpComp with (q:=Fnormalize beta b (Z.abs_nat p) f); try assumption.
rewrite <- FnormalizeCorrect with beta b (Z.abs_nat p) f; try assumption.
apply Fulp_ulp_aux.
apply FnormalizeCanonic; try assumption.
replace 1 with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
apply FnormalizeBounded; try assumption.
apply sym_eq, FnormalizeCorrect; try assumption.
Qed.

End Equiv.

Section Equiv_instanc.

Lemma round_NE_is_pff_round_b32: forall (r:R),
   exists f:Pff.float, (Fcanonic 2 bsingle f /\ (EvenClosest bsingle 2 24 r f) /\
    FtoR 2 f =  round radix2 (FLT_exp (-149) 24) rndNE r).
Proof.
apply (round_NE_is_pff_round radix2 bsingle 24).
apply psGivesBound.
apply eq_refl.
Qed.

Lemma round_NE_is_pff_round_b64: forall (r:R),
   exists f:Pff.float, (Fcanonic 2 bdouble f /\ (EvenClosest bdouble 2 53 r f) /\
    FtoR 2 f =  round radix2 (FLT_exp (-1074) 53) rndNE r).
Proof.
apply (round_NE_is_pff_round radix2 bdouble 53).
apply pdGivesBound.
apply eq_refl.
Qed.

End Equiv_instanc.

End Pff2FlocqAux.

End Pff.

End Flocq.


Import Stdlib.micromega.Psatz.
Import Flocq.Core.Core Flocq_DOT_Prop_DOT_Plus_error.Flocq.AVOID_RESERVED_Prop.Plus_error Flocq_DOT_Prop_DOT_Mult_error.Flocq.AVOID_RESERVED_Prop.Mult_error Flocq.Calc.Operations Flocq_DOT_Prop_DOT_Sterbenz.Flocq.AVOID_RESERVED_Prop.Sterbenz.
Import Flocq.Pff.Pff Flocq.Pff.Pff2FlocqAux.

Open Scope R_scope.

Section FTS.
Variable emin prec : Z.
Variable choice : Z -> bool.
Hypothesis precisionNotZero : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) (Znearest choice)).
Notation bpow e := (bpow radix2 e).

Lemma round_N_opp_sym: forall x, round_flt (- x) =
       - round_flt x.
Proof using choice_sym.
intros x; unfold round; rewrite <- F2R_Zopp.
rewrite cexp_opp; f_equal; f_equal.
rewrite scaled_mantissa_opp.
rewrite Znearest_opp.
generalize (scaled_mantissa radix2 (FLT_exp emin prec) x).
intros z; unfold Znearest; case (Rcompare _); try easy.
now rewrite <- choice_sym.
Qed.

Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a := round_flt (x+y).
Let b := round_flt (y+round_flt (x-a)).

Theorem Fast2Sum_correct: Rabs y <= Rabs x -> a+b=x+y.
Proof using Fx Fy choice_sym emin_neg precisionNotZero.
Proof with auto with typeclass_instances.
intros H.

destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.

pose (Iplus := fun (f g:Pff.float) => RND_Closest
        (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) choice
         (FtoR radix2 f + FtoR radix2 g)).
pose (Iminus := fun (f g:Pff.float) => RND_Closest
        (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) choice
         (FtoR radix2 f - FtoR radix2 g)).
assert (H1: forall x y, FtoR 2 (Iplus x y) = round_flt (FtoR 2 x + FtoR 2 y)).
clear -prec_gt_0_ precisionNotZero emin_neg; intros x y.
unfold Iplus.
apply trans_eq with (round radix2
  (FLT_exp (- dExp (make_bound radix2 prec emin)) prec)
  (Znearest choice) (FtoR radix2 x + FtoR radix2 y)).
apply pff_round_N_is_round; try assumption.
now apply make_bound_p.
rewrite make_bound_Emin; try assumption.
now rewrite Z.opp_involutive.
assert (H2: forall x y, FtoR 2 (Iminus x y) = round_flt (FtoR 2 x - FtoR 2 y)).
clear -prec_gt_0_ precisionNotZero emin_neg; intros x y.
unfold Iminus.
apply trans_eq with (round radix2
  (FLT_exp (- dExp (make_bound radix2 prec emin)) prec)
  (Znearest choice) (FtoR radix2 x - FtoR radix2 y)).
apply pff_round_N_is_round; try assumption.
now apply make_bound_p.
rewrite make_bound_Emin; try assumption.
now rewrite Z.opp_involutive.

assert (K: FtoR 2 (Iminus fy (Iminus (Iplus fx fy) fx)) =
       FtoR 2 fx + FtoR 2 fy - FtoR 2 (Iplus fx fy)).
apply Pff.Dekker_FTS with (make_bound radix2 prec emin) (Z.abs_nat prec); try assumption.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.

intros p q Fp Fq.
apply RND_Closest_correct.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.

intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq.
apply lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply FcanonicFopp.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite Fopp_correct, 2!H1, 2!Fopp_correct, <- Ropp_plus_distr.
now rewrite round_N_opp_sym.

intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite H1,H2.
rewrite Fopp_correct.
f_equal; ring.

unfold Pff.FtoRradix.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy; assumption.

generalize K; rewrite 2!H2, H1.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy; fold a; unfold b; intros K'.
apply Rplus_eq_reg_r with (-a).
apply trans_eq with (round_flt (y - round_flt (a - x))).
2: rewrite K'; ring.
ring_simplify; f_equal; unfold Rminus; f_equal.
rewrite <- round_N_opp_sym.
f_equal; ring.
Qed.

End FTS.

Section TS.

Variable emin prec : Z.
Variable choice : Z -> bool.
Hypothesis precisionNotZero : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) (Znearest choice)).
Notation bpow e := (bpow radix2 e).

Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a  := round_flt (x+y).
Let x' := round_flt (a-x).
Let dx := round_flt (x- round_flt (a-x')).
Let dy := round_flt (y - x').
Let b  := round_flt (dx + dy).

Theorem TwoSum_correct: a+b=x+y.
Proof using Fx Fy choice_sym dx dy emin_neg precisionNotZero.
Proof with auto with typeclass_instances.

destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.

pose (Iplus := fun (f g:Pff.float) => RND_Closest
        (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) choice
         (FtoR radix2 f + FtoR radix2 g)).
pose (Iminus := fun (f g:Pff.float) => RND_Closest
        (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) choice
         (FtoR radix2 f - FtoR radix2 g)).
assert (H1: forall x y, FtoR 2 (Iplus x y) = round_flt (FtoR 2 x + FtoR 2 y)).
clear -prec_gt_0_ precisionNotZero emin_neg; intros x y.
unfold Iplus.
apply trans_eq with (round radix2
  (FLT_exp (- dExp (make_bound radix2 prec emin)) prec)
  (Znearest choice) (FtoR radix2 x + FtoR radix2 y)).
apply pff_round_N_is_round; try assumption.
now apply make_bound_p.
rewrite make_bound_Emin; try assumption.
now rewrite Z.opp_involutive.
assert (H2: forall x y, FtoR 2 (Iminus x y) = round_flt (FtoR 2 x - FtoR 2 y)).
clear -prec_gt_0_ precisionNotZero emin_neg; intros x y.
unfold Iminus.
apply trans_eq with (round radix2
  (FLT_exp (- dExp (make_bound radix2 prec emin)) prec)
  (Znearest choice) (FtoR radix2 x - FtoR radix2 y)).
apply pff_round_N_is_round; try assumption.
now apply make_bound_p.
rewrite make_bound_Emin; try assumption.
now rewrite Z.opp_involutive.

assert (K: FtoR 2 (Iplus (Iminus fx (Iminus (Iplus fx fy) (Iminus (Iplus fx fy) fx)))
            (Iminus fy (Iminus (Iplus fx fy) fx))) =
       FtoR 2 fx + FtoR 2 fy - FtoR 2 (Iplus fx fy)).
apply Knuth with (make_bound radix2 prec emin) (Z.abs_nat prec); try assumption.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.

intros p q Fp Fq.
apply RND_Closest_correct.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.

unfold FtoRradix.
intros p q r s Fp Fq Fr Fs M1 M2.
now rewrite 2!H1, M1, M2.

intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
now rewrite 2!H1, Rplus_comm.

intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply FcanonicFopp.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite Fopp_correct, 2!H1, 2!Fopp_correct, <- Ropp_plus_distr.
now rewrite round_N_opp_sym.

intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite H1, H2, Fopp_correct.
f_equal; ring.

generalize K; rewrite 2!H1, 5!H2, H1.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy.
fold a; fold x'; fold dx; fold dy; fold b.
intros K'; rewrite K'; ring.
Qed.

End TS.

Section Veltkamp.

Variable beta : radix.
Variable emin prec : Z.
Variable choice : Z -> bool.
Variable s:Z.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation round_flt_s :=(round beta (FLT_exp emin (prec-s)) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).
Notation bpow e := (bpow beta e).

Hypothesis SLe: (2 <= s)%Z.
Hypothesis SGe: (s <= prec-2)%Z.
Variable x:R.
Hypothesis Fx: format x.

Let p := round_flt (x*(bpow s+1)).
Let q:= round_flt (x-p).
Let hx:=round_flt (q+p).
Let tx:=round_flt (x-hx).

Lemma C_format: format (bpow s +1).
Proof using SGe SLe emin_neg precisionGe3.
Proof with auto with typeclass_instances.
apply generic_format_FLT.
exists (Defs.Float beta (Zpower beta s+1)%Z 0%Z); simpl.
unfold F2R; simpl.
rewrite plus_IZR, IZR_Zpower; try lia.
simpl; ring.
rewrite Z.abs_eq.
apply Z.le_lt_trans with (beta^s+beta^0)%Z.
simpl; lia.
apply Z.le_lt_trans with (beta^s+beta^s)%Z.
apply Zplus_le_compat_l.
apply Zpower_le; lia.
apply Z.le_lt_trans with (2*beta^s)%Z.
lia.
apply Z.le_lt_trans with (beta^1*beta^s)%Z.
apply Zmult_le_compat_r.
rewrite Z.pow_1_r.
apply Zle_bool_imp_le; apply beta.
apply Zpower_ge_0.
rewrite <- Zpower_plus; try lia.
apply Zpower_lt; lia.
apply Z.le_trans with (beta^s)%Z; try lia.
apply Zpower_ge_0.
assumption.
Qed.

Theorem Veltkamp_Even:
  (choice = fun z => negb (Z.even z)) ->
   hx = round_flt_s x.
Proof using Fx SGe SLe emin_neg precisionGe3.
Proof with auto with typeclass_instances.
intros Hchoice.
assert (precisionNotZero : (1 < prec)%Z) by lia.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  (x*(bpow s+1)))
  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  (x-p))
  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  (q+p))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by lia.

destruct VeltkampEven with beta (make_bound beta prec emin) (Z.abs_nat s)
   (Z.abs_nat prec) fx fp fq fhx as (hx', (H1,H2)); try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 2%nat with (Z.abs_nat 2) by easy.
apply Zabs_nat_le; lia.
apply Nat2Z.inj_le.
rewrite inj_abs; lia.
rewrite Hfx; rewrite inj_abs; try lia.
rewrite bpow_powerRZ in Hfp'; exact Hfp'.
rewrite Hfx, Hfp'', <- Hchoice; assumption.
rewrite Hfp'', Hfq'', <- Hchoice; assumption.

unfold hx; rewrite Hchoice, <- Hfhx'', <- H1.
apply trans_eq with (FtoR beta (RND_EvenClosest
 (make_bound beta (prec-s) emin) beta (Z.abs_nat (prec-s)) x)).
generalize (EvenClosestUniqueP (make_bound beta (prec-s) emin) beta
   (Z.abs_nat (prec-s))); unfold UniqueP; intros T.
apply T with x; clear T.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite <- Hfx.
replace (Z.abs_nat (prec-s)) with (Z.abs_nat prec - Z.abs_nat s)%nat.
replace (make_bound beta (prec - s) emin) with
  (Bound  (Pos.of_succ_nat
                 (Peano.pred
                    (Z.abs_nat
                       (Zpower_nat beta (Z.abs_nat prec - Z.abs_nat s)))))
           (dExp (make_bound beta prec emin))).
exact H2.
generalize (make_bound_Emin beta (prec-s) _ emin_neg).
generalize (make_bound_p beta (prec-s) emin).
destruct (make_bound beta (prec-s) emin) as (l1,l2).
simpl; intros H3 H4; f_equal.
apply Pos2Z.inj.
rewrite H3; try lia.
replace (Z.abs_nat (prec - s)) with (Z.abs_nat prec - Z.abs_nat s)%nat.
rewrite <- (p'GivesBound beta (make_bound beta prec emin) (Z.abs_nat s) (Z.abs_nat prec)) at 2.
simpl; easy.
apply radix_gt_1.
apply Nat2Z.inj.
rewrite inj_minus; repeat rewrite inj_abs; lia.
apply N2Z.inj.
rewrite H4.
rewrite Zabs2N.id_abs.
now apply Z.abs_neq.
apply Nat2Z.inj.
rewrite inj_abs; lia.
apply RND_EvenClosest_correct.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite pff_round_NE_is_round; try lia.
f_equal; f_equal.
rewrite make_bound_Emin; lia.
apply make_bound_p; lia.
Qed.

Theorem Veltkamp: exists choice': Z->bool ,
   hx = round beta (FLT_exp emin (prec-s)) (Znearest choice') x.
Proof using Fx SGe SLe emin_neg precisionGe3 q.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x*(bpow s+1)))
  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-p))
  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (q+p))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by lia.

destruct Veltkamp with beta (make_bound beta prec emin) (Z.abs_nat s)
   (Z.abs_nat prec) fx fp fq fhx as (H1,(hx', (H2,(H3,H4)))); try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 2%nat with (Z.abs_nat 2) by easy.
apply Zabs_nat_le; lia.
apply Nat2Z.inj_le.
rewrite inj_abs; lia.
rewrite Hfx; rewrite inj_abs; try lia.
rewrite bpow_powerRZ in Hfp'; exact Hfp'.
rewrite Hfx, Hfp''; assumption.
rewrite Hfp'', Hfq''; assumption.

destruct pff_round_is_round_N with beta (make_bound beta (prec-s) emin)
 (Z.abs_nat (prec-s)) (FtoR beta fx) hx' as (choice',M).
rewrite Zabs2Nat.id.
apply make_bound_p; lia.
rewrite inj_abs; simpl; lia.
unfold make_bound.
replace (Z.to_pos (beta ^ (prec - s))) with (Pos.of_succ_nat
                 (Init.Nat.pred
                    (Z.abs_nat
                       (Zpower_nat beta
                          (Z.abs_nat prec - Z.abs_nat s))))).
replace (Z.abs_N emin) with (dExp (make_bound beta prec emin)) by easy.
exact H3.
apply Zpos_eq_iff.
apply trans_eq with (Zpower_nat beta (Z.abs_nat prec - Z.abs_nat s)).
rewrite <- p''GivesBound with (b:=make_bound beta prec emin) at 2.
simpl; auto.
apply radix_gt_1.
rewrite Zpower_Zpower_nat,Z2Pos.id.
f_equal; apply sym_eq, Zabs2Nat.inj_sub; lia.
apply Zpower_nat_less.
apply radix_gt_1.
lia.
exists choice'.
unfold hx; rewrite <- Hfhx'', <- H2, M.
f_equal; try easy.
f_equal.
rewrite make_bound_Emin; lia.
rewrite inj_abs; simpl; lia.
Qed.

Theorem Veltkamp_tail:
 x = hx+tx /\  generic_format beta (FLT_exp emin s) tx.
Proof using Fx SGe SLe emin_neg precisionGe3 q.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x*(bpow s+1)))
  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-p))
  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (q+p))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-hx))
  as (ftx,(Hftx, (Hftx',Hftx''))).
rewrite make_bound_Emin in Hftx''; try assumption.
replace (--emin)%Z with emin in Hftx'' by lia.

destruct Veltkamp_tail with beta (make_bound beta prec emin) (Z.abs_nat s)
   (Z.abs_nat prec) fx fp fq fhx ftx as (tx', (H1,(H2,(H3,H4)))); try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 2%nat with (Z.abs_nat 2) by easy.
apply Zabs_nat_le; lia.
apply Nat2Z.inj_le.
rewrite inj_abs; lia.
rewrite Hfx; rewrite inj_abs; try lia.
rewrite bpow_powerRZ in Hfp'; apply Hfp'.
rewrite Hfx, Hfp''; apply Hfq'.
rewrite Hfp'', Hfq''; apply Hfhx'.
rewrite Hfhx'', Hfx; apply Hftx'.

split.
rewrite <- Hfx, <-H2, Hfhx'', H1, Hftx''; easy.
unfold tx; rewrite <- Hftx'', <- H1.
replace emin with (-dExp (Bound
       (Pos.of_succ_nat
                 (Peano.pred (Z.abs_nat (Zpower_nat beta (Z.abs_nat s)))))
       (dExp (make_bound beta prec emin))))%Z.
apply pff_format_is_format; try assumption; try lia.
simpl.
rewrite Zpos_P_of_succ_nat, inj_pred.
rewrite <- Zsucc_pred.
apply inj_abs.
apply Zpower_NR0.
apply Zlt_le_weak; apply radix_gt_0.
apply sym_not_eq, Nat.lt_neq, lt_Zlt_inv.
rewrite inj_abs.
apply Zpower_nat_less.
apply radix_gt_1.
apply Zpower_NR0.
apply Zlt_le_weak; apply radix_gt_0.
simpl.
rewrite Zabs2N.id_abs.
rewrite Z.abs_neq; lia.
Qed.

End Veltkamp.

Section Underf_mult_aux.

Variable beta : radix.
Variable b: Fbound.
Variable prec: Z.

Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat beta (Z.abs_nat prec).
Hypothesis precisionGt1 : (1 < prec)%Z.

Lemma underf_mult_aux:
 forall e x y,
  Fbounded b x ->
  Fbounded b y ->
   (bpow beta (e + 2 * prec - 1)%Z <= Rabs (FtoR beta x * FtoR beta y)) ->
     (e <= Pff.Fexp x + Pff.Fexp y)%Z.
Proof using pGivesBound precisionGt1.
intros e x y Fx Fy H.
assert (HH: forall z, Fbounded b z
   -> Rabs (FtoR beta z) < bpow beta (Pff.Fexp z + prec)).
clear -precisionGt1 pGivesBound; intros z Hz.
unfold FtoR; rewrite <- bpow_powerRZ.
rewrite Rabs_mult, Rmult_comm.
rewrite Rabs_right.
2: apply Rle_ge, bpow_ge_0.
rewrite bpow_plus; apply Rmult_lt_compat_l.
apply bpow_gt_0.
destruct Hz as (T1,T2).
rewrite pGivesBound in T1.
rewrite <- abs_IZR, <- IZR_Zpower;[idtac|lia].
apply IZR_lt.
apply Z.lt_le_trans with (1:=T1).
rewrite Zpower_Zpower_nat; lia.
assert (e+2*prec-1 < (Pff.Fexp x+prec) +(Pff.Fexp y +prec))%Z; try lia.

apply lt_bpow with beta.
apply Rle_lt_trans with (1:=H).
rewrite Rabs_mult, bpow_plus.
apply Rmult_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
now apply HH.
now apply HH.
Qed.

Lemma underf_mult_aux':
 forall x y,
  Fbounded b x ->
  Fbounded b y ->
   (bpow beta (-dExp b + 2 * prec - 1)%Z <= Rabs (FtoR beta x * FtoR beta y)) ->
     (-dExp b <= Pff.Fexp x + Pff.Fexp y)%Z.
Proof using pGivesBound precisionGt1.
intros.
now apply underf_mult_aux.
Qed.

End Underf_mult_aux.

Section Dekker.

Variable beta : radix.
Variable emin prec: Z.
Variable choice : Z -> bool.
Let s:= (prec- Z.div2 prec)%Z.

Hypothesis precisionGe4 : (4 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin < 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation round_flt_s :=(round beta (FLT_exp emin (prec-s)) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).
Notation bpow e := (bpow beta e).

Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let px := round_flt (x*(bpow s+1)).
Let qx:= round_flt (x-px).
Let hx:=round_flt (qx+px).
Let tx:=round_flt (x-hx).

Let py := round_flt (y*(bpow s+1)).
Let qy:= round_flt (y-py).
Let hy:=round_flt (qy+py).
Let ty:=round_flt (y-hy).

Let x1y1:=round_flt (hx*hy).
Let x1y2:=round_flt (hx*ty).
Let x2y1:=round_flt (tx*hy).
Let x2y2:=round_flt (tx*ty).

Let r :=round_flt(x*y).
Let t1 :=round_flt (-r+x1y1).
Let t2 :=round_flt (t1+x1y2).
Let t3 :=round_flt (t2+x2y1).
Let t4 :=round_flt (t3+x2y2).

Theorem Dekker: (radix_val beta=2)%Z \/ (Z.Even prec) ->
  (x*y=0 \/ bpow (emin + 2 * prec - 1) <= Rabs (x * y) ->  (x*y=r+t4)%R) /\
    (Rabs (x*y-(r+t4)) <= (7/2)*bpow emin)%R.
Proof using Fx Fy emin_neg precisionGe4 t3 x2y2.
Proof with auto with typeclass_instances.
intros HH.

case (Req_dec x 0); intros Kx.
assert (Kr: r=0).
unfold r; rewrite Kx, Rmult_0_l, round_0...
assert (Khx: hx=0).
unfold hx, qx, px; rewrite Kx, Rmult_0_l, round_0...
rewrite Rplus_0_r, Rminus_0_l, Ropp_0, round_0...
apply round_0...
assert (Kt4: t4=0).
unfold t4, t3, t2, t1, x1y1, x1y2, x2y1, x2y2, tx; rewrite Kr, Kx, Khx.
rewrite 2!Rmult_0_l, round_0...
rewrite Rminus_0_r, Rplus_0_r, round_0...
rewrite 2!Rmult_0_l, round_0...
rewrite 3!Rplus_0_r, Ropp_0; repeat rewrite round_0...
rewrite Kx, Kr, Kt4.
split;[intros; ring|idtac].
rewrite Rmult_0_l, Rplus_0_l, Rminus_0_l, Ropp_0, Rabs_R0.
apply Rmult_le_pos; try apply bpow_ge_0.
apply Rmult_le_pos.
apply Fourier_util.Rle_zero_pos_plus1; apply Rmult_le_pos.
left; apply Rlt_0_2.
apply Fourier_util.Rle_zero_pos_plus1; left; apply Rlt_0_2.
left; apply pos_half_prf.

case (Req_dec y 0); intros Ky.
assert (Kr: r=0).
unfold r; rewrite Ky, Rmult_0_r, round_0...
assert (Khy: hy=0).
unfold hy, qy, py; rewrite Ky, Rmult_0_l, round_0...
rewrite Rplus_0_r, Rminus_0_l, Ropp_0, round_0...
apply round_0...
assert (Kt4: t4=0).
unfold t4, t3, t2, t1, x1y1, x1y2, x2y1, x2y2, ty; rewrite Kr, Ky, Khy.
rewrite 2!Rmult_0_r, round_0...
rewrite Rminus_0_r, Rplus_0_r, round_0...
rewrite 2!Rmult_0_r, round_0...
rewrite 3!Rplus_0_r, Ropp_0; repeat rewrite round_0...
rewrite Ky, Kr, Kt4.
split;[intros; ring|idtac].
rewrite Rmult_0_r, Rplus_0_l, Rminus_0_l, Ropp_0, Rabs_R0.
apply Rmult_le_pos; try apply bpow_ge_0.
apply Rmult_le_pos.
apply Fourier_util.Rle_zero_pos_plus1; apply Rmult_le_pos.
left; apply Rlt_0_2.
apply Fourier_util.Rle_zero_pos_plus1; left; apply Rlt_0_2.
left; apply pos_half_prf.

assert (precisionNotZero : (1 < prec)%Z) by lia.
assert (emin_neg': (emin <= 0)%Z) by lia.
destruct (format_is_pff_format_can beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x*(bpow s+1)))
  as (fpx,(Hfpx, (Hfpx',Hfpx''))).
rewrite make_bound_Emin in Hfpx''; try assumption.
replace (--emin)%Z with emin in Hfpx'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-px))
  as (fqx,(Hfqx, (Hfqx',Hfqx''))).
rewrite make_bound_Emin in Hfqx''; try assumption.
replace (--emin)%Z with emin in Hfqx'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (qx+px))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x-hx))
  as (ftx,(Hftx, (Hftx',Hftx''))).
rewrite make_bound_Emin in Hftx''; try assumption.
replace (--emin)%Z with emin in Hftx'' by lia.

destruct (format_is_pff_format_can beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (y*(bpow s+1)))
  as (fpy,(Hfpy, (Hfpy',Hfpy''))).
rewrite make_bound_Emin in Hfpy''; try assumption.
replace (--emin)%Z with emin in Hfpy'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (y-py))
  as (fqy,(Hfqy, (Hfqy',Hfqy''))).
rewrite make_bound_Emin in Hfqy''; try assumption.
replace (--emin)%Z with emin in Hfqy'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (qy+py))
  as (fhy,(Hfhy, (Hfhy',Hfhy''))).
rewrite make_bound_Emin in Hfhy''; try assumption.
replace (--emin)%Z with emin in Hfhy'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (y-hy))
  as (fty,(Hfty, (Hfty',Hfty''))).
rewrite make_bound_Emin in Hfty''; try assumption.
replace (--emin)%Z with emin in Hfty'' by lia.

destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (hx*hy))
  as (fx1y1,(Hfx1y1, (Hfx1y1',Hfx1y1''))).
rewrite make_bound_Emin in Hfx1y1''; try assumption.
replace (--emin)%Z with emin in Hfx1y1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (hx*ty))
  as (fx1y2,(Hfx1y2, (Hfx1y2',Hfx1y2''))).
rewrite make_bound_Emin in Hfx1y2''; try assumption.
replace (--emin)%Z with emin in Hfx1y2'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (tx*hy))
  as (fx2y1,(Hfx2y1, (Hfx2y1',Hfx2y1''))).
rewrite make_bound_Emin in Hfx2y1''; try assumption.
replace (--emin)%Z with emin in Hfx2y1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (tx*ty))
  as (fx2y2,(Hfx2y2, (Hfx2y2',Hfx2y2''))).
rewrite make_bound_Emin in Hfx2y2''; try assumption.
replace (--emin)%Z with emin in Hfx2y2'' by lia.

destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (x*y))
  as (fr,(Hfr, (Hfr',Hfr''))).
rewrite make_bound_Emin in Hfr''; try assumption.
replace (--emin)%Z with emin in Hfr'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (-r+x1y1))
  as (ft1,(Hft1, (Hft1',Hft1''))).
rewrite make_bound_Emin in Hft1''; try assumption.
replace (--emin)%Z with emin in Hft1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (t1+x1y2))
  as (ft2,(Hft2, (Hft2',Hft2''))).
rewrite make_bound_Emin in Hft2''; try assumption.
replace (--emin)%Z with emin in Hft2'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (t2+x2y1))
  as (ft3,(Hft3, (Hft3',Hft3''))).
rewrite make_bound_Emin in Hft3''; try assumption.
replace (--emin)%Z with emin in Hft3'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero
  choice (t3+x2y2))
  as (ft4,(Hft4, (Hft4',Hft4''))).
rewrite make_bound_Emin in Hft4''; try assumption.
replace (--emin)%Z with emin in Hft4'' by lia.

assert (Hs:(s =(Z.abs_nat prec - Nat.div2 (Z.abs_nat prec))%nat)).
unfold s; rewrite inj_minus.
assert (TT: (Z.div2 prec = Nat.div2 (Z.abs_nat prec))%Z).
rewrite Nat.div2_div, Z.div2_div, Nat2Z.inj_div; simpl.
rewrite inj_abs; lia.
rewrite <- TT.
rewrite inj_abs; try lia.
rewrite Z.max_r; try lia.
assert (Z.div2 prec <= prec)%Z; try lia.
rewrite Z.div2_div; apply Zlt_le_weak.
apply Z_div_lt; lia.

assert (D:(((- dExp (make_bound beta prec emin) <= Pff.Fexp fx + Pff.Fexp fy)%Z ->
        (FtoR beta fx * FtoR beta fy = FtoR beta fr + FtoR beta ft4)) /\
   Rabs (FtoR beta fx * FtoR beta fy - (FtoR beta fr + FtoR beta ft4)) <=
       7 / 2 * powerRZ beta (- dExp (make_bound beta prec emin)))).
apply Dekker with (Z.abs_nat prec) fpx fqx fhx ftx fpy fqy fhy fty
   fx1y1 fx1y2 fx2y1 fx2y2 ft1 ft2 ft3; try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 4%nat with (Z.abs_nat 4) by easy.
apply Zabs_nat_le; lia.

rewrite Hfx, <- Hs, <- bpow_powerRZ; apply Hfpx'.
rewrite Hfx, Hfpx''; apply Hfqx'.
rewrite Hfpx'', Hfqx''; apply Hfhx'.
rewrite Hfx, Hfhx''; apply Hftx'.
rewrite Hfy, <- Hs, <- bpow_powerRZ; apply Hfpy'.
rewrite Hfy, Hfpy''; apply Hfqy'.
rewrite Hfpy'', Hfqy''; apply Hfhy'.
rewrite Hfy, Hfhy''; apply Hfty'.
rewrite Hfhx'', Hfhy''; apply Hfx1y1'.
rewrite Hfhx'', Hfty''; apply Hfx1y2'.
rewrite Hftx'', Hfhy''; apply Hfx2y1'.
rewrite Hftx'', Hfty''; apply Hfx2y2'.
rewrite Hfx, Hfy; apply Hfr'.
rewrite Hfr'', Hfx1y1''; apply Hft1'.
rewrite Hft1'', Hfx1y2''; apply Hft2'.
rewrite Hft2'', Hfx2y1''; apply Hft3'.
rewrite Hft3'', Hfx2y2''; apply Hft4'.
rewrite make_bound_Emin; lia.
case HH; intros K;[now left|right].
destruct K as (l,Hl).
exists (Z.abs_nat l).
apply Nat2Z.inj.
rewrite inj_mult.
rewrite 2!inj_abs; lia.

rewrite <- Hfx, <- Hfy.
unfold r; rewrite <- Hfr''.
unfold t4; rewrite <- Hft4''.
destruct D as (D1,D2); split.
intros L.
apply D1.
apply underf_mult_aux' with beta prec; try assumption.
apply make_bound_p; assumption.
now apply FcanonicBound with beta.
now apply FcanonicBound with beta.
case L; intros L'.
contradict L'.
apply Rmult_integral_contrapositive_currified.
rewrite Hfx; easy.
rewrite Hfy; easy.
apply Rle_trans with (2:=L').
right; repeat f_equal.
rewrite make_bound_Emin, Z.opp_involutive; lia.
apply Rle_trans with (1:=D2).
rewrite make_bound_Emin, Z.opp_involutive.
2: lia.
rewrite bpow_powerRZ.
now right.
Qed.

End Dekker.

Section ErrFMA_V1.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis Even_radix: Even beta.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Variable choice : Z -> bool.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).

Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let alpha1 := round_flt (y+u2).
Let alpha2 := (y+u2)-alpha1.
Let beta1 := round_flt (u1+alpha1).
Let beta2 := (u1+alpha1) - beta1.
Let gamma := round_flt (round_flt (beta1-r1)+beta2).
Let r2 := round_flt (gamma+alpha2).
Let r3 := (gamma+alpha2) -r2.

Hypothesis V1_Und1: a * x = 0 \/ bpow beta (emin + 2 * prec - 1) <= Rabs (a * x).
Hypothesis V1_Und2: alpha1 = 0 \/ bpow beta (emin + prec) <= Rabs alpha1.
Hypothesis V1_Und4: beta1 = 0 \/ bpow beta (emin + prec+1) <= Rabs beta1.
Hypothesis V1_Und5: r1 = 0 \/ bpow beta (emin + prec-1) <= Rabs r1.

Lemma V1_Und3': u1 = 0 \/ bpow beta (emin + 2*prec-1) <= Rabs u1.
Proof using V1_Und1 choice prec_gt_0_ precisionGe3.
Proof with auto with typeclass_instances.
case V1_Und1; intros K.
left; unfold u1.
rewrite K; apply round_0...
right; unfold u1.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
Qed.

Lemma V1_Und3: u1 = 0 \/ bpow beta (emin + prec) <= Rabs u1.
Proof using V1_Und1 choice prec_gt_0_ precisionGe3.
case V1_Und3';[now left|right].
apply Rle_trans with (2:=H).
apply bpow_le; lia.
Qed.

Lemma ErrFMA_bounded: format r1 /\ format r2 /\ format r3.
Proof using Fa Fx Fy V1_Und1 alpha2 gamma prec_gt_0_.
Proof with auto with typeclass_instances.
split.
apply generic_format_round...
split.
apply generic_format_round...
replace (r3) with (-(r2-(gamma+alpha2))) by (unfold r3; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
replace (alpha2) with (-(alpha1-(y+u2))) by (unfold alpha2; ring).
apply generic_format_opp.
apply plus_error...
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case V1_Und1; easy.
Qed.

Lemma ErrFMA_correct:
   a*x+y = r1+r2+r3.
Proof using Even_radix Fa Fx Fy V1_Und1 V1_Und2 V1_Und4 V1_Und5 alpha2 emin_neg gamma prec_gt_0_ precisionGe3.
Proof with auto with typeclass_instances.

destruct V1_Und1 as [HZ|Und1'].
assert (HZ1: u1 = 0).
unfold u1; rewrite HZ; apply round_0...
rewrite HZ; unfold r3; ring_simplify.
unfold gamma, alpha2, beta2, beta1, alpha1.
rewrite HZ1; replace u2 with 0.
rewrite Rplus_0_r, Rplus_0_l; rewrite 2!round_generic with (x:=y)...
replace r1 with y.
replace (y-y) with 0 by ring.
rewrite Rplus_0_r, round_0...
rewrite Rplus_0_r, round_0...
ring.
unfold r1; rewrite HZ.
rewrite Rplus_0_l, round_generic...
unfold u2; rewrite HZ, HZ1; ring.

assert (precisionNotZero : (1 < prec)%Z) by lia.
replace (r1+r2+r3) with (r1+gamma+alpha2).
2: unfold r3; ring.
assert (J1: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
assert (J2: format alpha2).
replace (alpha2) with (-(alpha1-(y+u2))) by (unfold alpha2; ring).
apply generic_format_opp.
apply plus_error...
assert (J3: format beta2).
replace (beta2) with (-(beta1-(u1+alpha1))) by (unfold beta2; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
apply generic_format_round...

destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero u2)
  as (fu2,(Hfu2,Hfu2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero alpha2)
  as (fal2,(Hfal2,Hfal2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero beta2)
  as (fbe2,(Hfbe2,Hfbe2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
rewrite <- Hfa, <- Hfx, <- Hfy, <- Hfal2.

destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (a*x+y))
  as (fr1,(Hfr1, (Hfr1',Hfr1''))).
rewrite make_bound_Emin in Hfr1''; try assumption.
replace (--emin)%Z with emin in Hfr1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (a*x))
  as (fu1,(Hfu1, (Hfu1',Hfu1''))).
rewrite make_bound_Emin in Hfu1''; try assumption.
replace (--emin)%Z with emin in Hfu1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (y+u2))
  as (fal1,(Hfal1, (Hfal1',Hfal1''))).
rewrite make_bound_Emin in Hfal1''; try assumption.
replace (--emin)%Z with emin in Hfal1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (u1+alpha1))
  as (fbe1,(Hfbe1, (Hfbe1',Hfbe1''))).
rewrite make_bound_Emin in Hfbe1''; try assumption.
replace (--emin)%Z with emin in Hfbe1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (beta1-r1))
  as (ff,(Hff, (Hff',Hff''))).
rewrite make_bound_Emin in Hff''; try assumption.
replace (--emin)%Z with emin in Hff'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (FtoR beta ff+beta2))
  as (fga,(Hfga, (Hfga',Hfga''))).
rewrite make_bound_Emin in Hfga''; try assumption.
replace (--emin)%Z with emin in Hfga'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (gamma+alpha2))
  as (fr2,(Hfr2, (Hfr2',Hfr2''))).
rewrite make_bound_Emin in Hfr2''; try assumption.
replace (--emin)%Z with emin in Hfr2'' by lia.
unfold r1; rewrite <- Hfr1''.
unfold gamma; rewrite <- Hff'', <- Hfga''.

apply FmaErr with (make_bound beta prec emin) (Z.abs_nat prec)
  (fun r f => f = RND_Closest (make_bound beta prec emin) beta (Z.abs_nat prec) choice r)
   fu1 fu2 fal1 fbe1 fbe2 ff;
  try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 3%nat with (Z.abs_nat 3).
apply Zabs_nat_le; lia.
now unfold Z.abs_nat, Pos.to_nat.
intros r f H.
rewrite H.
apply RND_Closest_correct.
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
apply make_bound_p; lia.
intros x1 x2 g1 g2 K1 K2 K3.
rewrite K1, K2, K3; easy.

rewrite Hfal1''; fold alpha1.
case V1_Und2; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; lia.
lia.
apply FcanonicBound with (1:=Hfal1).
rewrite Hfal1''; fold alpha1.
now rewrite make_bound_Emin, Z.opp_involutive.
rewrite Hfu1''; fold u1.
case V1_Und3; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; lia.
lia.
apply FcanonicBound with (1:=Hfu1).
rewrite Hfu1''; fold u1.
now rewrite make_bound_Emin, Z.opp_involutive.
rewrite Hfbe1''; fold beta1.
case V1_Und4; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; lia.
lia.
apply FcanonicBound with (1:=Hfbe1).
rewrite Hfbe1''; fold beta1.
rewrite make_bound_Emin, Z.opp_involutive; try assumption.
apply Rle_trans with (2:=V); right.
f_equal; ring.
rewrite Hfr1''; fold r1.
case V1_Und5; intros V;[now right|left].
apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite Hfr1''; fold r1.
rewrite make_bound_Emin, Z.opp_involutive; try assumption.
apply underf_mult_aux' with beta prec; try assumption.
apply make_bound_p; lia.
rewrite Hfa, Hfx.
apply Rle_trans with (2:=Und1').
rewrite make_bound_Emin, Z.opp_involutive.
now right.
lia.

rewrite Hfa, Hfx; apply Hfu1'.
now rewrite Hfu2, Hfa, Hfx, Hfu1''.
rewrite Hfy, Hfu2; apply Hfal1'.
now rewrite Hfal2, Hfy, Hfu2, Hfal1''.
now rewrite Hfbe2, Hfu1'', Hfal1'', Hfbe1''.
rewrite Hfbe1'', Hfr1''; apply Hff'.
rewrite Hfbe2; apply Hfga'.
apply FcanonicUnique with (4:=Hfr1) (precision:=Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq.
apply absolu_lt_nz; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
apply make_bound_p; lia.
rewrite Hfr1''.
rewrite Hfa, Hfx, Hfy.
rewrite pff_round_N_is_round; try assumption.
f_equal; f_equal.
rewrite make_bound_Emin; try easy; ring.
apply make_bound_p; lia.
rewrite Hfu1'', Hfal1''; fold u1; fold alpha1.
apply FcanonicUnique with (4:=Hfbe1) (precision:=Z.abs_nat prec).
apply radix_gt_1.
apply sym_not_eq, Nat.lt_neq.
apply absolu_lt_nz; lia.
apply make_bound_p; lia.
apply RND_Closest_canonic.
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.
apply make_bound_p; lia.
rewrite pff_round_N_is_round; try assumption.
rewrite Hfbe1''.
f_equal; f_equal.
rewrite make_bound_Emin; try easy; ring.
apply make_bound_p; lia.
Qed.

End ErrFMA_V1.

Section ErrFMA_V2.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis Even_radix: Even beta.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).

Lemma mult_error_FLT_ge_bpow': forall a b e, format a -> format b ->
   a*b = 0 \/ bpow beta e <= Rabs (a*b) ->
   a*b-round_flt (a*b) = 0 \/
     bpow beta (e+1-2*prec) <= Rabs (a*b-round_flt (a*b)).
Proof using .
Proof with auto with typeclass_instances.
intros a b e Fa Fb H.
case (Req_dec (a * b - round_flt (a * b)) 0); intros Z1;[now left|right].
rewrite <- Rabs_Ropp.
replace (- (a * b - round_flt (a * b))) with (round_flt (a * b) - a*b) by ring.
case H; intros H'.
contradict Z1.
rewrite H', round_0...
ring.
apply mult_error_FLT_ge_bpow...
apply Rle_trans with (2:=H'); apply bpow_le; lia.
replace (round_flt (a * b) - a*b) with (- (a * b - round_flt (a * b))) by ring.
now apply Ropp_neq_0_compat.
Qed.

Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let alpha1 := round_flt (y+u2).
Let alpha2 := (y+u2)-alpha1.
Let beta1 := round_flt (u1+alpha1).
Let beta2 := (u1+alpha1) - beta1.
Let gamma := round_flt (round_flt (beta1-r1)+beta2).
Let r2 := round_flt (gamma+alpha2).
Let r3 := (gamma+alpha2) -r2.

Hypothesis U1: a * x = 0 \/ bpow beta (emin + 4*prec - 3) <= Rabs (a * x).
Hypothesis U2: y = 0 \/ bpow beta (emin + 2*prec) <= Rabs y.

Lemma ErrFMA_bounded_simpl: format r1 /\ format r2 /\ format r3.
Proof using Fa Fx Fy U1 alpha2 gamma prec_gt_0_ precisionGe3.
Proof with auto with typeclass_instances.
apply ErrFMA_bounded; try assumption.
case U1; intros H; [now left|right].
apply Rle_trans with (2:=H); apply bpow_le.
lia.
Qed.

Lemma V2_Und4: a*x <> 0 -> beta1 = 0 \/ bpow beta (emin + prec+1) <= Rabs beta1.
Proof using U1 alpha1 prec_gt_0_ precisionGe3.
Proof with auto with typeclass_instances.
intros Zax.
unfold beta1; case U1; intros H.
now contradict H.
case (Req_dec (round_flt (u1 + alpha1)) 0%R); intros L;[now left|right].
apply round_FLT_plus_ge; try assumption...
apply generic_format_round...
apply generic_format_round...
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=H).
apply bpow_le; lia.
Qed.

Lemma V2_Und2:  y <> 0 ->  alpha1 = 0 \/ bpow beta (emin + prec) <= Rabs alpha1.
Proof using Fa Fx Fy U1 U2 prec_gt_0_ precisionGe3 u2.
Proof with auto with typeclass_instances.
intros Zy.
unfold alpha1.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case U1; intros H; try easy.
apply Rle_trans with (2:=H); apply bpow_le.
lia.
case (Req_dec (round_flt (y + u2)) 0%R); intros L;[now left|right].
apply round_FLT_plus_ge...
case U2; try easy; intros M.
apply Rle_trans with (2:=M); apply bpow_le; lia.
Qed.

Lemma V2_Und5: a*x <> 0 -> r1 = 0 \/ bpow beta (emin + prec-1) <= Rabs r1.
Proof using Fa Fx Fy U1 U2 prec_gt_0_ precisionGe3.
Proof with auto with typeclass_instances.
intros Zax.
case (Req_dec r1 0); intros Zr1.
now left.
case U1; intros H.
now contradict H.
right.
case U2; intros Hy.
unfold r1; rewrite Hy, Rplus_0_r.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=H).
apply bpow_le; lia.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
case (Req_dec u2 0); intros Zu2.
rewrite Zu2, Rplus_0_r.
case (Req_dec (round_flt (u1 + y)) 0%R); intros L.
contradict Zr1.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
now rewrite Zu2, Rplus_0_r.
rewrite Rplus_comm; apply round_FLT_plus_ge...
apply generic_format_round...
apply Rle_trans with (2:=Hy).
apply bpow_le; lia.
now rewrite Rplus_comm.

assert (T:round_flt (u1 + y) <> 0 -> (bpow beta (emin + 3 * prec - 2 - prec) <=
 Rabs (round_flt (u1 + y)))).
intros K; apply round_FLT_plus_ge...
apply generic_format_round...
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=H).
apply bpow_le; lia.
case (Req_dec (u1+y) 0); intros H1.
replace (u1+u2+y) with (u1+y+u2) by ring.
rewrite H1, Rplus_0_l.
case (mult_error_FLT_ge_bpow' a x (emin + 4 * prec - 3)); try assumption.
intros H2; contradict Zr1.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
replace (u1+u2+y) with (u1+y+u2) by ring.
rewrite H1, Rplus_0_l.
unfold u2, u1; rewrite H2, round_0...
fold u1 u2; intros H2.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=H2).
apply bpow_le; lia.
generalize Zr1; unfold r1.
replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
replace (u1+u2+y) with ((u1+y)+u2) by ring.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case U1; intros J; try easy.
apply Rle_trans with (2:=J); apply bpow_le.
lia.
intros K; apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
assert (K':u1 + y + u2 <> 0).
intros L; apply K; rewrite L.
apply round_0...
generalize K'.
unfold u1; unfold round.
rewrite Fy, Fu2.
rewrite <- F2R_plus, <- F2R_plus.
intros L.
apply Rle_trans with (2:=F2R_ge _ _ L).
rewrite 2!Fexp_Fplus.
apply bpow_le.
apply Z.min_glb.
apply Z.min_glb.
simpl.
apply Z.le_trans with (FLT_exp emin prec (emin +3*prec-1)).
unfold FLT_exp.
rewrite Z.max_l; lia.
apply cexp_ge_bpow...
apply Rle_trans with (2:=H).
apply bpow_le; lia.
simpl.
apply Z.le_trans with (FLT_exp emin prec (emin +2*prec+1)).
unfold FLT_exp.
rewrite Z.max_l; lia.
apply cexp_ge_bpow...
apply Rle_trans with (2:=Hy).
apply bpow_le; lia.
simpl.
apply Z.le_trans with (FLT_exp emin prec (emin +2*prec-1)).
unfold FLT_exp.
rewrite Z.max_l; lia.
apply cexp_ge_bpow...
case (mult_error_FLT_ge_bpow' a x (emin+4*prec-3)); try assumption.
intros Z; contradict Zu2.
unfold u2, u1; easy.
intros H2.
apply Rle_trans with (2:=H2).
apply bpow_le.
lia.
Qed.

Lemma ErrFMA_correct_simpl:
   a*x+y = r1+r2+r3.
Proof using Even_radix Fa Fx Fy U1 U2 alpha2 emin_neg gamma prec_gt_0_ precisionGe3.
Proof with auto with typeclass_instances.

case (Req_dec (a*x) 0); intros Zax.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, u1, alpha1, alpha2,u2,u1.
rewrite Zax, round_0...
unfold Rminus; repeat rewrite Rplus_0_l.
rewrite Ropp_0, Rplus_0_r.
repeat rewrite (round_generic _ _ _ y)...
replace (y+-y) with 0 by ring.
rewrite round_0, Rplus_0_l...
rewrite round_0, Rplus_0_l...
rewrite round_0, Rplus_0_l...
ring.

case (Req_dec u2 0); intros Zu2.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, u1, alpha1, alpha2.
rewrite Zu2, Rplus_0_r.
repeat rewrite (round_generic _ _ _ y)...
ring_simplify.
assert (G:round_flt (a * x) = a*x).
apply trans_eq with (u1+u2).
now rewrite Zu2, Rplus_0_r.
unfold u2, u1; ring.
rewrite G.
replace (round_flt (a * x + y) - round_flt (a * x + y)) with 0 by ring.
rewrite round_0, Rplus_0_l...
rewrite (round_generic _ _ _ (a * x + y - round_flt (a * x + y))).
ring.
replace (a * x + y - round_flt (a * x + y)) with
 (- (round_flt (a * x + y) -(a*x+y))) by ring.
apply generic_format_opp.
rewrite <- G.
apply plus_error...
apply generic_format_round...

case (Req_dec y 0); intros Zy.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case U1; intros H; try easy.
apply Rle_trans with (2:=H); apply bpow_le.
lia.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, alpha1, alpha2.
rewrite Zy, Rplus_0_r, Rplus_0_l; fold u1.
rewrite (round_generic _ _ _ u2)...
replace (u1+u2) with (a*x).
2: unfold u2, u1; ring.
fold u1; ring_simplify (u1-u1).
rewrite round_0...
rewrite Rplus_0_l.
fold u2; rewrite (round_generic _ _ _ u2)...
ring_simplify (u2+(u2-u2)).
rewrite (round_generic _ _ _ u2)...
unfold u2,u1; ring.

apply ErrFMA_correct; try assumption.
case U1; intros H; [now left|right].
apply Rle_trans with (2:=H); apply bpow_le.
lia.
fold u1 u2 alpha1.
now apply V2_Und2.
fold u1 u2 alpha1 alpha2.
now apply V2_Und4.
now apply V2_Und5.
Qed.

End ErrFMA_V2.

Section ErrFmaApprox.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis precisionGe3 : (4 <= prec)%Z.
Variable choice : Z -> bool.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).

Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let v1 := round_flt (y+u1).
Let v2 := (y+u1)-v1.
Let t1 := round_flt (v1-r1).
Let t2 := round_flt (u2+v2).
Let r2 := round_flt (t1+t2).

Hypothesis Und1: a * x = 0 \/ bpow beta (emin + 2 * prec - 1) <= Rabs (a * x).
Hypothesis Und2: v1 = 0 \/ bpow beta (emin + prec - 1) <= Rabs v1.
Hypothesis Und3: r1 = 0 \/ bpow beta (emin + prec - 1) <= Rabs r1.
Hypothesis Und4: r2 = 0 \/ bpow beta (emin + prec - 1) <= Rabs r2.
Hypothesis Und5: t2 = 0 \/ bpow beta (emin + prec - 1) <= Rabs t2.

Lemma ErrFmaAppr_correct:
   Rabs (r1+r2 -(a*x+y)) <= (3*beta/2+/2) * bpow beta (2-2*prec)%Z * Rabs (r1).
Proof using Fa Fx Fy Und1 Und2 Und3 Und4 Und5 emin_neg prec_gt_0_ precisionGe3.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.
assert (J1: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros L; case Und1; easy.
assert (J2: format v2).
replace (v2) with (-(v1-(y+u1))) by (unfold v2; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
assert (G: forall f, Fcanonic beta (make_bound beta prec emin) f -> (FtoR beta f = 0 \/
   bpow beta (emin+prec-1)%Z <= Rabs (FtoR beta f)) ->
    Fnormal beta (make_bound beta prec emin) f \/
      FtoR beta f = 0%nat).
intros f Hf K; case K; [right|left].
now rewrite H.
apply CanonicGeNormal with prec; try easy.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
apply Rle_trans with (2:=H).
apply bpow_le; lia.

case Und1; intros Und1'.
unfold r2, t1, t2, v2, v1, r1, u2, u1; rewrite Und1'.
rewrite round_0...
rewrite Rplus_0_l, Rplus_0_r.
rewrite (round_generic _ _ _ y)...
replace (y-y) with 0 by ring.
rewrite Rplus_0_r, Rminus_0_l, Ropp_0, round_0...
rewrite Rplus_0_l, round_0...
replace (y+0-y) with 0 by ring; rewrite Rabs_R0.
apply Rmult_le_pos.
2: apply Rabs_pos.
apply Rmult_le_pos; try apply bpow_ge_0.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos.
apply Rmult_le_pos.
auto with real.
left; apply IZR_lt; apply radix_gt_0.
left; apply pos_half_prf.
left; apply pos_half_prf.

destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero u2)
  as (fu2,(Hfu2,Hfu2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero v2)
  as (fv2,(Hfv2,Hfv2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.

destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (a*x+y))
  as (fr1,(Hfr1, (Hfr1',Hfr1''))).
rewrite make_bound_Emin in Hfr1''; try assumption.
replace (--emin)%Z with emin in Hfr1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (a*x))
  as (fu1,(Hfu1, (Hfu1',Hfu1''))).
rewrite make_bound_Emin in Hfu1''; try assumption.
replace (--emin)%Z with emin in Hfu1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (y+u1))
  as (fv1,(Hfv1, (Hfv1',Hfv1''))).
rewrite make_bound_Emin in Hfv1''; try assumption.
replace (--emin)%Z with emin in Hfv1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (v1-r1))
  as (ft1,(Hft1, (Hft1',Hft1''))).
rewrite make_bound_Emin in Hft1''; try assumption.
replace (--emin)%Z with emin in Hft1'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (u2+v2))
  as (ft2,(Hft2, (Hft2',Hft2''))).
rewrite make_bound_Emin in Hft2''; try assumption.
replace (--emin)%Z with emin in Hft2'' by lia.
destruct (round_N_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero choice (t1+t2))
  as (fr2,(Hfr2, (Hfr2',Hfr2''))).
rewrite make_bound_Emin in Hfr2''; try assumption.
replace (--emin)%Z with emin in Hfr2'' by lia.

unfold r1; rewrite <- Hfr1''.
unfold r2; rewrite <- Hfr2''.
rewrite <- Hfa, <- Hfx, <- Hfy.
rewrite bpow_powerRZ.
replace prec with (Z.of_nat (Z.abs_nat prec)).
2: rewrite inj_abs; lia.
apply ErrFmaApprox with (make_bound beta prec emin) fu1 fu2 fv1 fv2 ft1 ft2; try assumption.
apply radix_gt_1.
apply make_bound_p; lia.
replace 4%nat with (Z.abs_nat 4).
apply Zabs_nat_le; lia.
now unfold Z.abs_nat, Pos.to_nat.

apply G; try assumption.
case Und1; intros K1;[left|right].
rewrite Hfu1'', K1, round_0...
rewrite Hfu1''.
apply abs_round_ge_generic...
apply generic_format_bpow.
unfold FLT_exp; rewrite Z.max_l; lia.
apply Rle_trans with (2:=K1).
apply bpow_le; lia.
apply G; try assumption.
rewrite Hfv1''; apply Und2.
apply G; try assumption.
rewrite Hfr1''; apply Und3.
apply G; try assumption.
rewrite Hfr2''; apply Und4.
apply G; try assumption.
rewrite Hft2''; apply Und5.
apply underf_mult_aux' with beta prec; try assumption.
apply make_bound_p; assumption.
rewrite Hfa, Hfx.
apply Rle_trans with (2:=Und1').
apply bpow_le.
rewrite make_bound_Emin, Z.opp_involutive; lia.

rewrite Hfa, Hfx, Hfy; apply Hfr1'.
rewrite Hfa, Hfx; apply Hfu1'.
now rewrite Hfu2, Hfa, Hfx, Hfu1''.
rewrite Hfu1'', Hfy, Rplus_comm; apply Hfv1'.
rewrite Hfv2, Hfu1'', Hfy, Hfv1''.
unfold v2; unfold v1; unfold u1; ring.
rewrite Hfv1'', Hfr1''; apply Hft1'.
rewrite Hfu2, Hfv2; apply Hft2'.
rewrite Hft1'', Hft2''; apply Hfr2'.
Qed.

End ErrFmaApprox.

Section Axpy.
Variable emin prec : Z.
Variable choice : Z -> bool.
Hypothesis precisionGt : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) (Znearest choice)).
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation bpow e := (bpow radix2 e).

Variable a x y:R.
Variable ta tx ty:R.
Hypothesis Fta: format ta.
Hypothesis Ftx: format tx.
Hypothesis Fty: format ty.

Let tv := round_flt (ty+ round_flt (ta*tx)).

Hypothesis H1 : (5+4*bpow (-prec))/(1-bpow (-prec))*
   (Rabs (ta*tx)+ bpow (emin-1)) <= Rabs ty.

Hypothesis H2 : Rabs (y-ty) + Rabs (a*x-ta*tx) <=
    bpow (-prec-2)*(1-bpow (1-prec))*Rabs ty -
    bpow (-prec-2)*Rabs (ta*tx) - bpow (emin-2).

Theorem Axpy :
  tv = round radix2 (FLT_exp emin prec) Zfloor (y+a*x) \/
     tv = round radix2 (FLT_exp emin prec) Zceil (y+a*x).
Proof using Fta Ftx Fty H1 H2 choice emin_neg precisionGt.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.

destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero ta)
  as (fta,(Hfta,Hfta')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero tx)
  as (ftx,(Hftx,Hftx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero ty)
  as (fty,(Hfty,Hfty')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.

destruct (round_N_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero choice (ta*tx))
  as (fg,(Hfg, (Hfg',Hfg''))).
rewrite make_bound_Emin in Hfg''; try assumption.
replace (--emin)%Z with emin in Hfg'' by lia.
destruct (round_N_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero choice (ty+FtoR radix2 fg))
  as (ftv,(Hftv, (Hftv',Hftv''))).
rewrite make_bound_Emin in Hftv''; try assumption.
replace (--emin)%Z with emin in Hftv'' by lia.

assert (MinOrMax radix2 (make_bound radix2 prec emin) (a*x+y) ftv).
unfold radix2 in Hfty, Hftx, Hfta; simpl in Hfty, Hftx, Hfta.
apply Axpy_opt with (Z.abs_nat prec) fta ftx fty fg; try assumption.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
now apply FcanonicBound with radix2.
now apply FcanonicBound with radix2.
now rewrite Hfta, Hftx.
now rewrite Rplus_comm, Hfty.
rewrite Hfty, Hftx, Hfta.
rewrite inj_abs; try lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
clear -H1.
apply Rle_trans with (2:=H1); right.
f_equal.
rewrite bpow_powerRZ.
unfold Rdiv; simpl; f_equal; ring.
f_equal; rewrite bpow_powerRZ.
simpl; f_equal; easy.
rewrite Hfty, Hfta,Hftx.
rewrite inj_abs; try lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
clear -H2.
apply Rle_trans with (1:=H2); right.
rewrite 3!bpow_powerRZ; unfold Z.pred, Z.succ.
unfold Rminus; f_equal; f_equal; f_equal.
f_equal; f_equal;[ring| f_equal; f_equal; ring].
f_equal; f_equal; ring.
ring.

unfold tv; rewrite <- Hfg'', <- Hftv''.
case H; intros H'; [left|right].
apply trans_eq with (FtoR radix2 (RND_Min
   (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (a*x+y))).
apply MinUniqueP with  (make_bound radix2 prec emin) (a*x+y)%R; try easy.
apply RND_Min_correct; try easy.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite pff_round_DN_is_round.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Rplus_comm; easy.
apply make_bound_p; lia.
lia.
apply trans_eq with (FtoR radix2 (RND_Max
   (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (a*x+y))).
apply MaxUniqueP with  (make_bound radix2 prec emin) (a*x+y)%R; try easy.
apply RND_Max_correct; try easy.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; lia.
apply make_bound_p; lia.
rewrite pff_round_UP_is_round.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Rplus_comm; easy.
apply make_bound_p; lia.
lia.
Qed.

End Axpy.

Section Discri1.
Variable emin prec : Z.
Hypothesis precisionGt : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation bpow e := (bpow radix2 e).

Variable a b c:R.
Hypothesis Fa: format a.
Hypothesis Fb: format b.
Hypothesis Fc: format c.

Let p:=round_flt (b*b).
Let q:=round_flt (a*c).
Let dp:= b*b-p.
Let dq:= a*c-q.
Let d:= if (Rle_bool (p+q) (3*Rabs (p-q)))
            then round_flt (p-q)
            else round_flt (round_flt (p-q) + round_flt(dp-dq)).

Hypothesis U1 : b * b <> 0 ->
    bpow (emin + 3 * prec) <= Rabs (b * b).
Hypothesis U2 : a * c <> 0 ->
    bpow (emin + 3 * prec) <= Rabs (a * c).
Hypothesis Zd : d <> 0.

Lemma U3_discri1 : b * b <> 0 -> a * c <> 0 -> p - q <> 0 ->
   bpow (emin + 2*prec) <= Rabs (round_flt (p-q)).
Proof using U1 prec_gt_0_ precisionGt.
Proof with auto with typeclass_instances.
intros Z1 Z2 Z3.
unfold Rminus; apply round_FLT_plus_ge...
apply generic_format_round...
apply generic_format_opp, generic_format_round...
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=U1 Z1); apply bpow_le; lia.
apply round_plus_neq_0...
apply generic_format_round...
apply generic_format_opp, generic_format_round...
Qed.

Lemma U4_discri1 : b * b <> 0 -> a * c <> 0 -> p - q <> 0 ->
    bpow (emin + prec) <= Rabs d.
Proof using U1 Zd prec_gt_0_ precisionGt.
Proof with auto with typeclass_instances.
intros Z1 Z2 Z3; generalize Zd; unfold d.
case (Rle_bool_spec _ _); intros H Z4.
apply Rle_trans with (2:=U3_discri1 Z1 Z2 Z3).
apply bpow_le; lia.
apply round_FLT_plus_ge...
apply generic_format_round...
apply generic_format_round...
replace (emin + prec + prec)%Z with (emin+2*prec)%Z by ring.
apply U3_discri1; easy.
Qed.

Lemma format_dp : format dp.
Proof using Fb U1 p prec_gt_0_ precisionGt.
Proof with auto with typeclass_instances.
replace (dp) with (-(p-(b*b))) by (unfold dp; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros Zbb; apply Rle_trans with (2:=U1 Zbb).
apply bpow_le; lia.
Qed.

Lemma format_dq : format dq.
Proof using Fa Fc U2 prec_gt_0_ precisionGt q.
Proof with auto with typeclass_instances.
replace (dq) with (-(q-(a*c))) by (unfold dq; ring).
apply generic_format_opp.
apply mult_error_FLT...
intros Zac; apply Rle_trans with (2:=U2 Zac).
apply bpow_le; lia.
Qed.

Lemma format_d_discri1 : format d.
Proof using dp dq prec_gt_0_.
Proof with auto with typeclass_instances.
unfold d; case (Rle_bool _ _).
apply generic_format_round...
apply generic_format_round...
Qed.

Lemma U5_discri1_aux : forall x y e, format x -> format y
   -> (emin <= e)%Z -> bpow e <= Rabs x -> bpow e <= Rabs y
   -> round_flt (x+y) <> x+y
   -> bpow e <= Rabs (round_flt (x+y)).
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
intros x y e Fx Fy He Hex Hey H.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
case (Rle_or_lt (bpow e) (Rabs (x+y))); intros H1; try easy.
absurd (round_flt (x + y) = x + y); try assumption.
apply round_generic...
apply generic_format_plus...
apply Rlt_le; apply Rlt_le_trans with (1:=H1).
destruct (mag radix2 x) as (ex,Y1).
destruct (mag radix2 y) as (ey,Y2); simpl.
apply bpow_le.
apply Z.min_glb.
apply le_bpow with radix2.
apply Rle_trans with (1:=Hex).
apply Rlt_le, Y1.
intros Zx; contradict H.
rewrite Zx, Rplus_0_l, round_generic...
apply le_bpow with radix2.
apply Rle_trans with (1:=Hey).
apply Rlt_le, Y2.
intros Zy; contradict H.
rewrite Zy, Rplus_0_r, round_generic...
Qed.

Lemma U5_discri1 : b * b <> 0 -> a*c <> 0 ->
  round_flt (dp - dq) <> dp - dq ->
  bpow (emin + prec - 1) <= Rabs (round_flt (dp - dq)).
Proof using Fa Fb Fc U1 U2 prec_gt_0_ precisionGt.
Proof with auto with typeclass_instances.
intros Z1 Z2 Z3.
apply U5_discri1_aux.
apply format_dp...
apply generic_format_opp, format_dq...
lia.
unfold dp; replace (b * b - p) with (-(p-b*b)) by ring.
rewrite Rabs_Ropp; unfold p.
apply mult_error_FLT_ge_bpow...
apply Rle_trans with (2:=U1 Z1).
apply bpow_le; lia.
replace (round_flt (b * b) - b * b) with (-dp).
apply Ropp_neq_0_compat.
intros Z4; contradict Z3.
rewrite Z4, Rminus_0_l, round_generic...
apply generic_format_opp, format_dq...
unfold dp, p; ring.
unfold dq; replace (-(a * c - q)) with (q-a*c) by ring.
unfold q; apply mult_error_FLT_ge_bpow...
apply Rle_trans with (2:=U2 Z2).
apply bpow_le; lia.
replace (round_flt (a * c) - a * c) with (-dq).
apply Ropp_neq_0_compat.
intros Z4; contradict Z3.
rewrite Z4, Rminus_0_r, round_generic...
apply format_dp...
unfold dq, q; ring.
easy.
Qed.

Theorem discri_correct_test :
 Rabs (d-(b*b-a*c)) <= 2* ulp_flt d.
Proof using Fa Fb Fc U1 U2 Zd emin_neg prec_gt_0_ precisionGt.
Proof with auto with typeclass_instances.

case (Req_dec (b*b) 0); intros Zbb.
unfold d, p; rewrite Zbb, round_0...
rewrite Rplus_0_l, Rminus_0_l, Rabs_Ropp.
rewrite Rle_bool_true.
rewrite round_NE_opp.
rewrite ulp_opp.
rewrite round_generic...
2: apply generic_format_round...
apply Rle_trans with (Rabs (-(q-a*c))).
right; f_equal; ring.
rewrite Rabs_Ropp.
apply Rle_trans with (1:=error_le_half_ulp_round _ _ _ _).
fold q; apply Rmult_le_compat_r.
apply ulp_ge_0.
lra.
apply Rle_trans with (1:=RRle_abs _).
rewrite <- (Rmult_1_l (Rabs _)) at 1.
apply Rmult_le_compat_r.
apply Rabs_pos.
lra.
case (Req_dec (a*c) 0); intros Zac.
unfold d, q; rewrite Zac, round_0...
rewrite Rplus_0_r, 2!Rminus_0_r.
rewrite Rle_bool_true.
rewrite round_generic...
2: apply generic_format_round...
apply Rle_trans with (1:=error_le_half_ulp_round _ _ _ _).
fold p; apply Rmult_le_compat_r.
apply ulp_ge_0.
lra.
apply Rle_trans with (1:=RRle_abs _).
rewrite <- (Rmult_1_l (Rabs _)) at 1.
apply Rmult_le_compat_r.
apply Rabs_pos.
lra.

case (Req_dec (p-q) 0); intros Zpq.
assert (H:d = round_flt (dp - dq)).
unfold d; case (Rle_bool_spec _ _); intros H.
contradict Zd.
unfold d; rewrite Rle_bool_true; try assumption.
rewrite Zpq, round_0...
rewrite Zpq, round_0...
rewrite Rplus_0_l, round_generic...
apply generic_format_round...
replace d with (round_flt (b * b - a * c)).
apply Rle_trans with (1:=error_le_half_ulp_round _ _ _ _).
apply Rmult_le_compat_r.
apply ulp_ge_0.
lra.
rewrite H; f_equal.
unfold dp, dq; apply trans_eq with (b * b - a * c - (p-q)).
rewrite Zpq; ring.
ring.

assert (G: (3 * Rabs (p - q) < p + q /\ round_flt (dp - dq) = dp-dq) \/
    ((3 * Rabs (p - q) < p + q) -> round_flt (dp - dq) <> dp-dq)).
case (Req_dec (round_flt (dp - dq)) (dp-dq)); intros G1;
  case (Rlt_or_le (3 * Rabs (p - q)) (p+q)); intros G2.
left; now split.
right; intros G3; contradict G2; apply Rlt_not_le; easy.
now right.
now right.
destruct G as [(G1,G2)|G].
unfold d; rewrite Rle_bool_false...
rewrite G2.
replace (round_flt (p - q)) with (p-q).
replace ((p - q + (dp - dq))) with (b * b - a * c).
2: unfold dp, p, dq, q; ring.
apply Rle_trans with (1:=error_le_half_ulp_round _ _ _ _).
apply Rmult_le_compat_r.
apply ulp_ge_0.
lra.
apply sym_eq, round_generic...
apply sterbenz...
apply generic_format_round...
apply generic_format_round...
split.
apply Rmult_le_reg_l with 4%R.
lra.
apply Rplus_le_reg_l with (q-3*p).
apply Rle_trans with (p+q);[idtac|right; ring].
apply Rlt_le, Rle_lt_trans with (2:=G1).
rewrite <- Rabs_Ropp.
apply Rle_trans with (3*(-(p-q))).
right; field.
apply Rmult_le_compat_l; [lra|apply RRle_abs].
apply Rmult_le_reg_l with 2%R.
lra.
apply Rplus_le_reg_l with (p-3*q).
apply Rle_trans with (p+q);[idtac|right; ring].
apply Rlt_le, Rle_lt_trans with (2:=G1).
apply Rle_trans with (3*(p-q)).
right; field.
apply Rmult_le_compat_l; [lra|apply RRle_abs].
assert (precisionNotZero : (1 < prec)%Z) by lia.

destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero b)
  as (fb,(Hfb,Hfb')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero c)
  as (fc,(Hfc,Hfc')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.

destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (b*b))  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (a*c))  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero dp)
  as (fdp,(Hfdp,Hfdp')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
apply format_dp.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero dq)
  as (fdq,(Hfdq,Hfdq')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
apply format_dq.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (p-q))  as (ft,(Hft, (Hft',Hft''))).
rewrite make_bound_Emin in Hft''; try assumption.
replace (--emin)%Z with emin in Hft'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (dp-dq))  as (fs,(Hfs, (Hfs',Hfs''))).
rewrite make_bound_Emin in Hfs''; try assumption.
replace (--emin)%Z with emin in Hfs'' by lia.
destruct (format_is_pff_format_can radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero d)
  as (fd,(Hfd,Hfd')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
apply format_d_discri1.
assert (K: (1 < Z.abs_nat prec)%nat).
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.

rewrite <- Hfd, <- Hfb, <- Hfa, <- Hfc.
apply Rle_trans with (2 * Fulp (make_bound radix2 prec emin) 2 (Z.abs_nat prec) fd)%R.
apply discri with fp fq ft fdp fdq fs; try assumption.
apply make_bound_p; lia.
apply FcanonicBound with radix2; try assumption.
apply FcanonicBound with radix2; try assumption.
apply FcanonicBound with radix2; try assumption.
apply FcanonicBound with radix2; try assumption.

rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
assert (emin < Pff.Fexp fd)%Z; try lia.
apply FloatFexp_gt with radix2 (make_bound radix2 prec emin) prec; try assumption.
apply make_bound_p; lia.
apply FcanonicBound with radix2; try assumption.
rewrite Hfd.
apply U4_discri1; assumption.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
assert (emin < Pff.Fexp ft)%Z; try lia.
apply FloatFexp_gt with radix2 (make_bound radix2 prec emin) prec; try assumption.
apply make_bound_p; lia.
now apply FcanonicBound with radix2.
rewrite Hft''.
apply Rle_trans with (2:=U3_discri1 Zbb Zac Zpq).
apply bpow_le; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite inj_abs;[idtac|lia].
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfb.
apply Rle_trans with (2:=U1 Zbb).
rewrite <- bpow_powerRZ.
apply bpow_le; simpl (radix_val radix2); lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite inj_abs;[idtac|lia].
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfa, Hfc.
apply Rle_trans with (2:=U2 Zac).
rewrite <- bpow_powerRZ.
apply bpow_le; simpl (radix_val radix2); lia.
replace 2%Z with (radix_val radix2) by easy.
right; apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Hfp''.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=U1 Zbb).
apply bpow_le; lia.
replace 2%Z with (radix_val radix2) by easy.
right; apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Hfq''.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
lia.
apply Rle_trans with (2:=U2 Zac).
apply bpow_le; lia.
intros C; right.
replace 2%Z with (radix_val radix2) by easy.
apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Hfs''.
apply U5_discri1; try assumption.
apply G.
unfold p, q; rewrite <- Hfp'', <- Hfq''; easy.
replace 2%Z with (radix_val radix2) by easy.
apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite Hfd.
apply Rle_trans with (2:=U4_discri1 Zbb Zac Zpq).
apply bpow_le; lia.

rewrite <- Hfb in Hfp'; assumption.
rewrite <- Hfa, <- Hfc in Hfq'; assumption.
intros Y.
assert (Y' : d = round_flt (p - q)).
unfold d; rewrite Rle_bool_true; try easy.
unfold p; rewrite <- Hfp''; unfold q; rewrite <- Hfq''.
easy.
apply EvenClosestCompatible with (p-q)
   (RND_EvenClosest (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (p-q)); try easy.
apply make_bound_p; lia.
apply RND_EvenClosest_correct; try easy.
apply make_bound_p; lia.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfd, Y'.
rewrite pff_round_NE_is_round; try easy.
2: apply make_bound_p; lia.
2: apply FcanonicBound with radix2; try assumption.
rewrite make_bound_Emin; try assumption.
now replace (--emin)%Z with emin by lia.
intros _; generalize Hft'.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
intros _; replace 2%Z with (radix_val radix2) by easy.
rewrite Hfdp; unfold dp; now rewrite <- Hfb, Hfp''.
intros _; replace 2%Z with (radix_val radix2) by easy.
rewrite Hfdq; unfold dq; now rewrite <- Hfa, <- Hfc, Hfq''.
intros _; generalize Hfs'.
now rewrite <- Hfdp, <- Hfdq.
intros Y.
assert (Y' : d = round_flt (round_flt (p - q) + round_flt (dp - dq))).
unfold d; rewrite Rle_bool_false; try easy.
unfold p; rewrite <- Hfp''; unfold q; rewrite <- Hfq''.
easy.
apply EvenClosestCompatible with (FtoR radix2 ft+FtoR radix2 fs)
   (RND_EvenClosest (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (FtoR radix2 ft+FtoR radix2 fs)); try easy.
apply make_bound_p; lia.
apply RND_EvenClosest_correct; try easy.
apply make_bound_p; lia.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfd, Y'.
rewrite pff_round_NE_is_round; try easy.
2: apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
now rewrite Hfs'', Hft''.
apply FcanonicBound with radix2; try assumption.
right; f_equal.
replace 2%Z with (radix_val radix2) by easy.
rewrite Fulp_ulp; try easy.
2: apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
now replace (--emin)%Z with emin by lia.
apply FcanonicBound with radix2; try assumption.
Qed.

End Discri1.

Section Discri2.
Variable emin prec : Z.
Hypothesis precisionGt : (4 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation bpow e := (bpow radix2 e).

Variable a b c:R.
Hypothesis Fa: format a.
Hypothesis Fb: format b.
Hypothesis Fc: format c.

Let p:=round_flt (b*b).
Let q:=round_flt (a*c).
Let dp:= b*b-p.
Let dq:= a*c-q.
Let d:= if (Rle_bool (round_flt (p+q)) (round_flt (3*Rabs (round_flt (p-q)))))
            then round_flt (p-q)
            else round_flt (round_flt (p-q) + round_flt(dp-dq)).

Hypothesis U1 : b * b <> 0 ->
    bpow (emin + 3 * prec) <= Rabs (b * b).
Hypothesis U2 : a * c <> 0 ->
    bpow (emin + 3 * prec) <= Rabs (a * c).
Hypothesis Zd : d <> 0.

Lemma format_d_discri2 : format d.
Proof using dp dq prec_gt_0_.
Proof with auto with typeclass_instances.
unfold d; case (Rle_bool _ _).
apply generic_format_round...
apply generic_format_round...
Qed.

Theorem discri_fp_test :
 Rabs (d-(b*b-a*c)) <= 2* ulp_flt d.
Proof using Fa Fb Fc U1 U2 Zd emin_neg prec_gt_0_ precisionGt.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by lia.

destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero b)
  as (fb,(Hfb,Hfb')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero c)
  as (fc,(Hfc,Hfc')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia; assumption.

destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (b*b))  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (a*c))  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by lia.
destruct (format_is_pff_format_can radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero dp)
  as (fdp,(Hfdp,Hfdp')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
now apply format_dp.
destruct (format_is_pff_format_can radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero dq)
  as (fdq,(Hfdq,Hfdq')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
now apply format_dq.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (p-q))  as (ft,(Hft, (Hft',Hft''))).
rewrite make_bound_Emin in Hft''; try assumption.
replace (--emin)%Z with emin in Hft'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (dp-dq))  as (fs,(Hfs, (Hfs',Hfs''))).
rewrite make_bound_Emin in Hfs''; try assumption.
replace (--emin)%Z with emin in Hfs'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (p+q))  as (fv,(Hfv, (Hfv',Hfv''))).
rewrite make_bound_Emin in Hfv''; try assumption.
replace (--emin)%Z with emin in Hfv'' by lia.
destruct (round_NE_is_pff_round radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero
  (3*Rabs (FtoR radix2 ft)))  as (fu,(Hfu, (Hfu',Hfu''))).
rewrite make_bound_Emin in Hfu''; try assumption.
replace (--emin)%Z with emin in Hfu'' by lia.
destruct (format_is_pff_format_can radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero d)
  as (fd,(Hfd,Hfd')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
apply format_d_discri2.
assert (K: (1 < Z.abs_nat prec)%nat).
replace 1%nat with (Z.abs_nat 1) by easy.
apply Zabs_nat_lt; lia.

rewrite <- Hfd, <- Hfb, <- Hfa, <- Hfc.
apply Rle_trans with (2 * Fulp (make_bound radix2 prec emin) 2 (Z.abs_nat prec) fd)%R.
cut ((FtoR radix2 fd = 0 \/ (Rabs  (FtoR radix2 fd -
   (FtoR radix2 fb * FtoR radix2 fb -
    FtoR radix2 fa * FtoR radix2 fc)) <=
    2 * Fulp (make_bound radix2 prec emin) 2 (Z.abs_nat prec) fd))).
intros M; case M; try easy.
intros KK; contradict Zd; rewrite <- Hfd; easy.
apply discri16 with fp fq ft fdp fdq fs fu fv; try assumption.
apply make_bound_p; lia.
change 4%nat with (Z.abs_nat 4).
apply Zabs_nat_le; lia.
intros _; apply FcanonicBound with radix2; try assumption.
intros _; apply FcanonicBound with radix2; try assumption.

unfold radix2 in Hfb; simpl in Hfb; rewrite Hfb.
case (Req_dec b 0); intros Zb.
now left.
right; apply Rle_trans with (bpow (emin + 3 * prec-1)).
rewrite bpow_powerRZ; right; f_equal.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite inj_abs; lia.
apply Rle_trans with (bpow (emin + 3 * prec)).
apply bpow_le; lia.
apply U1; auto with real.
unfold radix2 in Hfa, Hfc; simpl in Hfa, Hfc; rewrite Hfa, Hfc.
case (Req_dec (a*c) 0); intros Zac.
now left.
right; apply Rle_trans with (bpow (emin + 3 * prec - 1)).
rewrite bpow_powerRZ; right; f_equal.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
rewrite inj_abs; lia.
apply Rle_trans with (2:=U2 Zac); auto with real.
apply bpow_le; lia.

rewrite <- Hfb in Hfp'; assumption.
rewrite <- Hfa, <- Hfc in Hfq'; assumption.
generalize Hft'.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
generalize Hfv'.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
intros Y.
assert (Y' : d = round_flt (p - q)).
unfold d; rewrite Rle_bool_true; try easy.
now rewrite <- Hfv'', <- Hft'', <- Hfu''.
apply EvenClosestCompatible with (p-q)
   (RND_EvenClosest (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (p-q)); try easy.
apply make_bound_p; lia.
apply RND_EvenClosest_correct; try easy.
apply make_bound_p; lia.
unfold p; rewrite <- Hfp''; unfold q; now rewrite <- Hfq''.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfd, Y'.
rewrite pff_round_NE_is_round; try easy.
2: apply make_bound_p; lia.
2: apply FcanonicBound with radix2; try assumption.
rewrite make_bound_Emin; try assumption.
now replace (--emin)%Z with emin by lia.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfdp; unfold dp; now rewrite <- Hfb, Hfp''.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfdq; unfold dq; now rewrite <- Hfa, <- Hfc, Hfq''.
intros _; generalize Hfs'.
now rewrite <- Hfdp, <- Hfdq.
intros Y.
assert (Y' : d = round_flt (round_flt (p - q) + round_flt (dp - dq))).
unfold d; rewrite Rle_bool_false; try easy.
now rewrite <- Hfv'', <- Hft'', <- Hfu''.
apply EvenClosestCompatible with (FtoR radix2 ft+FtoR radix2 fs)
   (RND_EvenClosest (make_bound radix2 prec emin) radix2 (Z.abs_nat prec) (FtoR radix2 ft+FtoR radix2 fs)); try easy.
apply make_bound_p; lia.
apply RND_EvenClosest_correct; try easy.
apply make_bound_p; lia.
replace 2%Z with (radix_val radix2) by easy.
rewrite Hfd, Y'.
rewrite pff_round_NE_is_round; try easy.
2: apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by lia.
now rewrite Hfs'', Hft''.
apply FcanonicBound with radix2; try assumption.
right; f_equal.
replace 2%Z with (radix_val radix2) by easy.
rewrite Fulp_ulp; try easy.
2: apply make_bound_p; lia.
rewrite make_bound_Emin; try assumption.
now replace (--emin)%Z with emin by lia.
apply FcanonicBound with radix2; try assumption.
Qed.

End Discri2.


Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Core Flocq.Calc.Operations Flocq_DOT_Prop_DOT_Relative.Flocq.AVOID_RESERVED_Prop.Relative Flocq_DOT_Prop_DOT_Sterbenz.Flocq.AVOID_RESERVED_Prop.Sterbenz Flocq_DOT_Prop_DOT_Mult_error.Flocq.AVOID_RESERVED_Prop.Mult_error.

Section Fprop_divsqrt_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.

Lemma generic_format_plus_prec :
  forall fexp, (forall e, (fexp e <= e - prec)%Z) ->
  forall x y (fx fy: float beta),
  (x = F2R fx)%R -> (y = F2R fy)%R -> (Rabs (x+y) < bpow (prec+Fexp fx))%R ->
  (Rabs (x+y) < bpow (prec+Fexp fy))%R ->
  generic_format beta fexp (x+y)%R.
Proof using .
intros fexp Hfexp x y fx fy Hx Hy H1 H2.
case (Req_dec (x+y) 0); intros H.
rewrite H; apply generic_format_0.
rewrite Hx, Hy, <- F2R_plus.
apply generic_format_F2R.
intros _.
change (F2R _) with (F2R (Fplus fx fy)).
apply Z.le_trans with (Z.min (Fexp fx) (Fexp fy)).
rewrite F2R_plus, <- Hx, <- Hy.
unfold cexp.
apply Z.le_trans with (1:=Hfexp _).
apply Zplus_le_reg_l with prec; ring_simplify.
apply mag_le_bpow with (1 := H).
now apply Z.min_case.
rewrite <- Fexp_Fplus.
apply Z.le_refl.
Qed.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (cexp beta (FLX_exp prec)).

Variable choice : Z -> bool.

Theorem div_error_FLX :
  forall rnd { Zrnd : Valid_rnd rnd } x y,
  format x -> format y ->
  format (x - round beta (FLX_exp prec) rnd (x/y) * y)%R.
Proof using prec_gt_0_.
Proof with auto with typeclass_instances.
intros rnd Zrnd x y Hx Hy.
destruct (Req_dec y 0) as [Zy|Zy].
now rewrite Zy, Rmult_0_r, Rminus_0_r.
destruct (Req_dec (round beta (FLX_exp prec) rnd (x/y)) 0) as [Hr|Hr].
rewrite Hr; ring_simplify (x-0*y)%R; assumption.
assert (Zx: x <> R0).
contradict Hr.
rewrite Hr.
unfold Rdiv.
now rewrite Rmult_0_l, round_0.
destruct (canonical_generic_format _ _ x Hx) as (fx,(Hx1,Hx2)).
destruct (canonical_generic_format _ _ y Hy) as (fy,(Hy1,Hy2)).
destruct (canonical_generic_format beta (FLX_exp prec) (round beta (FLX_exp prec) rnd (x / y))) as (fr,(Hr1,Hr2)).
apply generic_format_round...
unfold Rminus; apply generic_format_plus_prec with fx (Fopp (Fmult fr fy)); trivial.
intros e; apply Z.le_refl.
now rewrite F2R_opp, F2R_mult, <- Hr1, <- Hy1.

destruct (relative_error_FLX_ex beta prec (prec_gt_0 prec) rnd (x / y)%R) as (eps,(Heps1,Heps2)).
rewrite Heps2.
rewrite <- Rabs_Ropp.
replace (-(x + - (x / y * (1 + eps) * y)))%R with (x * eps)%R by now field.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs x * 1)%R.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
apply Rlt_le_trans with (1 := Heps1).
change 1%R with (bpow 0).
apply bpow_le.
generalize (prec_gt_0 prec).
clear ; lia.
rewrite Rmult_1_r.
rewrite Hx2, <- Hx1.
unfold cexp.
destruct (mag beta x) as (ex, Hex).
simpl.
specialize (Hex Zx).
apply Rlt_le.
apply Rlt_le_trans with (1 := proj2 Hex).
apply bpow_le.
unfold FLX_exp.
ring_simplify.
apply Z.le_refl.

replace (Fexp (Fopp (Fmult fr fy))) with (Fexp fr + Fexp fy)%Z.
2: unfold Fopp, Fmult; destruct fr; destruct fy; now simpl.
replace (x + - (round beta (FLX_exp prec) rnd (x / y) * y))%R with
  (y * (-(round beta (FLX_exp prec) rnd (x / y) - x/y)))%R.
2: field; assumption.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs y * bpow (Fexp fr))%R.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
rewrite Rabs_Ropp.
replace (bpow (Fexp fr)) with (ulp beta (FLX_exp prec) (F2R fr)).
rewrite <- Hr1.
apply error_lt_ulp_round...
apply Rmult_integral_contrapositive_currified; try apply Rinv_neq_0_compat; assumption.
rewrite ulp_neq_0.
2: now rewrite <- Hr1.
apply f_equal.
now rewrite Hr2, <- Hr1.
replace (prec+(Fexp fr+Fexp fy))%Z with ((prec+Fexp fy)+Fexp fr)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite Hy2, <- Hy1 ; unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta y - prec))%Z.
destruct (mag beta y); simpl.
left; now apply a.
Qed.

Variable Hp1 : Z.lt 1 prec.

Theorem sqrt_error_FLX_N :
  forall x, format x ->
  format (x - Rsqr (round beta (FLX_exp prec) (Znearest choice) (sqrt x)))%R.
Proof using Hp1 prec_gt_0_.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (total_order_T x 0) as [[Hxz|Hxz]|Hxz].
unfold sqrt.
destruct (Rcase_abs x).
rewrite round_0...
unfold Rsqr.
now rewrite Rmult_0_l, Rminus_0_r.
elim (Rlt_irrefl 0).
now apply Rgt_ge_trans with x.
rewrite Hxz, sqrt_0, round_0...
unfold Rsqr.
rewrite Rmult_0_l, Rminus_0_r.
apply generic_format_0.
case (Req_dec (round beta (FLX_exp prec) (Znearest choice) (sqrt x)) 0); intros Hr.
rewrite Hr; unfold Rsqr; ring_simplify (x-0*0)%R; assumption.
destruct (canonical_generic_format _ _ x Hx) as (fx,(Hx1,Hx2)).
destruct (canonical_generic_format beta (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) (sqrt x))) as (fr,(Hr1,Hr2)).
apply generic_format_round...
unfold Rminus; apply generic_format_plus_prec with fx (Fopp (Fmult fr fr)); trivial.
intros e; apply Z.le_refl.
unfold Rsqr; now rewrite F2R_opp,F2R_mult, <- Hr1.

apply Rle_lt_trans with x.
apply Rabs_minus_le.
apply Rle_0_sqr.
destruct (relative_error_N_FLX_ex beta prec (prec_gt_0 prec) choice (sqrt x)) as (eps,(Heps1,Heps2)).
rewrite Heps2.
rewrite Rsqr_mult, Rsqr_sqrt, Rmult_comm.
2: now apply Rlt_le.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rle_trans with (5²/4²)%R.
rewrite <- Rsqr_div.
apply Rsqr_le_abs_1.
apply Rle_trans with (1 := Rabs_triang _ _).
rewrite Rabs_R1.
apply Rplus_le_reg_l with (-1)%R.
replace (-1 + (1 + Rabs eps))%R with (Rabs eps) by ring.
apply Rle_trans with (1 := Heps1).
rewrite Rabs_pos_eq.
apply Rmult_le_reg_l with 2%R.
now apply IZR_lt.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
apply Rle_trans with (bpow (-1)).
apply bpow_le.
lia.
replace (2 * (-1 + 5 / 4))%R with (/2)%R by field.
apply Rinv_le.
now apply IZR_lt.
apply IZR_le.
unfold Zpower_pos.
simpl.
rewrite Zmult_1_r.
apply Zle_bool_imp_le.
apply beta.
now apply IZR_neq.
unfold Rdiv.
apply Rmult_le_pos.
now apply IZR_le.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
now apply IZR_neq.
unfold Rsqr.
replace (5 * 5 / (4 * 4))%R with (25 * /16)%R by field.
apply Rmult_le_reg_r with 16%R.
now apply IZR_lt.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now apply (IZR_le _ 32).
now apply IZR_neq.
rewrite Hx2, <- Hx1; unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta x - prec))%Z.
destruct (mag beta x); simpl.
rewrite <- (Rabs_right x).
apply a.
now apply Rgt_not_eq.
now apply Rgt_ge.

replace (Fexp (Fopp (Fmult fr fr))) with (Fexp fr + Fexp fr)%Z.
2: unfold Fopp, Fmult; destruct fr; now simpl.
rewrite Hr1.
replace (x + - Rsqr (F2R fr))%R with (-((F2R fr - sqrt x)*(F2R fr + sqrt x)))%R.
2: rewrite <- (sqrt_sqrt x) at 3; auto.
2: unfold Rsqr; ring.
rewrite Rabs_Ropp, Rabs_mult.
apply Rle_lt_trans with ((/2*bpow (Fexp fr))* Rabs (F2R fr + sqrt x))%R.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rle_trans with (/2*ulp beta  (FLX_exp prec) (F2R fr))%R.
rewrite <- Hr1.
apply error_le_half_ulp_round...
right; rewrite ulp_neq_0.
2: now rewrite <- Hr1.
apply f_equal.
rewrite Hr2, <- Hr1; trivial.
rewrite Rmult_assoc, Rmult_comm.
replace (prec+(Fexp fr+Fexp fr))%Z with (Fexp fr + (prec+Fexp fr))%Z by ring.
rewrite bpow_plus, Rmult_assoc.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
apply Rmult_lt_reg_l with (1 := Rlt_0_2).
apply Rle_lt_trans with (Rabs (F2R fr + sqrt x)).
right; field.
apply Rle_lt_trans with (1:=Rabs_triang _ _).

assert (Rabs (F2R fr) < bpow (prec + Fexp fr))%R.
rewrite Hr2.
unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta (F2R fr) - prec))%Z.
destruct (mag beta (F2R fr)); simpl.
apply a.
rewrite <- Hr1; auto.

apply Rlt_le_trans with (bpow (prec + Fexp fr)+ Rabs (sqrt x))%R.
now apply Rplus_lt_compat_r.

replace (2 * bpow (prec + Fexp fr))%R with (bpow (prec + Fexp fr) + bpow (prec + Fexp fr))%R by ring.
apply Rplus_le_compat_l.
assert (sqrt x <> 0)%R.
apply Rgt_not_eq.
now apply sqrt_lt_R0.
destruct (mag beta (sqrt x)) as (es,Es).
specialize (Es H0).
apply Rle_trans with (bpow es).
now apply Rlt_le.
apply bpow_le.
case (Zle_or_lt es (prec + Fexp fr)) ; trivial.
intros H1.
absurd (Rabs (F2R fr) < bpow (es - 1))%R.
apply Rle_not_lt.
rewrite <- Hr1.
apply abs_round_ge_generic...
apply generic_format_bpow.
unfold FLX_exp; lia.
apply Es.
apply Rlt_le_trans with (1:=H).
apply bpow_le.
lia.
now apply Rlt_le.
Qed.

Lemma sqrt_error_N_FLX_aux1 x (Fx : format x) (Px : (0 < x)%R) :
  exists (mu : R) (e : Z), (format mu /\ x = mu * bpow (2 * e) :> R
                            /\ 1 <= mu < bpow 2)%R.
Proof using .
set (e := ((mag beta x - 1) / 2)%Z).
set (mu := (x * bpow (-2 * e)%Z)%R).
assert (Hbe : (bpow (-2 * e) * bpow (2 * e) = 1)%R).
{
 now rewrite <- bpow_plus; case e; simpl; [reflexivity| |]; intro p;
    rewrite Z.pos_sub_diag.
}
assert (Fmu : format mu); [now apply mult_bpow_exact_FLX|].
exists mu, e; split; [exact Fmu|split; [|split]].
{
 set (e2 := (2 * e)%Z); simpl; unfold mu; rewrite Rmult_assoc.
  now unfold e2; rewrite Hbe, Rmult_1_r.
}
{
 apply (Rmult_le_reg_r (bpow (2 * e))).
  {
 apply bpow_gt_0.
}
  rewrite Rmult_1_l; set (e2 := (2 * e)%Z); simpl; unfold mu.
  unfold e2; rewrite Rmult_assoc, Hbe, Rmult_1_r.
  apply (Rle_trans _ (bpow (mag beta x - 1))).
  {
 now apply bpow_le; unfold e; apply Z_mult_div_ge.
}
  set (l := mag _ _); rewrite <- (Rabs_pos_eq _ (Rlt_le _ _ Px)).
  unfold l; apply bpow_mag_le.
  intro Hx; revert Px; rewrite Hx; apply Rlt_irrefl.
}
simpl; unfold mu; change (IZR _) with (bpow 2).
apply (Rmult_lt_reg_r (bpow (2 * e))); [now apply bpow_gt_0|].
rewrite Rmult_assoc, Hbe, Rmult_1_r.
apply (Rlt_le_trans _ (bpow (mag beta x))).
{
 rewrite <- (Rabs_pos_eq _ (Rlt_le _ _ Px)) at 1; apply bpow_mag_gt.
}
rewrite <- bpow_plus; apply bpow_le; unfold e; set (mxm1 := (_ - 1)%Z).
replace (_ * _)%Z with (2 * (mxm1 / 2) + mxm1 mod 2 - mxm1 mod 2)%Z by ring.
rewrite <- Z.div_mod; [|now simpl].
apply (Zplus_le_reg_r _ _ (mxm1 mod 2 - mag beta x)%Z).
unfold mxm1; destruct (Z.mod_bound_or (mag beta x - 1) 2); lia.
Qed.

Notation u_ro := (u_ro beta prec).

Lemma sqrt_error_N_FLX_aux2 x (Fx : format x) :
  (1 <= x)%R ->
  (x = 1 :> R \/ x = 1 + 2 * u_ro :> R \/ 1 + 4 * u_ro <= x)%R.
Proof using Hp1 prec_gt_0_.
intro HxGe1.
assert (Pu_ro : (0 <= u_ro)%R); [apply Rmult_le_pos; [lra|apply bpow_ge_0]|].
destruct (Rle_or_lt x 1) as [HxLe1|HxGt1]; [now left; apply Rle_antisym|right].
assert (F1 : format 1); [now apply generic_format_FLX_1|].
assert (H2eps : (2 * u_ro = bpow (-prec + 1))%R).
{
 unfold u_ro; rewrite bpow_plus; field.
}
assert (HmuGe1p2eps : (1 + 2 * u_ro <= x)%R).
{
 rewrite H2eps, <- succ_FLX_1.
  now apply succ_le_lt; [now apply FLX_exp_valid| | |].
}
destruct (Rle_or_lt x (1 + 2 * u_ro)) as [HxLe1p2eps|HxGt1p2eps];
  [now left; apply Rle_antisym|right].
assert (Hulp1p2eps : (ulp beta (FLX_exp prec) (1 + 2 * u_ro) = 2 * u_ro)%R).
{
 destruct (ulp_succ_pos _ _ _ F1 Rlt_0_1) as [Hsucc|Hsucc].
  {
 now rewrite H2eps, <- succ_FLX_1, <- ulp_FLX_1.
}
  exfalso; revert Hsucc; apply Rlt_not_eq.
  rewrite succ_FLX_1, mag_1, bpow_1, <- H2eps; simpl.
  apply (Rlt_le_trans _ 2); [apply Rplus_lt_compat_l|].
  {
 unfold u_ro; rewrite <-Rmult_assoc, Rinv_r, Rmult_1_l; [|lra].
    change R1 with (bpow 0); apply bpow_lt; lia.
}
  apply IZR_le, Zle_bool_imp_le, radix_prop.
}
assert (Hsucc1p2eps :
          (succ beta (FLX_exp prec) (1 + 2 * u_ro) = 1 + 4 * u_ro)%R).
{
 unfold succ; rewrite Rle_bool_true; [rewrite Hulp1p2eps; ring|].
  apply Rplus_le_le_0_compat; lra.
}
rewrite <- Hsucc1p2eps.
apply succ_le_lt; [now apply FLX_exp_valid| |exact Fx|now simpl].
rewrite H2eps, <- succ_FLX_1.
now apply generic_format_succ; [apply FLX_exp_valid|].
Qed.

Lemma sqrt_error_N_FLX_aux3 :
  (u_ro / sqrt (1 + 4 * u_ro) <= 1 - 1 / sqrt (1 + 2 * u_ro))%R.
Proof using Hp1 prec_gt_0_.
assert (Pu_ro : (0 <= u_ro)%R); [apply Rmult_le_pos; [lra|apply bpow_ge_0]|].
unfold Rdiv; apply (Rplus_le_reg_r (/ sqrt (1 + 2 * u_ro))); ring_simplify.
apply (Rmult_le_reg_r (sqrt (1 + 4 * u_ro) * sqrt (1 + 2 * u_ro))).
{
 apply Rmult_lt_0_compat; apply sqrt_lt_R0; lra.
}
field_simplify; [|split; apply Rgt_not_eq, Rlt_gt, sqrt_lt_R0; lra].
try unfold Rdiv; rewrite ?Rinv_1, ?Rmult_1_r.
apply Rsqr_incr_0_var; [|now apply Rmult_le_pos; apply sqrt_pos].
rewrite <-sqrt_mult; [|lra|lra].
rewrite Rsqr_sqrt; [|apply Rmult_le_pos; lra].
unfold Rsqr; ring_simplify; unfold pow; rewrite !Rmult_1_r.
rewrite !sqrt_def; [|lra|lra].
apply (Rplus_le_reg_r (-u_ro * u_ro - 1 -4 * u_ro - 2 * u_ro ^ 3)).
ring_simplify; apply Rsqr_incr_0_var.
{
 unfold Rsqr; ring_simplify.
  unfold pow; rewrite !Rmult_1_r, !sqrt_def; [|lra|lra].
  apply (Rplus_le_reg_r (-32 * u_ro ^ 4 - 24 * u_ro ^ 3 - 4 * u_ro ^ 2)).
  ring_simplify.
  replace (_ + _)%R
    with (((4 * u_ro ^ 2 - 28 * u_ro + 9) * u_ro + 4) * u_ro ^ 3)%R by ring.
  apply Rmult_le_pos; [|now apply pow_le].
  assert (Heps_le_half : (u_ro <= 1 / 2)%R).
  {
 unfold u_ro, Rdiv; rewrite Rmult_comm; apply Rmult_le_compat_r; [lra|].
    change 1%R with (bpow 0); apply bpow_le; lia.
}
  apply (Rle_trans _ (-8 * u_ro + 4)); [lra|].
  apply Rplus_le_compat_r, Rmult_le_compat_r; [apply Pu_ro|].
  now assert (H : (0 <= u_ro ^ 2)%R); [apply pow2_ge_0|lra].
}
assert (H : (u_ro ^ 3 <= u_ro ^ 2)%R).
{
 unfold pow; rewrite <-!Rmult_assoc, Rmult_1_r.
  apply Rmult_le_compat_l; [now apply Rmult_le_pos; apply Pu_ro|].
  now apply Rlt_le, u_ro_lt_1.
}
now assert (H' : (0 <= u_ro ^ 2)%R); [apply pow2_ge_0|lra].
Qed.

Lemma om1ds1p2u_ro_pos : (0 <= 1 - 1 / sqrt (1 + 2 * u_ro))%R.
Proof using .
unfold Rdiv; rewrite Rmult_1_l, <-Rinv_1 at 1.
apply Rle_0_minus, Rinv_le; [lra|].
rewrite <- sqrt_1 at 1; apply sqrt_le_1_alt.
assert (H := u_ro_pos beta prec); lra.
Qed.

Lemma om1ds1p2u_ro_le_u_rod1pu_ro :
  (1 - 1 / sqrt (1 + 2 * u_ro) <= u_ro / (1 + u_ro))%R.
Proof using .
assert (Pu_ro := u_ro_pos beta prec).
apply (Rmult_le_reg_r (sqrt (1 + 2 * u_ro) * (1 + u_ro))).
{
 apply Rmult_lt_0_compat; [apply sqrt_lt_R0|]; lra.
}
field_simplify; [|lra|intro H; apply sqrt_eq_0 in H; lra].
try unfold Rdiv; unfold Rminus; rewrite ?Rinv_1, ?Rmult_1_r, !Rplus_assoc.
rewrite <-(Rplus_0_r (sqrt _ * _)) at 2; apply Rplus_le_compat_l.
apply (Rplus_le_reg_r (1 + u_ro)); ring_simplify.
rewrite <-(sqrt_square (_ + 1)); [|lra]; apply sqrt_le_1_alt.
assert (H : (0 <= u_ro * u_ro)%R); [apply Rmult_le_pos|]; lra.
Qed.

Lemma s1p2u_rom1_pos : (0 <= sqrt (1 + 2 * u_ro) - 1)%R.
Proof using .
apply (Rplus_le_reg_r 1); ring_simplify.
rewrite <-sqrt_1 at 1; apply sqrt_le_1_alt.
assert (H := u_ro_pos beta prec); lra.
Qed.

Theorem sqrt_error_N_FLX x (Fx : format x) :
  (Rabs (round beta (FLX_exp prec) (Znearest choice) (sqrt x) - sqrt x)
   <= (1 - 1 / sqrt (1 + 2 * u_ro)) * Rabs (sqrt x))%R.
Proof using Hp1 prec_gt_0_.
assert (Peps := u_ro_pos beta prec).
assert (Peps' : (0 < u_ro)%R).
{
 unfold u_ro; apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
}
assert (Pb := om1ds1p2u_ro_pos).
assert (Pb' := s1p2u_rom1_pos).
destruct (Rle_or_lt x 0) as [Nx|Px].
{
 rewrite (sqrt_neg _ Nx), round_0, Rabs_R0, Rmult_0_r; [|apply valid_rnd_N].
  now unfold Rminus; rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0; right.
}
destruct (sqrt_error_N_FLX_aux1 _ Fx Px)
  as (mu, (e, (Fmu, (Hmu, (HmuGe1, HmuLtsqradix))))).
pose (t := sqrt x).
set (rt := round _ _ _ _).
assert (Ht : (t = sqrt mu * bpow e)%R).
{
 unfold t; rewrite Hmu, sqrt_mult_alt; [|now apply (Rle_trans _ _ _ Rle_0_1)].
  now rewrite sqrt_bpow.
}
destruct (sqrt_error_N_FLX_aux2 _ Fmu HmuGe1) as [Hmu'|[Hmu'|Hmu']].
{
 unfold rt; fold t; rewrite Ht, Hmu', sqrt_1, Rmult_1_l.
  rewrite round_generic; [|now apply valid_rnd_N|].
  {
 rewrite Rminus_diag_eq, Rabs_R0; [|now simpl].
    now apply Rmult_le_pos; [|apply Rabs_pos].
}
  apply generic_format_bpow'; [now apply FLX_exp_valid|].
  unfold FLX_exp; lia.
}
{
 assert (Hsqrtmu : (1 <= sqrt mu < 1 + u_ro)%R); [rewrite Hmu'; split|].
  {
 rewrite <- sqrt_1 at 1; apply sqrt_le_1_alt; lra.
}
  {
 rewrite <- sqrt_square; [|lra]; apply sqrt_lt_1_alt; split; [lra|].
    ring_simplify; assert (0 < u_ro ^ 2)%R; [apply pow_lt|]; lra.
}
  assert (Fbpowe : generic_format beta (FLX_exp prec) (bpow e)).
  {
 apply generic_format_bpow; unfold FLX_exp; lia.
}
  assert (Hrt : rt = bpow e :> R).
  {
 unfold rt; fold t; rewrite Ht; simpl; apply Rle_antisym.
    {
 apply round_N_le_midp; [now apply FLX_exp_valid|exact Fbpowe|].
      apply (Rlt_le_trans _ ((1 + u_ro) * bpow e)).
      {
 now apply Rmult_lt_compat_r; [apply bpow_gt_0|].
}
      unfold succ; rewrite Rle_bool_true; [|now apply bpow_ge_0].
      rewrite ulp_bpow; unfold FLX_exp.
      unfold Z.sub, u_ro; rewrite !bpow_plus; right; field.
}
    apply round_ge_generic;
      [now apply FLX_exp_valid|now apply valid_rnd_N|exact Fbpowe|].
    rewrite <- (Rmult_1_l (bpow _)) at 1.
    now apply Rmult_le_compat_r; [apply bpow_ge_0|].
}
  fold t; rewrite Hrt, Ht, Hmu', <-(Rabs_pos_eq _ Pb), <-Rabs_mult.
  rewrite Rabs_minus_sym; right; f_equal; field; lra.
}
assert (Hsqrtmu : (1 + u_ro < sqrt mu)%R).
{
 apply (Rlt_le_trans _ (sqrt (1 + 4 * u_ro))); [|now apply sqrt_le_1_alt].
  assert (P1peps : (0 <= 1 + u_ro)%R)
    by now apply Rplus_le_le_0_compat; [lra|apply Peps].
  rewrite <- (sqrt_square (1 + u_ro)); [|lra].
  apply sqrt_lt_1_alt; split; [now apply Rmult_le_pos|].
  apply (Rplus_lt_reg_r (-1 - 2 * u_ro)); ring_simplify; simpl.
  rewrite Rmult_1_r; apply Rmult_lt_compat_r; [apply Peps'|].
  now apply (Rlt_le_trans _ 1); [apply u_ro_lt_1|lra].
}
assert (Hulpt : (ulp beta (FLX_exp prec) t = 2 * u_ro * bpow e)%R).
{
 unfold ulp; rewrite Req_bool_false; [|apply Rgt_not_eq, Rlt_gt].
  {
 unfold u_ro; rewrite <-Rmult_assoc, Rinv_r, Rmult_1_l, <-bpow_plus; [|lra].
    f_equal; unfold cexp, FLX_exp.
    assert (Hmagt : (mag beta t = 1 + e :> Z)%Z).
    {
 apply mag_unique.
      unfold t; rewrite (Rabs_pos_eq _ (Rlt_le _ _ (sqrt_lt_R0 _ Px))).
      fold t; split.
      {
 rewrite Ht; replace (_ - _)%Z with e by ring.
        rewrite <- (Rmult_1_l (bpow _)) at 1; apply Rmult_le_compat_r.
        {
 apply bpow_ge_0.
}
        now rewrite <- sqrt_1; apply sqrt_le_1_alt.
}
      rewrite bpow_plus, bpow_1, Ht; simpl.
      apply Rmult_lt_compat_r; [now apply bpow_gt_0|].
      rewrite <- sqrt_square.
      {
 apply sqrt_lt_1_alt; split; [lra|].
        apply (Rlt_le_trans _ _ _ HmuLtsqradix); right.
        now unfold bpow, Z.pow_pos; simpl; rewrite Zmult_1_r, mult_IZR.
}
      apply IZR_le, (Z.le_trans _ 2), Zle_bool_imp_le, radix_prop; lia.
}
    rewrite Hmagt; ring.
}
  rewrite Ht; apply Rmult_lt_0_compat; [|now apply bpow_gt_0].
  now apply (Rlt_le_trans _ 1); [lra|rewrite <- sqrt_1; apply sqrt_le_1_alt].
}
assert (Pt : (0 < t)%R).
{
 rewrite Ht; apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
}
assert (H : (Rabs ((rt - sqrt x) / sqrt x)
             <= 1 - 1 / sqrt (1 + 2 * u_ro))%R).
{
 unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/ _));
    [|now left; apply Rinv_0_lt_compat].
  apply (Rle_trans _ ((u_ro * bpow e) / t)).
  {
 unfold Rdiv; apply Rmult_le_compat_r; [now left; apply Rinv_0_lt_compat|].
    apply (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _)).
    fold t; rewrite Hulpt; right; field.
}
  apply (Rle_trans _ (u_ro / sqrt (1 + 4 * u_ro))).
  {
 apply (Rle_trans _ (u_ro * bpow e / (sqrt (1 + 4 * u_ro) * bpow e))).
    {
 unfold Rdiv; apply Rmult_le_compat_l;
        [now apply Rmult_le_pos; [apply Peps|apply bpow_ge_0]|].
      apply Rinv_le.
      {
 apply Rmult_lt_0_compat; [apply sqrt_lt_R0; lra|apply bpow_gt_0].
}
      now rewrite Ht; apply Rmult_le_compat_r;
        [apply bpow_ge_0|apply sqrt_le_1_alt].
}
    right; field; split; apply Rgt_not_eq, Rlt_gt;
      [apply sqrt_lt_R0; lra|apply bpow_gt_0].
}
  apply sqrt_error_N_FLX_aux3.
}
revert H; unfold Rdiv; rewrite Rabs_mult, Rabs_Rinv; [|fold t; lra]; intro H.
apply (Rmult_le_reg_r (/ Rabs (sqrt x)));
  [apply Rinv_0_lt_compat, Rabs_pos_lt; fold t; lra|].
apply (Rle_trans _ _ _ H); right; field; split; [apply Rabs_no_R0;fold t|]; lra.
Qed.

Theorem sqrt_error_N_FLX_ex x (Fx : format x) :
  exists eps,
  (Rabs eps <= 1 - 1 / sqrt (1 + 2 * u_ro))%R /\
  round beta (FLX_exp prec) (Znearest choice) (sqrt x)
  = (sqrt x * (1 + eps))%R.
Proof using Hp1 prec_gt_0_.
now apply relative_error_le_conversion;
  [apply valid_rnd_N|apply om1ds1p2u_ro_pos|apply sqrt_error_N_FLX].
Qed.

Lemma sqrt_error_N_round_ex_derive :
  forall x rx,
  (exists eps,
   (Rabs eps <= 1 - 1 / sqrt (1 + 2 * u_ro))%R /\ rx = (x * (1 + eps))%R) ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\ x = (rx * (1 + eps))%R.
Proof using prec_gt_0_.
intros x rx (d, (Bd, Hd)).
assert (H := Rabs_le_inv _ _ Bd).
assert (H' := om1ds1p2u_ro_le_u_rod1pu_ro).
assert (H'' := u_rod1pu_ro_le_u_ro beta prec).
assert (H''' := u_ro_lt_1 beta prec prec_gt_0_).
assert (Hpos := s1p2u_rom1_pos).
destruct (Req_dec rx 0) as [Zfx|Nzfx].
{
 exists 0%R; split; [now rewrite Rabs_R0|].
  rewrite Rplus_0_r, Rmult_1_r, Zfx; rewrite Zfx in Hd.
  destruct (Rmult_integral _ _ (sym_eq Hd)); lra.
}
destruct (Req_dec x 0) as [Zx|Nzx].
{
 now exfalso; revert Hd; rewrite Zx; rewrite Rmult_0_l.
}
set (d' := ((x - rx) / rx)%R).
assert (Hd' : (Rabs d' <= sqrt (1 + 2 * u_ro) - 1)%R).
{
 unfold d'; rewrite Hd.
  replace (_ / _)%R with (- d / (1 + d))%R; [|now field; split; lra].
  unfold Rdiv; rewrite Rabs_mult, Rabs_Ropp.
  rewrite (Rabs_pos_eq (/ _)); [|apply Rlt_le, Rinv_0_lt_compat; lra].
  apply (Rmult_le_reg_r (1 + d)); [lra|].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [|lra].
  apply (Rle_trans _ _ _ Bd).
  apply (Rle_trans _ ((sqrt (1 + 2 * u_ro) - 1) * (1/sqrt (1 + 2 * u_ro))));
    [right; field|apply Rmult_le_compat_l]; lra.
}
now exists d'; split; [exact Hd'|]; unfold d'; field.
Qed.

Theorem sqrt_error_N_FLX_round_ex :
  forall x,
  format x ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\
  sqrt x = (round beta (FLX_exp prec) (Znearest choice) (sqrt x) * (1 + eps))%R.
Proof using Hp1 prec_gt_0_.
now intros x Fx; apply sqrt_error_N_round_ex_derive, sqrt_error_N_FLX_ex.
Qed.

Variable emin : Z.
Hypothesis Hemin : (emin <= 2 * (1 - prec))%Z.

Theorem sqrt_error_N_FLT_ex :
  forall x,
  generic_format beta (FLT_exp emin prec) x ->
  exists eps,
  (Rabs eps <= 1 - 1 / sqrt (1 + 2 * u_ro))%R /\
  round beta (FLT_exp emin prec) (Znearest choice) (sqrt x)
  = (sqrt x * (1 + eps))%R.
Proof using Hemin Hp1 prec_gt_0_.
intros x Fx.
assert (Heps := u_ro_pos).
assert (Pb := om1ds1p2u_ro_pos).
destruct (Rle_or_lt x 0) as [Nx|Px].
{
 exists 0%R; split; [now rewrite Rabs_R0|].
  now rewrite (sqrt_neg x Nx), round_0, Rmult_0_l; [|apply valid_rnd_N].
}
assert (Fx' := generic_format_FLX_FLT _ _ _ _ Fx).
destruct (sqrt_error_N_FLX_ex _ Fx') as (d, (Bd, Hd)).
exists d; split; [exact Bd|]; rewrite <-Hd; apply round_FLT_FLX.
apply (Rle_trans _ (bpow (emin / 2)%Z)).
{
 apply bpow_le, Z.div_le_lower_bound; lia.
}
apply (Rle_trans _ _ _ (sqrt_bpow_ge _ _)).
rewrite Rabs_pos_eq; [|now apply sqrt_pos]; apply sqrt_le_1_alt.
revert Fx; apply generic_format_ge_bpow; [|exact Px].
intro e; unfold FLT_exp; apply Z.le_max_r.
Qed.

Theorem sqrt_error_N_FLT_round_ex :
  forall x,
  generic_format beta (FLT_exp emin prec) x ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\
  sqrt x
  = (round beta (FLT_exp emin prec) (Znearest choice) (sqrt x) * (1 + eps))%R.
Proof using Hemin Hp1 prec_gt_0_.
now intros x Fx; apply sqrt_error_N_round_ex_derive, sqrt_error_N_FLT_ex.
Qed.

End Fprop_divsqrt_error.

Section format_REM_aux.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Notation format := (generic_format beta fexp).

Lemma format_REM_aux:
  forall x y : R,
  format x -> format y -> (0 <= x)%R -> (0 < y)%R ->
  ((0 < x/y < /2)%R -> rnd (x/y) = 0%Z) ->
  format (x - IZR (rnd (x/y))*y).
Proof using monotone_exp valid_exp valid_rnd.
Proof with auto with typeclass_instances.
intros x y Fx Fy Hx Hy rnd_small.
pose (n:=rnd (x / y)).
assert (Hn:(IZR n = round beta (FIX_exp 0) rnd (x/y))%R).
unfold round, FIX_exp, cexp, scaled_mantissa, F2R; simpl.
now rewrite 2!Rmult_1_r.
assert (H:(0 <= n)%Z).
apply le_IZR; rewrite Hn; simpl.
apply Rle_trans with (round beta (FIX_exp 0) rnd 0).
right; apply sym_eq, round_0...
apply round_le...
apply Fourier_util.Rle_mult_inv_pos; assumption.
case (Zle_lt_or_eq 0 n); try exact H.
clear H; intros H.
case (Zle_lt_or_eq 1 n).
lia.
clear H; intros H.
set (ex := cexp beta fexp x).
set (ey := cexp beta fexp y).
set (mx := Ztrunc (scaled_mantissa beta fexp x)).
set (my := Ztrunc (scaled_mantissa beta fexp y)).
case (Zle_or_lt ey ex); intros Hexy.

assert (H0:(x-IZR n *y = F2R (Float beta (mx*beta^(ex-ey) - n*my) ey))%R).
unfold Rminus; rewrite Rplus_comm.
replace (IZR n) with (F2R (Float beta n 0)).
rewrite Fx, Fy.
fold mx my ex ey.
rewrite <- F2R_mult.
rewrite <- F2R_opp.
rewrite <- F2R_plus.
unfold Fplus.
simpl.
rewrite Zle_imp_le_bool with (1 := Hexy).
f_equal; f_equal; ring.
unfold F2R; simpl; ring.
fold n; rewrite H0.
apply generic_format_F2R.
rewrite <- H0; intros H3.
apply monotone_exp.
apply mag_le_abs.
rewrite H0; apply F2R_neq_0; easy.
apply Rmult_le_reg_l with (/Rabs y)%R.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt.
now apply Rgt_not_eq.
rewrite Rinv_l.
2: apply Rgt_not_eq, Rabs_pos_lt.
2: now apply Rgt_not_eq.
rewrite <- Rabs_Rinv.
2: now apply Rgt_not_eq.
rewrite <- Rabs_mult.
replace (/y * (x - IZR n *y))%R with (-(IZR n - x/y))%R.
rewrite Rabs_Ropp.
rewrite Hn.
apply Rle_trans with (1:= error_le_ulp beta (FIX_exp 0) _ _).
rewrite ulp_FIX.
simpl; apply Rle_refl.
field.
now apply Rgt_not_eq.

absurd (1 < n)%Z; try easy.
apply Zle_not_lt.
apply le_IZR; simpl; rewrite Hn.
apply round_le_generic...
apply generic_format_FIX.
exists (Float beta 1 0); try easy.
unfold F2R; simpl; ring.
apply Rmult_le_reg_r with y; try easy.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l, Rmult_1_r, Rmult_1_l.
2: now apply Rgt_not_eq.
assert (mag beta x < mag beta y)%Z.
case (Zle_or_lt (mag beta y) (mag beta x)); try easy.
intros J; apply monotone_exp in J; clear -J Hexy.
unfold ex, ey, cexp in Hexy; lia.
left; apply lt_mag with beta; easy.

intros Hn'; fold n; rewrite <- Hn'.
rewrite Rmult_1_l.
case Hx; intros Hx'.
assert (J:(0 < x/y)%R).
apply Fourier_util.Rlt_mult_inv_pos; assumption.
apply sterbenz...
assert (H0:(Rabs (1  - x/y) < 1)%R).
rewrite Hn', Hn.
apply Rlt_le_trans with (ulp beta (FIX_exp 0) (round beta (FIX_exp 0) rnd (x / y)))%R.
apply error_lt_ulp_round...
now apply Rgt_not_eq.
rewrite ulp_FIX.
rewrite <- Hn, <- Hn'.
apply Rle_refl.
apply Rabs_lt_inv in H0.
split; apply Rmult_le_reg_l with (/y)%R; try now apply Rinv_0_lt_compat.
unfold Rdiv; rewrite <- Rmult_assoc.
rewrite Rinv_l.
2: now apply Rgt_not_eq.
rewrite Rmult_1_l, Rmult_comm; fold (x/y)%R.
case (Rle_or_lt (/2) (x/y)); try easy.
intros K.
elim Zlt_not_le with (1 := H).
apply Zeq_le.
apply rnd_small.
now split.
apply Ropp_le_cancel; apply Rplus_le_reg_l with 1%R.
apply Rle_trans with (1-x/y)%R.
2: right; unfold Rdiv; ring.
left; apply Rle_lt_trans with (2:=proj1 H0).
right; field.
now apply Rgt_not_eq.
rewrite <- Hx', Rminus_0_l.
now apply generic_format_opp.

clear H; intros H; fold n; rewrite <- H.
now rewrite Rmult_0_l, Rminus_0_r.
Qed.

End format_REM_aux.

Section format_REM.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.

Notation format := (generic_format beta fexp).

Theorem format_REM :
  forall rnd : R -> Z, Valid_rnd rnd ->
  forall x y : R,
  ((Rabs (x/y) < /2)%R -> rnd (x/y)%R = 0%Z) ->
  format x -> format y ->
  format (x - IZR (rnd (x/y)%R) * y).
Proof using monotone_exp valid_exp.
Proof with auto with typeclass_instances.

assert (H: forall rnd : R -> Z, Valid_rnd rnd ->
  forall x y : R,
  ((Rabs (x/y) < /2)%R -> rnd (x/y)%R = 0%Z) ->
  format x -> format y -> (0 < y)%R ->
  format (x - IZR (rnd (x/y)%R) * y)).
intros rnd valid_rnd x y Hrnd Fx Fy Hy.
case (Rle_or_lt 0 x); intros Hx.
apply format_REM_aux; try easy.
intros K.
apply Hrnd.
rewrite Rabs_pos_eq.
apply K.
apply Rlt_le, K.
replace (x - IZR (rnd (x/y)) * y)%R with
   (- (-x - IZR (Zrnd_opp rnd (-x/y)) * y))%R.
apply generic_format_opp.
apply format_REM_aux; try easy...
now apply generic_format_opp.
apply Ropp_le_cancel; rewrite Ropp_0, Ropp_involutive; now left.
replace (- x / y)%R with (- (x/y))%R by (unfold Rdiv; ring).
intros K.
unfold Zrnd_opp.
rewrite Ropp_involutive, Hrnd.
easy.
rewrite Rabs_left.
apply K.
apply Ropp_lt_cancel.
now rewrite Ropp_0.
unfold Zrnd_opp.
replace (- (- x / y))%R with (x / y)%R by (unfold Rdiv; ring).
rewrite opp_IZR.
ring.

intros rnd valid_rnd x y Hrnd Fx Fy.
case (Rle_or_lt 0 y); intros Hy.
destruct Hy as [Hy|Hy].
now apply H.
now rewrite <- Hy, Rmult_0_r, Rminus_0_r.
replace (IZR (rnd (x/y)) * y)%R with
  (IZR ((Zrnd_opp rnd) ((x / -y))) * -y)%R.
apply H; try easy...
replace (x / - y)%R with (- (x/y))%R.
intros K.
unfold Zrnd_opp.
rewrite Ropp_involutive, Hrnd.
easy.
now rewrite <- Rabs_Ropp.
field; now apply Rlt_not_eq.
now apply generic_format_opp.
apply Ropp_lt_cancel; now rewrite Ropp_0, Ropp_involutive.
unfold Zrnd_opp.
replace (- (x / - y))%R with (x/y)%R.
rewrite opp_IZR.
ring.
field; now apply Rlt_not_eq.
Qed.

Theorem format_REM_ZR:
  forall x y : R,
  format x -> format y ->
  format (x - IZR (Ztrunc (x/y)) * y).
Proof using monotone_exp valid_exp.
Proof with auto with typeclass_instances.
intros x y Fx Fy.
apply format_REM; try easy...
intros K.
apply Z.abs_0_iff.
rewrite <- Ztrunc_abs.
rewrite Ztrunc_floor by apply Rabs_pos.
apply Zle_antisym.
replace 0%Z with (Zfloor (/2)).
apply Zfloor_le.
now apply Rlt_le.
apply Zfloor_imp.
simpl ; lra.
apply Zfloor_lub.
apply Rabs_pos.
Qed.

Theorem format_REM_N :
  forall choice,
  forall x y : R,
  format x -> format y ->
  format (x - IZR (Znearest choice (x/y)) * y).
Proof using monotone_exp valid_exp.
Proof with auto with typeclass_instances.
intros choice x y Fx Fy.
apply format_REM; try easy...
intros K.
apply Znearest_imp.
now rewrite Rminus_0_r.
Qed.

End format_REM.


Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Core Flocq.Core.FTZ.

Open Scope R_scope.

Section Double_round.

Variable beta : radix.
Notation bpow e := (bpow beta e).
Notation mag x := (mag beta x).

Definition round_round_eq fexp1 fexp2 choice1 choice2 x :=
  round beta fexp1 (Znearest choice1) (round beta fexp2 (Znearest choice2) x)
  = round beta fexp1 (Znearest choice1) x.

Ltac bpow_simplify :=

  repeat
    match goal with
      | |- context [(Raux.bpow _ _ * Raux.bpow _ _)] =>
        rewrite <- bpow_plus
      | |- context [(?X1 * Raux.bpow _ _ * Raux.bpow _ _)] =>
        rewrite (Rmult_assoc X1); rewrite <- bpow_plus
      | |- context [(?X1 * (?X2 * Raux.bpow _ _) * Raux.bpow _ _)] =>
        rewrite <- (Rmult_assoc X1 X2); rewrite (Rmult_assoc (X1 * X2));
        rewrite <- bpow_plus
    end;

  repeat
    match goal with
      | |- context [(Raux.bpow _ ?X)] =>
        progress ring_simplify X
    end;

  change (Raux.bpow _ 0) with 1;
  repeat
    match goal with
      | |- context [(_ * 1)] =>
        rewrite Rmult_1_r
    end.

Definition midp (fexp : Z -> Z) (x : R) :=
  round beta fexp Zfloor x + / 2 * ulp beta fexp x.

Definition midp' (fexp : Z -> Z) (x : R) :=
  round beta fexp Zceil x - / 2 * ulp beta fexp x.

Lemma round_round_lt_mid_further_place' :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  x < bpow (mag x) - / 2 * ulp beta fexp2 x ->
  x < midp fexp1 x - / 2 * ulp beta fexp2 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hx1.
unfold round_round_eq.
set (x' := round beta fexp1 Zfloor x).
intro Hx2'.
assert (Hx2 : x - round beta fexp1 Zfloor x
              < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
{
 now apply (Rplus_lt_reg_r (round beta fexp1 Zfloor x)); ring_simplify.
}
set (x'' := round beta fexp2 (Znearest choice2) x).
assert (Hr1 : Rabs (x'' - x) <= / 2 * bpow (fexp2 (mag x))).
apply Rle_trans with (/ 2 * ulp beta fexp2 x).
now unfold x''; apply error_le_half_ulp...
rewrite ulp_neq_0;[now right|now apply Rgt_not_eq].
assert (Pxx' : 0 <= x - x').
{
 apply Rle_0_minus.
  apply round_DN_pt.
  exact Vfexp1.
}
rewrite 2!ulp_neq_0 in Hx2; try (apply Rgt_not_eq; assumption).
assert (Hr2 : Rabs (x'' - x') < / 2 * bpow (fexp1 (mag x))).
{
 replace (x'' - x') with (x'' - x + (x - x')) by ring.
  apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
  replace (/ 2 * _) with (/ 2 * bpow (fexp2 (mag x))
                          + (/ 2 * (bpow (fexp1 (mag x))
                                    - bpow (fexp2 (mag x))))) by ring.
  apply Rplus_le_lt_compat.
  -
 exact Hr1.
  -
 now rewrite Rabs_right; [|now apply Rle_ge]; apply Hx2.
}
destruct (Req_dec x'' 0) as [Zx''|Nzx''].
-

  rewrite Zx'' in Hr1 |- *.
  rewrite round_0; [|now apply valid_rnd_N].
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  rewrite (Znearest_imp _ _ 0); [now simpl; rewrite Rmult_0_l|].
  apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult; rewrite Rmult_minus_distr_r.
  rewrite Rmult_0_l.
  bpow_simplify.
  rewrite Rabs_minus_sym.
  apply (Rle_lt_trans _ _ _ Hr1).
  apply Rmult_lt_compat_l; [lra|].
  apply bpow_lt.
  lia.
-

  assert (Lx'' : mag x'' = mag x :> Z).
  {
 apply Zle_antisym.
    -
 apply mag_le_bpow; [exact Nzx''|].
      replace x'' with (x'' - x + x) by ring.
      apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
      replace (bpow _) with (/ 2 * bpow (fexp2 (mag x))
                             + (bpow (mag x)
                                - / 2 * bpow (fexp2 (mag x)))) by ring.
      apply Rplus_le_lt_compat; [exact Hr1|].
      rewrite ulp_neq_0 in Hx1;[idtac| now apply Rgt_not_eq].
      now rewrite Rabs_right; [|apply Rle_ge; apply Rlt_le].
    -
 unfold x'' in Nzx'' |- *.
      now apply mag_round_ge; [|apply valid_rnd_N|].
}
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  rewrite Lx''.
  rewrite (Znearest_imp _ _ (Zfloor (scaled_mantissa beta fexp1 x))).
  +
 rewrite (Znearest_imp _ _ (Zfloor (scaled_mantissa beta fexp1 x)));
    [reflexivity|].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    fold x'.
    bpow_simplify.
    rewrite Rabs_right; [|now apply Rle_ge].
    apply (Rlt_le_trans _ _ _ Hx2).
    apply Rmult_le_compat_l; [lra|].
    generalize (bpow_ge_0 beta (fexp2 (mag x))).
    unfold ulp, cexp; lra.
  +
 apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    fold x'.
    now bpow_simplify.
Qed.

Lemma round_round_lt_mid_further_place :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  x < midp fexp1 x - / 2 * ulp beta fexp2 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1.
intro Hx2'.
assert (Hx2 : x - round beta fexp1 Zfloor x
              < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
{
 now apply (Rplus_lt_reg_r (round beta fexp1 Zfloor x)); ring_simplify.
}
revert Hx2.
unfold round_round_eq.
set (x' := round beta fexp1 Zfloor x).
intro Hx2.
assert (Pxx' : 0 <= x - x').
{
 apply Rle_0_minus.
  apply round_DN_pt.
  exact Vfexp1.
}
assert (x < bpow (mag x) - / 2 * bpow (fexp2 (mag x)));
  [|apply round_round_lt_mid_further_place'; try assumption]...
2: rewrite ulp_neq_0;[assumption|now apply Rgt_not_eq].
destruct (Req_dec x' 0) as [Zx'|Nzx'].
-

  rewrite Zx' in Hx2; rewrite Rminus_0_r in Hx2.
  apply (Rlt_le_trans _ _ _ Hx2).
  rewrite Rmult_minus_distr_l.
  rewrite 2!ulp_neq_0;[idtac|now apply Rgt_not_eq|now apply Rgt_not_eq].
  apply Rplus_le_compat_r.
  apply (Rmult_le_reg_r (bpow (- mag x))); [now apply bpow_gt_0|].
  unfold ulp, cexp; bpow_simplify.
  apply Rmult_le_reg_l with (1 := Rlt_0_2).
  replace (2 * (/ 2 * _)) with (bpow (fexp1 (mag x) - mag x)) by field.
  apply Rle_trans with 1; [|lra].
  change 1 with (bpow 0); apply bpow_le.
  lia.
-

  assert (Px' : 0 < x').
  {
 assert (0 <= x'); [|lra].
    unfold x'.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_0_l.
    unfold round, F2R, cexp; simpl; bpow_simplify.
    apply IZR_le.
    apply Zfloor_lub.
    rewrite <- (Rabs_right x); [|now apply Rle_ge; apply Rlt_le].
    rewrite scaled_mantissa_abs.
    apply Rabs_pos.
}
  assert (Hx' : x' <= bpow (mag x) - ulp beta fexp1 x).
  {
 apply (Rplus_le_reg_r (ulp beta fexp1 x)); ring_simplify.
    rewrite <- ulp_DN.
    -
 change (round _ _ _ _) with x'.
      apply id_p_ulp_le_bpow.
      +
 exact Px'.
      +
 change x' with (round beta fexp1 Zfloor x).
        now apply generic_format_round; [|apply valid_rnd_DN].
      +
 apply Rle_lt_trans with x.
        *
 now apply round_DN_pt.
        *
 rewrite <- (Rabs_right x) at 1; [|now apply Rle_ge; apply Rlt_le].
          apply bpow_mag_gt.
    -
 exact Vfexp1.
    -
 now apply Rlt_le.
}
  fold (cexp beta fexp2 x); fold (ulp beta fexp2 x).
  assert (/ 2 * ulp beta fexp1 x <= ulp beta fexp1 x).
  rewrite <- (Rmult_1_l (ulp _ _ _)) at 2.
  apply Rmult_le_compat_r; [|lra].
  apply ulp_ge_0.
  rewrite 2!ulp_neq_0 in Hx2;[|now apply Rgt_not_eq|now apply Rgt_not_eq].
  rewrite ulp_neq_0 in Hx';[|now apply Rgt_not_eq].
  rewrite ulp_neq_0 in H;[|now apply Rgt_not_eq].
  lra.
Qed.

Lemma round_round_lt_mid_same_place :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) = fexp1 (mag x))%Z ->
  x < midp fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 choice1 choice2 x Px Hf2f1.
intro Hx'.
assert (Hx : x - round beta fexp1 Zfloor x < / 2 * ulp beta fexp1 x).
{
 now apply (Rplus_lt_reg_r (round beta fexp1 Zfloor x)); ring_simplify.
}
revert Hx.
unfold round_round_eq.
set (x' := round beta fexp1 Zfloor x).
intro Hx.
assert (Pxx' : 0 <= x - x').
{
 apply Rle_0_minus.
  apply round_DN_pt.
  exact Vfexp1.
}
assert (H : Rabs (x * bpow (- fexp1 (mag x)) -
                  IZR (Zfloor (x * bpow (- fexp1 (mag x))))) < / 2).
{
 apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  unfold scaled_mantissa, cexp in Hx.
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  apply Rabs_lt.
  change (IZR _ * _) with x'.
  split.
  -
 apply Rlt_le_trans with 0; [|exact Pxx'].
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    rewrite <- (Rmult_0_r (/ 2)).
    apply Rmult_lt_compat_l; [lra|].
    apply bpow_gt_0.
  -
 rewrite ulp_neq_0 in Hx;try apply Rgt_not_eq; assumption.
}
unfold round at 2.
unfold F2R, scaled_mantissa, cexp; simpl.
rewrite Hf2f1.
rewrite (Znearest_imp _ _ (Zfloor (scaled_mantissa beta fexp1 x)) H).
rewrite round_generic.
  +
 unfold round, F2R, scaled_mantissa, cexp; simpl.
    now rewrite (Znearest_imp _ _ (Zfloor (x * bpow (- fexp1 (mag x))))).
  +
 now apply valid_rnd_N.
  +
 fold (cexp beta fexp1 x).
    change (IZR _ * bpow _) with (round beta fexp1 Zfloor x).
    apply generic_format_round.
    exact Vfexp1.
    now apply valid_rnd_DN.
Qed.

Lemma round_round_lt_mid :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x))%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  x < midp fexp1 x ->
  ((fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
   x < midp fexp1 x - / 2 * ulp beta fexp2 x) ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1 Hx Hx'.
destruct (Zle_or_lt (fexp1 (mag x)) (fexp2 (mag x))) as [Hf2'|Hf2'].
-

  assert (Hf2'' : (fexp2 (mag x) = fexp1 (mag x) :> Z)%Z) by lia.
  now apply round_round_lt_mid_same_place.
-

  assert (Hf2'' : (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z) by lia.
  generalize (Hx' Hf2''); intro Hx''.
  now apply round_round_lt_mid_further_place.
Qed.

Lemma round_round_gt_mid_further_place' :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  round beta fexp2 (Znearest choice2) x < bpow (mag x) ->
  midp' fexp1 x + / 2 * ulp beta fexp2 x < x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1.
intros Hx1 Hx2'.
assert (Hx2 : round beta fexp1 Zceil x - x
              < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
{
 apply (Rplus_lt_reg_r (- / 2 * ulp beta fexp1 x + x
                         + / 2 * ulp beta fexp2 x)); ring_simplify.
  now unfold midp' in Hx2'.
}
revert Hx1 Hx2.
unfold round_round_eq.
set (x' := round beta fexp1 Zceil x).
set (x'' := round beta fexp2 (Znearest choice2) x).
intros Hx1 Hx2.
assert (Hr1 : Rabs (x'' - x) <= / 2 * bpow (fexp2 (mag x))).
  apply Rle_trans with (/2* ulp beta fexp2 x).
  now unfold x''; apply error_le_half_ulp...
  rewrite ulp_neq_0;[now right|now apply Rgt_not_eq].
assert (Px'x : 0 <= x' - x).
{
 apply Rle_0_minus.
  apply round_UP_pt.
  exact Vfexp1.
}
assert (Hr2 : Rabs (x'' - x') < / 2 * bpow (fexp1 (mag x))).
{
 replace (x'' - x') with (x'' - x + (x - x')) by ring.
  apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
  replace (/ 2 * _) with (/ 2 * bpow (fexp2 (mag x))
                          + (/ 2 * (bpow (fexp1 (mag x))
                                    - bpow (fexp2 (mag x))))) by ring.
  apply Rplus_le_lt_compat.
  -
 exact Hr1.
  -
 rewrite Rabs_minus_sym.
   rewrite 2!ulp_neq_0 in Hx2; try (apply Rgt_not_eq; assumption).
    now rewrite Rabs_right; [|now apply Rle_ge]; apply Hx2.
}
destruct (Req_dec x'' 0) as [Zx''|Nzx''].
-

  rewrite Zx'' in Hr1 |- *.
  rewrite round_0; [|now apply valid_rnd_N].
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  rewrite (Znearest_imp _ _ 0); [now simpl; rewrite Rmult_0_l|].
  apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult; rewrite Rmult_minus_distr_r.
  rewrite Rmult_0_l.
  bpow_simplify.
  rewrite Rabs_minus_sym.
  apply (Rle_lt_trans _ _ _ Hr1).
  apply Rmult_lt_compat_l; [lra|].
  apply bpow_lt.
  lia.
-

  assert (Lx'' : mag x'' = mag x :> Z).
  {
 apply Zle_antisym.
    -
 apply mag_le_bpow; [exact Nzx''|].
      rewrite Rabs_right; [exact Hx1|apply Rle_ge].
      apply round_ge_generic.
      +
 exact Vfexp2.
      +
 now apply valid_rnd_N.
      +
 apply generic_format_0.
      +
 now apply Rlt_le.
    -
 unfold x'' in Nzx'' |- *.
      now apply mag_round_ge; [|apply valid_rnd_N|].
}
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  rewrite Lx''.
  rewrite (Znearest_imp _ _ (Zceil (scaled_mantissa beta fexp1 x))).
  +
 rewrite (Znearest_imp _ _ (Zceil (scaled_mantissa beta fexp1 x)));
    [reflexivity|].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    fold x'.
    bpow_simplify.
    rewrite Rabs_minus_sym.
    rewrite Rabs_right; [|now apply Rle_ge].
    apply (Rlt_le_trans _ _ _ Hx2).
    apply Rmult_le_compat_l; [lra|].
    generalize (bpow_ge_0 beta (fexp2 (mag x))).
    rewrite 2!ulp_neq_0; try (apply Rgt_not_eq; assumption).
    unfold cexp; lra.
  +
 apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    fold x'.
    now bpow_simplify.
Qed.

Lemma round_round_gt_mid_further_place :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  midp' fexp1 x + / 2 * ulp beta fexp2 x < x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1 Hx2'.
assert (Hx2 : round beta fexp1 Zceil x - x
              < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
{
 apply (Rplus_lt_reg_r (- / 2 * ulp beta fexp1 x + x
                         + / 2 * ulp beta fexp2 x)); ring_simplify.
  now unfold midp' in Hx2'.
}
revert Hx2.
unfold round_round_eq.
set (x' := round beta fexp1 Zfloor x).
intro Hx2.
set (x'' := round beta fexp2 (Znearest choice2) x).
destruct (Rlt_or_le x'' (bpow (mag x))) as [Hx''|Hx''];
  [now apply round_round_gt_mid_further_place'|].

assert (Hx''pow : x'' = bpow (mag x)).
{
 assert (H'x'' : x'' < bpow (mag x) + / 2 * ulp beta fexp2 x).
  {
 apply Rle_lt_trans with (x + / 2 * ulp beta fexp2 x).
    -
 apply (Rplus_le_reg_r (- x)); ring_simplify.
      apply Rabs_le_inv.
      apply error_le_half_ulp.
      exact Vfexp2.
    -
 apply Rplus_lt_compat_r.
      rewrite <- Rabs_right at 1; [|now apply Rle_ge; apply Rlt_le].
      apply bpow_mag_gt.
}
  apply Rle_antisym; [|exact Hx''].
  unfold x'', round, F2R, scaled_mantissa, cexp; simpl.
  apply (Rmult_le_reg_r (bpow (- fexp2 (mag x)))); [now apply bpow_gt_0|].
  bpow_simplify.
  rewrite <- (IZR_Zpower _ (_ - _)) by lia.
  apply IZR_le.
  apply Zlt_succ_le; unfold Z.succ.
  apply lt_IZR.
  rewrite plus_IZR; rewrite IZR_Zpower by lia.
  apply (Rmult_lt_reg_r (bpow (fexp2 (mag x)))); [now apply bpow_gt_0|].
  rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
  bpow_simplify.
  apply (Rlt_le_trans _ _ _ H'x'').
  apply Rplus_le_compat_l.
  rewrite <- (Rmult_1_l (Raux.bpow _ _)).
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
  apply Rmult_le_compat_r; [now apply bpow_ge_0|].
  lra.
}
assert (Hr : Rabs (x - x'') < / 2 * ulp beta fexp1 x).
{
 apply Rle_lt_trans with (/ 2 * ulp beta fexp2 x).
  -
 rewrite Rabs_minus_sym.
    apply error_le_half_ulp.
    exact Vfexp2.
  -
 apply Rmult_lt_compat_l; [lra|].
    rewrite 2!ulp_neq_0; try now apply Rgt_not_eq.
    unfold cexp; apply bpow_lt.
    lia.
}
unfold round, F2R, scaled_mantissa, cexp; simpl.
assert (Hf : (0 <= mag x - fexp1 (mag x''))%Z).
{
 rewrite Hx''pow.
  rewrite mag_bpow.
  cut (fexp1 (mag x + 1) <= mag x)%Z.
lia.
  destruct (Zle_or_lt (mag x) (fexp1 (mag x))) as [Hle|Hlt];
    [|now apply Vfexp1].
  assert (H : (mag x = fexp1 (mag x) :> Z)%Z);
    [now apply Zle_antisym|].
  rewrite H.
  now apply Vfexp1.
}
rewrite (Znearest_imp _ _ (beta ^ (mag x - fexp1 (mag x'')))%Z).
-
 rewrite (Znearest_imp _ _ (beta ^ (mag x - fexp1 (mag x)))%Z).
  +
 rewrite IZR_Zpower by exact Hf.
    rewrite IZR_Zpower by lia.
    now bpow_simplify.
  +
 rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
   rewrite ulp_neq_0 in Hr;[idtac|now apply Rgt_not_eq].
    rewrite <- Hx''pow; exact Hr.
-
 rewrite IZR_Zpower; [|exact Hf].
  apply (Rmult_lt_reg_r (bpow (fexp1 (mag x'')))); [now apply bpow_gt_0|].
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  rewrite Rminus_diag_eq; [|exact Hx''pow].
  rewrite Rabs_R0.
  rewrite <- (Rmult_0_r (/ 2)).
  apply Rmult_lt_compat_l; [lra|apply bpow_gt_0].
Qed.

Lemma round_round_gt_mid_same_place :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) = fexp1 (mag x))%Z ->
  midp' fexp1 x < x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 choice1 choice2 x Px Hf2f1 Hx'.
assert (Hx : round beta fexp1 Zceil x - x < / 2 * ulp beta fexp1 x).
{
 apply (Rplus_lt_reg_r (- / 2 * ulp beta fexp1 x + x)); ring_simplify.
  now unfold midp' in Hx'.
}
assert (H : Rabs (IZR (Zceil (x * bpow (- fexp1 (mag x))))
                  - x * bpow (- fexp1 (mag x))) < / 2).
{
 apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  unfold scaled_mantissa, cexp in Hx.
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  apply Rabs_lt.
  split.
  -
 apply Rlt_le_trans with 0.
    +
 rewrite <- Ropp_0; apply Ropp_lt_contravar.
      rewrite <- (Rmult_0_r (/ 2)).
      apply Rmult_lt_compat_l; [lra|].
      apply bpow_gt_0.
    +
 apply Rle_0_minus.
      apply round_UP_pt.
      exact Vfexp1.
  -
  rewrite ulp_neq_0 in Hx;[exact Hx|now apply Rgt_not_eq].
}
unfold round_round_eq, round at 2.
unfold F2R, scaled_mantissa, cexp; simpl.
rewrite Hf2f1.
rewrite (Znearest_imp _ _ (Zceil (scaled_mantissa beta fexp1 x))).
-
 rewrite round_generic.
  +
 unfold round, F2R, scaled_mantissa, cexp; simpl.
    now rewrite (Znearest_imp _ _ (Zceil (x * bpow (- fexp1 (mag x)))));
      [|rewrite Rabs_minus_sym].
  +
 now apply valid_rnd_N.
  +
 fold (cexp beta fexp1 x).
    change (IZR _ * bpow _) with (round beta fexp1 Zceil x).
    apply generic_format_round.
    exact Vfexp1.
    now apply valid_rnd_UP.
-
 now rewrite Rabs_minus_sym.
Qed.

Lemma round_round_gt_mid :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x))%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  midp' fexp1 x < x ->
  ((fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
   midp' fexp1 x + / 2 * ulp beta fexp2 x < x) ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1 Hx Hx'.
destruct (Zle_or_lt (fexp1 (mag x)) (fexp2 (mag x))) as [Hf2'|Hf2'].
-

  assert (Hf2'' : (fexp2 (mag x) = fexp1 (mag x) :> Z)%Z) by lia.
  now apply round_round_gt_mid_same_place.
-

  assert (Hf2'' : (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z) by lia.
  generalize (Hx' Hf2''); intro Hx''.
  now apply round_round_gt_mid_further_place.
Qed.

Section Double_round_mult.

Lemma mag_mult_disj :
  forall x y,
  x <> 0 -> y <> 0 ->
  ((mag (x * y) = (mag x + mag y - 1)%Z :> Z)
   \/ (mag (x * y) = (mag x + mag y)%Z :> Z)).
Proof using .
intros x y Zx Zy.
destruct (mag_mult beta x y Zx Zy).
lia.
Qed.

Definition round_round_mult_hyp fexp1 fexp2 :=
  (forall ex ey, (fexp2 (ex + ey) <= fexp1 ex + fexp1 ey)%Z)
  /\ (forall ex ey, (fexp2 (ex + ey - 1) <= fexp1 ex + fexp1 ey)%Z).

Lemma round_round_mult_aux :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_mult_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x * y).
Proof using .
intros fexp1 fexp2 Hfexp x y Fx Fy.
destruct (Req_dec x 0) as [Zx|Zx].
-

  rewrite Zx.
  rewrite Rmult_0_l.
  now apply generic_format_0.
-

  destruct (Req_dec y 0) as [Zy|Zy].
  +

    rewrite Zy.
    rewrite Rmult_0_r.
    now apply generic_format_0.
  +

    revert Fx Fy.
    unfold generic_format.
    unfold cexp.
    set (mx := Ztrunc (scaled_mantissa beta fexp1 x)).
    set (my := Ztrunc (scaled_mantissa beta fexp1 y)).
    unfold F2R; simpl.
    intros Fx Fy.
    set (fxy := Float beta (mx * my) (fexp1 (mag x) + fexp1 (mag y))).
    assert (Hxy : x * y = F2R fxy).
    {
 unfold fxy, F2R; simpl.
      rewrite bpow_plus.
      rewrite mult_IZR.
      rewrite Fx, Fy at 1.
      ring.
}
    apply generic_format_F2R' with (f := fxy); [now rewrite Hxy|].
    intros _.
    unfold cexp, fxy; simpl.
    destruct Hfexp as (Hfexp1, Hfexp2).
    now destruct (mag_mult_disj x y Zx Zy) as [Lxy|Lxy]; rewrite Lxy.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_round_mult :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_mult_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  round beta fexp1 rnd (round beta fexp2 rnd (x * y))
  = round beta fexp1 rnd (x * y).
Proof using valid_rnd.
intros fexp1 fexp2 Hfexp x y Fx Fy.
assert (Hxy : round beta fexp2 rnd (x * y) = x * y).
{
 apply round_generic; [assumption|].
  now apply (round_round_mult_aux fexp1 fexp2).
}
now rewrite Hxy at 1.
Qed.

Section Double_round_mult_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem round_round_mult_FLX :
  (2 * prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round beta (FLX_exp prec) rnd (round beta (FLX_exp prec') rnd (x * y))
  = round beta (FLX_exp prec) rnd (x * y).
Proof using valid_rnd.
intros Hprec x y Fx Fy.
apply round_round_mult;
  [|now apply generic_format_FLX|now apply generic_format_FLX].
unfold round_round_mult_hyp; split; intros ex ey; unfold FLX_exp;
lia.
Qed.

End Double_round_mult_FLX.

Section Double_round_mult_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem round_round_mult_FLT :
  (emin' <= 2 * emin)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round beta (FLT_exp emin prec) rnd
        (round beta (FLT_exp emin' prec') rnd (x * y))
  = round beta (FLT_exp emin prec) rnd (x * y).
Proof using valid_rnd.
intros Hemin Hprec x y Fx Fy.
apply round_round_mult;
  [|now apply generic_format_FLT|now apply generic_format_FLT].
unfold round_round_mult_hyp; split; intros ex ey;
unfold FLT_exp;
generalize (Zmax_spec (ex + ey - prec') emin');
generalize (Zmax_spec (ex + ey - 1 - prec') emin');
generalize (Zmax_spec (ex - prec) emin);
generalize (Zmax_spec (ey - prec) emin);
lia.
Qed.

End Double_round_mult_FLT.

Section Double_round_mult_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem round_round_mult_FTZ :
  (emin' + prec' <= 2 * emin + prec)%Z ->
  (2 * prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round beta (FTZ_exp emin prec) rnd
        (round beta (FTZ_exp emin' prec') rnd (x * y))
  = round beta (FTZ_exp emin prec) rnd (x * y).
Proof using prec_gt_0_ valid_rnd.
intros Hemin Hprec x y Fx Fy.
apply round_round_mult;
  [|now apply generic_format_FTZ|now apply generic_format_FTZ].
unfold round_round_mult_hyp; split; intros ex ey;
unfold FTZ_exp;
unfold Prec_gt_0 in *;
destruct (Z.ltb_spec (ex + ey - prec') emin');
destruct (Z.ltb_spec (ex - prec) emin);
destruct (Z.ltb_spec (ey - prec) emin);
destruct (Z.ltb_spec (ex + ey - 1 - prec') emin');
lia.
Qed.

End Double_round_mult_FTZ.

End Double_round_mult.

Section Double_round_plus.

Lemma mag_plus_disj :
  forall x y,
  0 < y -> y <= x ->
  ((mag (x + y) = mag x :> Z)
   \/ (mag (x + y) = (mag x + 1)%Z :> Z)).
Proof using .
intros x y Py Hxy.
destruct (mag_plus beta x y Py Hxy).
lia.
Qed.

Lemma mag_plus_separated :
  forall fexp : Z -> Z,
  forall x y,
  0 < x -> 0 <= y ->
  generic_format beta fexp x ->
  (mag y <= fexp (mag x))%Z ->
  (mag (x + y) = mag x :> Z).
Proof using .
intros fexp x y Px Nny Fx Hsep.
apply mag_plus_eps with (1 := Px) (2 := Fx).
apply (conj Nny).
rewrite <- Rabs_pos_eq with (1 := Nny).
apply Rlt_le_trans with (1 := bpow_mag_gt beta _).
rewrite ulp_neq_0 by now apply Rgt_not_eq.
now apply bpow_le.
Qed.

Lemma mag_minus_disj :
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= mag x - 2)%Z ->
  ((mag (x - y) = mag x :> Z)
   \/ (mag (x - y) = (mag x - 1)%Z :> Z)).
Proof using .
intros x y Px Py Hln.
assert (Hxy : y < x); [now apply (lt_mag beta); [ |lia]|].
generalize (mag_minus beta x y Py Hxy); intro Hln2.
generalize (mag_minus_lb beta x y Px Py Hln); intro Hln3.
lia.
Qed.

Lemma mag_minus_separated :
  forall fexp : Z -> Z, Valid_exp fexp ->
  forall x y,
  0 < x -> 0 < y -> y < x ->
  bpow (mag x - 1) < x ->
  generic_format beta fexp x -> (mag y <= fexp (mag x))%Z ->
  (mag (x - y) = mag x :> Z).
Proof using .
intros fexp Vfexp x y Px Py Yltx Xgtpow Fx Ly.
apply mag_unique.
split.
-
 apply Rabs_ge; right.
  assert (Hy : y < ulp beta fexp (bpow (mag x - 1))).
  {
 rewrite ulp_bpow.
    replace (_ + _)%Z with (mag x : Z) by ring.
    rewrite <- (Rabs_right y); [|now apply Rle_ge; apply Rlt_le].
    apply Rlt_le_trans with (bpow (mag y)).
    -
 apply bpow_mag_gt.
    -
 now apply bpow_le.
}
  apply (Rplus_le_reg_r y); ring_simplify.
  apply Rle_trans with (bpow (mag x - 1)
                        + ulp beta fexp (bpow (mag x - 1))).
  +
 now apply Rplus_le_compat_l; apply Rlt_le.
  +
 rewrite <- succ_eq_pos;[idtac|apply bpow_ge_0].
    apply succ_le_lt; [apply Vfexp|idtac|exact Fx|assumption].
    apply (generic_format_bpow beta fexp (mag x - 1)).
    replace (_ + _)%Z with (mag x : Z) by ring.
    cut (fexp (mag x) < mag x)%Z.
lia.
    now apply mag_generic_gt; [|now apply Rgt_not_eq|].
-
 rewrite Rabs_right.
  +
 apply Rlt_trans with x.
    *
 rewrite <- (Rplus_0_r x) at 2.
      apply Rplus_lt_compat_l.
      rewrite <- Ropp_0.
      now apply Ropp_lt_contravar.
    *
 apply Rabs_lt_inv.
      apply bpow_mag_gt.
  +
 lra.
Qed.

Definition round_round_plus_hyp fexp1 fexp2 :=
  (forall ex ey, (fexp1 (ex + 1) - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (fexp1 (ex - 1) + 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (fexp1 ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z).

Lemma round_round_plus_aux0_aux_aux :
  forall (fexp1 fexp2 : Z -> Z),
  forall x y,
  (fexp1 (mag x) <= fexp1 (mag y))%Z ->
  (fexp2 (mag (x + y))%Z <= fexp1 (mag x))%Z ->
  (fexp2 (mag (x + y))%Z <= fexp1 (mag y))%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof using .
intros fexp1 fexp2 x y Oxy Hlnx Hlny Fx Fy.
destruct (Req_dec x 0) as [Zx|Nzx].
-

  rewrite Zx, Rplus_0_l in Hlny |- *.
  now apply (generic_inclusion_mag beta fexp1).
-

  destruct (Req_dec y 0) as [Zy|Nzy].
  +

    rewrite Zy, Rplus_0_r in Hlnx |- *.
    now apply (generic_inclusion_mag beta fexp1).
  +

    revert Fx Fy.
    unfold generic_format at -3, cexp, F2R; simpl.
    set (mx := Ztrunc (scaled_mantissa beta fexp1 x)).
    set (my := Ztrunc (scaled_mantissa beta fexp1 y)).
    intros Fx Fy.
    set (fxy := Float beta (mx + my * (beta ^ (fexp1 (mag y)
                                               - fexp1 (mag x))))
                      (fexp1 (mag x))).
    assert (Hxy : x + y = F2R fxy).
    {
 unfold fxy, F2R; simpl.
      rewrite plus_IZR.
      rewrite Rmult_plus_distr_r.
      rewrite <- Fx.
      rewrite mult_IZR.
      rewrite IZR_Zpower by lia.
      bpow_simplify.
      now rewrite <- Fy.
}
    apply generic_format_F2R' with (f := fxy); [now rewrite Hxy|].
    intros _.
    now unfold cexp, fxy; simpl.
Qed.

Lemma round_round_plus_aux0_aux :
  forall (fexp1 fexp2 : Z -> Z),
  forall x y,
  (fexp2 (mag (x + y))%Z <= fexp1 (mag x))%Z ->
  (fexp2 (mag (x + y))%Z <= fexp1 (mag y))%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof using .
intros fexp1 fexp2 x y Hlnx Hlny Fx Fy.
destruct (Z.le_gt_cases (fexp1 (mag x)) (fexp1 (mag y))) as [Hle|Hgt].
-
 now apply (round_round_plus_aux0_aux_aux fexp1).
-
 rewrite Rplus_comm in Hlnx, Hlny |- *.
  now apply (round_round_plus_aux0_aux_aux fexp1); [lia| | | |].
Qed.

Lemma round_round_plus_aux0 :
  forall (fexp1 fexp2 : Z -> Z), Valid_exp fexp1 ->
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  (0 < x)%R -> (0 < y)%R -> (y <= x)%R ->
  (fexp1 (mag x) - 1 <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof using .
intros fexp1 fexp2 Vfexp1 Hexp x y Px Py Hyx Hln Fx Fy.
assert (Nny : (0 <= y)%R); [now apply Rlt_le|].
destruct Hexp as (_,(Hexp2,(Hexp3,Hexp4))).
destruct (Z.le_gt_cases (mag y) (fexp1 (mag x))) as [Hle|Hgt].
-

  assert (Lxy : mag (x + y) = mag x :> Z);
  [now apply (mag_plus_separated fexp1)|].
  apply (round_round_plus_aux0_aux fexp1);
    [| |assumption|assumption]; rewrite Lxy.
  +
 now apply Hexp4; lia.
  +
 now apply Hexp3; lia.
-

  apply (round_round_plus_aux0_aux fexp1); [| |assumption|assumption].
  destruct (mag_plus_disj x y Py Hyx) as [Lxy|Lxy]; rewrite Lxy.
  +
 now apply Hexp4; lia.
  +
 apply Hexp2; apply (mag_le beta y x Py) in Hyx.
    replace (_ - _)%Z with (mag x : Z) by ring.
    lia.
  +
 destruct (mag_plus_disj x y Py Hyx) as [Lxy|Lxy]; rewrite Lxy.
    *
 now apply Hexp3; lia.
    *
 apply Hexp2.
      replace (_ - _)%Z with (mag x : Z) by ring.
      lia.
Qed.

Lemma round_round_plus_aux1_aux :
  forall k, (0 < k)%Z ->
  forall (fexp : Z -> Z),
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= fexp (mag x) - k)%Z ->
  (mag (x + y) = mag x :> Z) ->
  generic_format beta fexp x ->
  0 < (x + y) - round beta fexp Zfloor (x + y) < bpow (fexp (mag x) - k).
Proof using .
assert (Hbeta : (2 <= beta)%Z).
{
 destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
}
intros k Hk fexp x y Px Py Hln Hlxy Fx.
revert Fx.
unfold round, generic_format, F2R, scaled_mantissa, cexp; simpl.
rewrite Hlxy.
set (mx := Ztrunc (x * bpow (- fexp (mag x)))).
intros Fx.
assert (R : (x + y) * bpow (- fexp (mag x))
            = IZR mx + y * bpow (- fexp (mag x))).
{
 rewrite Fx at 1.
  rewrite Rmult_plus_distr_r.
  now bpow_simplify.
}
rewrite R.
assert (LB : 0 < y * bpow (- fexp (mag x))).
{
 rewrite <- (Rmult_0_r y).
  now apply Rmult_lt_compat_l; [|apply bpow_gt_0].
}
assert (UB : y * bpow (- fexp (mag x)) < / IZR (beta ^ k)).
{
 apply Rlt_le_trans with (bpow (mag y) * bpow (- fexp (mag x))).
  -
 apply Rmult_lt_compat_r; [now apply bpow_gt_0|].
    rewrite <- (Rabs_right y) at 1; [|now apply Rle_ge; apply Rlt_le].
    apply bpow_mag_gt.
  -
 apply Rle_trans with (bpow (fexp (mag x) - k)
                          * bpow (- fexp (mag x)))%R.
    +
 apply Rmult_le_compat_r; [now apply bpow_ge_0|].
      now apply bpow_le.
    +
 bpow_simplify.
      rewrite bpow_opp.
      destruct k.
      *
 lia.
      *
 simpl; unfold Raux.bpow, Z.pow_pos.
        now apply Rle_refl.
      *
 exfalso; apply (Z.lt_irrefl 0).
        apply (Z.lt_trans _ _ _ Hk).
        apply Zlt_neg_0.
}
rewrite (Zfloor_imp mx).
{
 split; ring_simplify.
  -
 apply (Rmult_lt_reg_r (bpow (- fexp (mag x)))); [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r, Rmult_0_l.
    bpow_simplify.
    rewrite R; ring_simplify.
    now apply Rmult_lt_0_compat; [|apply bpow_gt_0].
  -
 apply (Rmult_lt_reg_r (bpow (- fexp (mag x)))); [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    rewrite R; ring_simplify.
    apply (Rlt_le_trans _ _ _ UB).
    rewrite bpow_opp.
    apply Rinv_le; [now apply bpow_gt_0|].
    now rewrite IZR_Zpower; [right|lia].
}
split.
-
 rewrite <- Rplus_0_r at 1; apply Rplus_le_compat_l.
  now apply Rlt_le.
-
 rewrite plus_IZR; apply Rplus_lt_compat_l.
  apply (Rmult_lt_reg_r (bpow (fexp (mag x)))); [now apply bpow_gt_0|].
  rewrite Rmult_1_l.
  bpow_simplify.
  apply Rlt_trans with (bpow (mag y)).
  +
 rewrite <- Rabs_right at 1; [|now apply Rle_ge; apply Rlt_le].
    apply bpow_mag_gt.
  +
 apply bpow_lt; lia.
Qed.

Lemma round_round_plus_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= fexp1 (mag x) - 2)%Z ->
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof using .
assert (Hbeta : (2 <= beta)%Z).
{
 destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
}
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Hly Fx.
assert (Lxy : mag (x + y) = mag x :> Z);
  [now apply (mag_plus_separated fexp1); [|apply Rlt_le| |lia]|].
destruct Hexp as (_,(_,(_,Hexp4))).
assert (Hf2 : (fexp2 (mag x) <= fexp1 (mag x))%Z);
  [now apply Hexp4; lia|].
assert (Bpow2 : bpow (- 2) <= / 2 * / 2).
{
 replace (/2 * /2) with (/4) by field.
  rewrite (bpow_opp _ 2).
  apply Rinv_le; [lra|].
  apply (IZR_le (2 * 2) (beta * (beta * 1))).
  rewrite Zmult_1_r.
  now apply Zmult_le_compat; lia.
}
assert (P2 : (0 < 2)%Z) by lia.
unfold round_round_eq.
apply round_round_lt_mid.
-
 exact Vfexp1.
-
 exact Vfexp2.
-
 lra.
-
 now rewrite Lxy.
-
 rewrite Lxy.
  cut (fexp1 (mag x) < mag x)%Z.
lia.
  now apply mag_generic_gt; [|apply Rgt_not_eq|].
-
 unfold midp.
  apply (Rplus_lt_reg_r (- round beta fexp1 Zfloor (x + y))).
  apply (Rlt_le_trans _ _ _ (proj2 (round_round_plus_aux1_aux 2 P2 fexp1 x y Px
                                                               Py Hly Lxy Fx))).
  ring_simplify.
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold cexp; rewrite Lxy.
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag x)))); [now apply bpow_gt_0|].
  bpow_simplify.
  apply (Rle_trans _ _ _ Bpow2).
  rewrite <- (Rmult_1_r (/ 2)) at 3.
  apply Rmult_le_compat_l; lra.
-
 rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold round, F2R, scaled_mantissa, cexp; simpl; rewrite Lxy.
  intro Hf2'.
  apply (Rmult_lt_reg_r (bpow (- fexp1 (mag x))));
    [now apply bpow_gt_0|].
  apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  bpow_simplify.
  apply (Rplus_lt_reg_r (- round beta fexp1 Zfloor (x + y))).
  unfold midp; ring_simplify.
  apply (Rlt_le_trans _ _ _ (proj2 (round_round_plus_aux1_aux 2 P2 fexp1 x y Px
                                                               Py Hly Lxy Fx))).
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag x)))); [now apply bpow_gt_0|].
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold cexp; rewrite Lxy, Rmult_minus_distr_r; bpow_simplify.
  apply (Rle_trans _ _ _ Bpow2).
  rewrite <- (Rmult_1_r (/ 2)) at 3; rewrite <- Rmult_minus_distr_l.
  apply Rmult_le_compat_l; [lra|].
  apply (Rplus_le_reg_r (- 1)); ring_simplify.
  replace (_ - _) with (- (/ 2)) by lra.
  apply Ropp_le_contravar.
  {
 apply Rle_trans with (bpow (- 1)).
    -
 apply bpow_le; lia.
    -
 unfold Raux.bpow, Z.pow_pos; simpl.
      apply Rinv_le; [lra|].
      apply IZR_le; lia.
}
Qed.

Lemma round_round_plus_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y -> y <= x ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Hyx Fx Fy.
unfold round_round_eq.
destruct (Zle_or_lt (mag y) (fexp1 (mag x) - 2)) as [Hly|Hly].
-

  now apply round_round_plus_aux1.
-

  rewrite (round_generic beta fexp2).
  +
 reflexivity.
  +
 now apply valid_rnd_N.
  +
 assert (Hf1 : (fexp1 (mag x) - 1 <= mag y)%Z) by lia.
    now apply (round_round_plus_aux0 fexp1).
Qed.

Lemma round_round_plus_aux :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Nnx Nny Fx Fy.
unfold round_round_eq.
destruct (Req_dec x 0) as [Zx|Nzx].
-

  destruct Hexp as (_,(_,(_,Hexp4))).
  rewrite Zx; rewrite Rplus_0_l.
  rewrite (round_generic beta fexp2).
  +
 reflexivity.
  +
 now apply valid_rnd_N.
  +
 apply (generic_inclusion_mag beta fexp1).
    now intros _; apply Hexp4; lia.
    exact Fy.
-

  destruct (Req_dec y 0) as [Zy|Nzy].
  +

    destruct Hexp as (_,(_,(_,Hexp4))).
    rewrite Zy; rewrite Rplus_0_r.
    rewrite (round_generic beta fexp2).
    *
 reflexivity.
    *
 now apply valid_rnd_N.
    *
 apply (generic_inclusion_mag beta fexp1).
      now intros _; apply Hexp4; lia.
      exact Fx.
  +

    assert (Px : 0 < x); [lra|].
    assert (Py : 0 < y); [lra|].
    destruct (Rlt_or_le x y) as [H|H].
    *

      apply Rlt_le in H.
      rewrite Rplus_comm.
      now apply round_round_plus_aux2.
    *
 now apply round_round_plus_aux2.
Qed.

Lemma round_round_minus_aux0_aux :
  forall (fexp1 fexp2 : Z -> Z),
  forall x y,
  (fexp2 (mag (x - y))%Z <= fexp1 (mag x))%Z ->
  (fexp2 (mag (x - y))%Z <= fexp1 (mag y))%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof using .
intros fexp1 fexp2 x y.
replace (x - y)%R with (x + (- y))%R; [|ring].
intros Hlnx Hlny Fx Fy.
rewrite <- (mag_opp beta y) in Hlny.
apply generic_format_opp in Fy.
now apply (round_round_plus_aux0_aux fexp1).
Qed.

Lemma round_round_minus_aux0 :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (fexp1 (mag x) - 1 <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof using .
intros fexp1 fexp2 Hexp x y Py Hyx Hln Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hyx).
destruct Hexp as (Hexp1,(_,(Hexp3,Hexp4))).
assert (Lyx : (mag y <= mag x)%Z);
  [now apply mag_le; [|apply Rlt_le]|].
destruct (Z.lt_ge_cases (mag x - 2) (mag y)) as [Hlt|Hge].
-

  assert (Hor : (mag y = mag x :> Z) \/ (mag y = mag x - 1 :> Z)%Z) by lia.
  destruct Hor as [Heq|Heqm1].
  +

    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    *
 apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
    *
 rewrite Heq.
      apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
  +

    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    *
 apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
    *
 rewrite Heqm1.
      apply Hexp4.
      apply Zplus_le_compat_r.
      now apply mag_minus.
-

  destruct (mag_minus_disj x y Px Py Hge) as [Lxmy|Lxmy].
  +

    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    *
 apply Hexp4.
      lia.
    *
 now rewrite Lxmy; apply Hexp3.
  +

    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy];
    rewrite Lxmy.
    *
 apply Hexp1.
      replace (_ + _)%Z with (mag x : Z); [|ring].
      now apply Z.le_trans with (mag y).
    *
 apply Hexp1.
      now replace (_ + _)%Z with (mag x : Z); [|ring].
Qed.

Lemma round_round_minus_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp1 (mag x) - 2)%Z ->
  (fexp1 (mag (x - y)) - 1 <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2  Hexp x y Py Hyx Hln Hln' Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hyx).
destruct Hexp as (Hexp1,(Hexp2,(Hexp3,Hexp4))).
assert (Lyx : (mag y <= mag x)%Z);
  [now apply mag_le; [|apply Rlt_le]|].
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
-
 apply Z.le_trans with (fexp1 (mag (x - y))).
  +
 apply Hexp4; lia.
  +
 lia.
-
 now apply Hexp3.
Qed.

Lemma round_round_minus_aux2_aux :
  forall (fexp : Z -> Z),
  Valid_exp fexp ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp (mag x) - 1)%Z ->
  generic_format beta fexp x ->
  generic_format beta fexp y ->
  round beta fexp Zceil (x - y) - (x - y) <= y.
Proof using .
intros fexp Vfexp x y Py Hxy Hly Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hxy).
revert Fx.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp (mag x)))).
intro Fx.
assert (Hfx : (fexp (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
destruct (Rlt_or_le (bpow (mag x - 1)) x) as [Hx|Hx].
-

  assert (Lxy : mag (x - y) = mag x :> Z);
    [now apply (mag_minus_separated fexp); [| | | | | |lia]|].
  assert (Rxy : round beta fexp Zceil (x - y) = x).
  {
 unfold round, F2R, scaled_mantissa, cexp; simpl.
    rewrite Lxy.
    apply eq_sym; rewrite Fx at 1; apply eq_sym.
    apply Rmult_eq_compat_r.
    apply f_equal.
    rewrite Fx at 1.
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    apply Zceil_imp.
    split.
    -
 unfold Zminus; rewrite plus_IZR.
      apply Rplus_lt_compat_l.
      apply Ropp_lt_contravar; simpl.
      apply (Rmult_lt_reg_r (bpow (fexp (mag x))));
        [now apply bpow_gt_0|].
      rewrite Rmult_1_l; bpow_simplify.
      apply Rlt_le_trans with (bpow (mag y)).
      +
 rewrite <- Rabs_right at 1; [|now apply Rle_ge; apply Rlt_le].
        apply bpow_mag_gt.
      +
 apply bpow_le.
        lia.
    -
 rewrite <- (Rplus_0_r (IZR _)) at 2.
      apply Rplus_le_compat_l.
      rewrite <- Ropp_0; apply Ropp_le_contravar.
      rewrite <- (Rmult_0_r y).
      apply Rmult_le_compat_l; [now apply Rlt_le|].
      now apply bpow_ge_0.
}
  rewrite Rxy; ring_simplify.
  apply Rle_refl.
-

  assert (Xpow : x = bpow (mag x - 1)).
  {
 apply Rle_antisym; [exact Hx|].
    destruct (mag x) as (ex, Hex); simpl.
    rewrite <- (Rabs_right x); [|now apply Rle_ge; apply Rlt_le].
    apply Hex.
    now apply Rgt_not_eq.
}
  assert (Lxy : (mag (x - y) = mag x - 1 :> Z)%Z).
  {
 apply Zle_antisym.
    -
 apply mag_le_bpow.
      +
 apply Rminus_eq_contra.
        now intro Hx'; rewrite Hx' in Hxy; apply (Rlt_irrefl y).
      +
 rewrite Rabs_right; lra.
    -
 apply (mag_minus_lb beta x y Px Py).
      lia.
}
  assert (Hfx1 : (fexp (mag x - 1) < mag x - 1)%Z);
    [now apply (valid_exp_large fexp (mag y)); [|lia]|].
  assert (Rxy : round beta fexp Zceil (x - y) <= x).
  {
 rewrite Xpow at 2.
    unfold round, F2R, scaled_mantissa, cexp; simpl.
    rewrite Lxy.
    apply (Rmult_le_reg_r (bpow (- fexp (mag x - 1)%Z)));
      [now apply bpow_gt_0|].
    bpow_simplify.
    rewrite <- (IZR_Zpower beta (_ - _ - _)) by lia.
    apply IZR_le.
    apply Zceil_glb.
    rewrite IZR_Zpower by lia.
    rewrite Xpow at 1.
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    rewrite <- (Rplus_0_r (bpow _)) at 2.
    apply Rplus_le_compat_l.
    rewrite <- Ropp_0; apply Ropp_le_contravar.
    rewrite <- (Rmult_0_r y).
    apply Rmult_le_compat_l; [now apply Rlt_le|].
    now apply bpow_ge_0.
}
  lra.
Qed.

Lemma round_round_minus_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp1 (mag x) - 2)%Z ->
  (mag y <= fexp1 (mag (x - y)) - 2)%Z ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof using .
assert (Hbeta : (2 <= beta)%Z).
{
 destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
}
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hxy Hly Hly' Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hxy).
destruct Hexp as (_,(_,(_,Hexp4))).
assert (Hf2 : (fexp2 (mag x) <= fexp1 (mag x))%Z);
  [now apply Hexp4; lia|].
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Bpow2 : bpow (- 2) <= / 2 * / 2).
{
 replace (/2 * /2) with (/4) by field.
  rewrite (bpow_opp _ 2).
  apply Rinv_le; [lra|].
  apply (IZR_le (2 * 2) (beta * (beta * 1))).
  rewrite Zmult_1_r.
  now apply Zmult_le_compat; lia.
}
assert (Ly : y < bpow (mag y)).
{
 apply Rabs_lt_inv.
  apply bpow_mag_gt.
}
unfold round_round_eq.
apply round_round_gt_mid.
-
 exact Vfexp1.
-
 exact Vfexp2.
-
 lra.
-
 apply Hexp4; lia.
-
 cut (fexp1 (mag (x - y)) < mag (x - y))%Z.
lia.
  apply (valid_exp_large fexp1 (mag x - 1)).
  +
 apply (valid_exp_large fexp1 (mag y)); [|lia].
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
  +
 now apply mag_minus_lb; [| |lia].
-
 unfold midp'.
  apply (Rplus_lt_reg_r (/ 2 * ulp beta fexp1 (x - y) - (x - y))).
  ring_simplify.
  replace (_ + _) with (round beta fexp1 Zceil (x - y) - (x - y)) by ring.
  apply Rlt_le_trans with (bpow (fexp1 (mag (x - y)) - 2)).
  +
 apply Rle_lt_trans with y;
    [now apply round_round_minus_aux2_aux; try assumption; lia|].
    apply (Rlt_le_trans _ _ _ Ly).
    now apply bpow_le.
  +
 rewrite ulp_neq_0;[idtac|now apply sym_not_eq, Rlt_not_eq, Rgt_minus].
    unfold cexp.
    replace (_ - 2)%Z with (fexp1 (mag (x - y)) - 1 - 1)%Z by ring.
    unfold Zminus at 1; rewrite bpow_plus.
    rewrite Rmult_comm.
    apply Rmult_le_compat.
    *
 now apply bpow_ge_0.
    *
 now apply bpow_ge_0.
    *
 unfold Raux.bpow, Z.pow_pos; simpl.
      rewrite Zmult_1_r; apply Rinv_le.
      lra.
      now apply IZR_le.
    *
 apply bpow_le; lia.
-
 intro Hf2'.
  unfold midp'.
  apply (Rplus_lt_reg_r (/ 2 * ulp beta fexp1 (x - y) - (x - y)
                         - / 2 * ulp beta fexp2 (x - y))).
  ring_simplify.
  replace (_ + _) with (round beta fexp1 Zceil (x - y) - (x - y)) by ring.
  apply Rle_lt_trans with y;
    [now apply round_round_minus_aux2_aux; try assumption; lia|].
  apply (Rlt_le_trans _ _ _ Ly).
  apply Rle_trans with (bpow (fexp1 (mag (x - y)) - 2));
    [now apply bpow_le|].
  replace (_ - 2)%Z with (fexp1 (mag (x - y)) - 1 - 1)%Z by ring.
  unfold Zminus at 1; rewrite bpow_plus.
  rewrite <- Rmult_minus_distr_l.
  rewrite Rmult_comm; apply Rmult_le_compat.
  +
 apply bpow_ge_0.
  +
 apply bpow_ge_0.
  +
 unfold Raux.bpow, Z.pow_pos; simpl.
    rewrite Zmult_1_r; apply Rinv_le; [lra|].
    now apply IZR_le.
  +
 rewrite 2!ulp_neq_0; try now apply Rgt_not_eq, Rgt_minus.
    unfold cexp.
    apply (Rplus_le_reg_r (bpow (fexp2 (mag (x - y))))); ring_simplify.
    apply Rle_trans with (2 * bpow (fexp1 (mag (x - y)) - 1)).
    *
 rewrite double.
      apply Rplus_le_compat_l.
      now apply bpow_le.
    *
 unfold Zminus; rewrite bpow_plus.
      rewrite Rmult_comm; rewrite Rmult_assoc.
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l; [now apply bpow_ge_0|].
      unfold Raux.bpow, Z.pow_pos; simpl.
      rewrite Zmult_1_r.
      apply IZR_le, Rinv_le in Hbeta.
      simpl in Hbeta.
      lra.
      apply Rlt_0_2.
Qed.

Lemma round_round_minus_aux3 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y <= x ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hyx Fx Fy.
assert (Px := Rlt_le_trans 0 y x Py Hyx).
unfold round_round_eq.
destruct (Req_dec y x) as [Hy|Hy].
-

  rewrite Hy; replace (x - x) with 0 by ring.
  rewrite round_0.
  +
 reflexivity.
  +
 now apply valid_rnd_N.
-

  assert (Hyx' : y < x); [lra|].
  destruct (Zle_or_lt (mag y) (fexp1 (mag x) - 2)) as [Hly|Hly].
  +

    destruct (Zle_or_lt (mag y) (fexp1 (mag (x - y)) - 2))
      as [Hly'|Hly'].
    *

      now apply round_round_minus_aux2.
    *

      {
 rewrite (round_generic beta fexp2).
        -
 reflexivity.
        -
 now apply valid_rnd_N.
        -
 assert (Hf1 : (fexp1 (mag (x - y)) - 1 <= mag y)%Z) by lia.
          now apply (round_round_minus_aux1 fexp1).
}
  +
 rewrite (round_generic beta fexp2).
    *
 reflexivity.
    *
 now apply valid_rnd_N.
    *
 assert (Hf1 : (fexp1 (mag x) - 1 <= mag y)%Z) by lia.
      now apply (round_round_minus_aux0 fexp1).
Qed.

Lemma round_round_minus_aux :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Nnx Nny Fx Fy.
unfold round_round_eq.
destruct (Req_dec x 0) as [Zx|Nzx].
-

  rewrite Zx; unfold Rminus; rewrite Rplus_0_l.
  do 3 rewrite round_N_opp.
  rewrite (round_generic beta fexp2).
  *
 reflexivity.
  *
 now apply valid_rnd_N.
  *
 apply (generic_inclusion_mag beta fexp1).
    destruct Hexp as (_,(_,(_,Hexp4))).
    now intros _; apply Hexp4; lia.
    exact Fy.
-

  destruct (Req_dec y 0) as [Zy|Nzy].
  +

    rewrite Zy; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
    rewrite (round_generic beta fexp2).
    *
 reflexivity.
    *
 now apply valid_rnd_N.
    *
 apply (generic_inclusion_mag beta fexp1).
      destruct Hexp as (_,(_,(_,Hexp4))).
      now intros _; apply Hexp4; lia.
      exact Fx.
  +

    assert (Px : 0 < x); [lra|].
    assert (Py : 0 < y); [lra|].
    destruct (Rlt_or_le x y) as [H|H].
    *

      apply Rlt_le in H.
      replace (x - y) with (- (y - x)) by ring.
      do 3 rewrite round_N_opp.
      apply Ropp_eq_compat.
      now apply round_round_minus_aux3.
    *

      now apply round_round_minus_aux3.
Qed.

Lemma round_round_plus :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold round_round_eq.
destruct (Rlt_or_le x 0) as [Sx|Sx]; destruct (Rlt_or_le y 0) as [Sy|Sy].
-

  replace (x + y) with (- (- x - y)); [|ring].
  do 3 rewrite round_N_opp.
  apply Ropp_eq_compat.
  assert (Px : 0 <= - x); [lra|].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fx.
  apply generic_format_opp in Fy.
  now apply round_round_plus_aux.
-

  replace (x + y) with (y - (- x)); [|ring].
  assert (Px : 0 <= - x); [lra|].
  apply generic_format_opp in Fx.
  now apply round_round_minus_aux.
-

  replace (x + y) with (x - (- y)); [|ring].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fy.
  now apply round_round_minus_aux.
-

  now apply round_round_plus_aux.
Qed.

Lemma round_round_minus :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold Rminus.
apply generic_format_opp in Fy.
now apply round_round_plus.
Qed.

Section Double_round_plus_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_plus_hyp :
  (2 * prec + 1 <= prec')%Z ->
  round_round_plus_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
intros Hprec.
unfold FLX_exp.
unfold round_round_plus_hyp; split; [|split; [|split]];
intros ex ey; try lia.
unfold Prec_gt_0 in prec_gt_0_.
lia.
Qed.

Theorem round_round_plus_FLX :
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Hprec x y Fx Fy.
apply round_round_plus.
-
 now apply FLX_exp_valid.
-
 now apply FLX_exp_valid.
-
 now apply FLX_round_round_plus_hyp.
-
 now apply generic_format_FLX.
-
 now apply generic_format_FLX.
Qed.

Theorem round_round_minus_FLX :
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Hprec x y Fx Fy.
apply round_round_minus.
-
 now apply FLX_exp_valid.
-
 now apply FLX_exp_valid.
-
 now apply FLX_round_round_plus_hyp.
-
 now apply generic_format_FLX.
-
 now apply generic_format_FLX.
Qed.

End Double_round_plus_FLX.

Section Double_round_plus_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_plus_hyp :
  (emin' <= emin)%Z -> (2 * prec + 1 <= prec')%Z ->
  round_round_plus_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof using prec_gt_0_.
intros Hemin Hprec.
unfold FLT_exp.
unfold round_round_plus_hyp; split; [|split; [|split]]; intros ex ey.
-
 generalize (Zmax_spec (ex + 1 - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
-
 generalize (Zmax_spec (ex - 1 - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
-
 unfold Prec_gt_0 in prec_gt_0_.
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
Qed.

Theorem round_round_plus_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_plus.
-
 now apply FLT_exp_valid.
-
 now apply FLT_exp_valid.
-
 now apply FLT_round_round_plus_hyp.
-
 now apply generic_format_FLT.
-
 now apply generic_format_FLT.
Qed.

Theorem round_round_minus_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_minus.
-
 now apply FLT_exp_valid.
-
 now apply FLT_exp_valid.
-
 now apply FLT_round_round_plus_hyp.
-
 now apply generic_format_FLT.
-
 now apply generic_format_FLT.
Qed.

End Double_round_plus_FLT.

Section Double_round_plus_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_plus_hyp :
  (emin' + prec' <= emin + 1)%Z -> (2 * prec + 1 <= prec')%Z ->
  round_round_plus_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof using prec_gt_0_ prec_gt_0_'.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in *.
unfold round_round_plus_hyp; split; [|split; [|split]]; intros ex ey.
-
 destruct (Z.ltb_spec (ex + 1 - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - 1 - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
Qed.

Theorem round_round_plus_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_plus.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_round_round_plus_hyp.
-
 now apply generic_format_FTZ.
-
 now apply generic_format_FTZ.
Qed.

Theorem round_round_minus_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_minus.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_round_round_plus_hyp.
-
 now apply generic_format_FTZ.
-
 now apply generic_format_FTZ.
Qed.

End Double_round_plus_FTZ.

Section Double_round_plus_radix_ge_3.

Definition round_round_plus_radix_ge_3_hyp fexp1 fexp2 :=
  (forall ex ey, (fexp1 (ex + 1) <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (fexp1 (ex - 1) + 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (fexp1 ex <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z).

Lemma round_round_plus_radix_ge_3_aux0 :
  forall (fexp1 fexp2 : Z -> Z), Valid_exp fexp1 ->
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  (0 < y)%R -> (y <= x)%R ->
  (fexp1 (mag x) <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof using .
intros fexp1 fexp2 Vfexp1 Hexp x y Py Hyx Hln Fx Fy.
assert (Px := Rlt_le_trans 0 y x Py Hyx).
assert (Nny : (0 <= y)%R); [now apply Rlt_le|].
destruct Hexp as (_,(Hexp2,(Hexp3,Hexp4))).
destruct (Z.le_gt_cases (mag y) (fexp1 (mag x))) as [Hle|Hgt].
-

  assert (Lxy : mag (x + y) = mag x :> Z);
  [now apply (mag_plus_separated fexp1)|].
  apply (round_round_plus_aux0_aux fexp1);
    [| |assumption|assumption]; rewrite Lxy.
  +
 now apply Hexp4; lia.
  +
 now apply Hexp3; lia.
-

  apply (round_round_plus_aux0_aux fexp1); [| |assumption|assumption].
  destruct (mag_plus_disj x y Py Hyx) as [Lxy|Lxy]; rewrite Lxy.
  +
 now apply Hexp4; lia.
  +
 apply Hexp2; apply (mag_le beta y x Py) in Hyx.
    replace (_ - _)%Z with (mag x : Z) by ring.
    lia.
  +
 destruct (mag_plus_disj x y Py Hyx) as [Lxy|Lxy]; rewrite Lxy.
    *
 now apply Hexp3; lia.
    *
 apply Hexp2.
      replace (_ - _)%Z with (mag x : Z) by ring.
      lia.
Qed.

Lemma round_round_plus_radix_ge_3_aux1 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= fexp1 (mag x) - 1)%Z ->
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Hly Fx.
assert (Lxy : mag (x + y) = mag x :> Z);
  [now apply (mag_plus_separated fexp1); [|apply Rlt_le| |lia]|].
destruct Hexp as (_,(_,(_,Hexp4))).
assert (Hf2 : (fexp2 (mag x) <= fexp1 (mag x))%Z);
  [now apply Hexp4; lia|].
assert (Bpow3 : bpow (- 1) <= / 3).
{
 unfold Raux.bpow, Z.pow_pos; simpl.
  rewrite Zmult_1_r.
  apply Rinv_le; [lra|].
  now apply IZR_le.
}
assert (P1 : (0 < 1)%Z) by lia.
unfold round_round_eq.
apply round_round_lt_mid.
-
 exact Vfexp1.
-
 exact Vfexp2.
-
 lra.
-
 now rewrite Lxy.
-
 rewrite Lxy.
  cut (fexp1 (mag x) < mag x)%Z.
lia.
  now apply mag_generic_gt; [|apply Rgt_not_eq|].
-
 unfold midp.
  apply (Rplus_lt_reg_r (- round beta fexp1 Zfloor (x + y))).
  apply (Rlt_le_trans _ _ _ (proj2 (round_round_plus_aux1_aux 1 P1 fexp1 x y Px
                                                               Py Hly Lxy Fx))).
  ring_simplify.
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold cexp; rewrite Lxy.
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
    [now apply bpow_gt_0|].
  bpow_simplify.
  apply (Rle_trans _ _ _ Bpow3); lra.
-
 rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold round, F2R, scaled_mantissa, cexp; simpl; rewrite Lxy.
  intro Hf2'.
  unfold midp.
  apply (Rplus_lt_reg_r (- round beta fexp1 Zfloor (x + y))); ring_simplify.
  rewrite <- Rmult_minus_distr_l.
  apply (Rlt_le_trans _ _ _ (proj2 (round_round_plus_aux1_aux 1 P1 fexp1 x y Px
                                                               Py Hly Lxy Fx))).
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold cexp; rewrite Lxy.
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
    [now apply bpow_gt_0|].
  rewrite (Rmult_assoc (/ 2)).
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  apply (Rle_trans _ _ _ Bpow3).
  apply Rle_trans with (/ 2 * (2 / 3)); [lra|].
  apply Rmult_le_compat_l; [lra|].
  apply (Rplus_le_reg_r (- 1)); ring_simplify.
  replace (_ - _) with (- (/ 3)) by lra.
  apply Ropp_le_contravar.
  now apply Rle_trans with (bpow (- 1)); [apply bpow_le; lia|].
Qed.

Lemma round_round_plus_radix_ge_3_aux2 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y <= x ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hyx Fx Fy.
assert (Px := Rlt_le_trans 0 y x Py Hyx).
unfold round_round_eq.
destruct (Zle_or_lt (mag y) (fexp1 (mag x) - 1)) as [Hly|Hly].
-

  now apply round_round_plus_radix_ge_3_aux1.
-

  rewrite (round_generic beta fexp2).
  +
 reflexivity.
  +
 now apply valid_rnd_N.
  +
 assert (Hf1 : (fexp1 (mag x) <= mag y)%Z) by lia.
    now apply (round_round_plus_radix_ge_3_aux0 fexp1).
Qed.

Lemma round_round_plus_radix_ge_3_aux :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Nnx Nny Fx Fy.
unfold round_round_eq.
destruct (Req_dec x 0) as [Zx|Nzx].
-

  destruct Hexp as (_,(_,(_,Hexp4))).
  rewrite Zx; rewrite Rplus_0_l.
  rewrite (round_generic beta fexp2).
  +
 reflexivity.
  +
 now apply valid_rnd_N.
  +
 apply (generic_inclusion_mag beta fexp1).
    now intros _; apply Hexp4; lia.
    exact Fy.
-

  destruct (Req_dec y 0) as [Zy|Nzy].
  +

    destruct Hexp as (_,(_,(_,Hexp4))).
    rewrite Zy; rewrite Rplus_0_r.
    rewrite (round_generic beta fexp2).
    *
 reflexivity.
    *
 now apply valid_rnd_N.
    *
 apply (generic_inclusion_mag beta fexp1).
      now intros _; apply Hexp4; lia.
      exact Fx.
  +

    assert (Px : 0 < x); [lra|].
    assert (Py : 0 < y); [lra|].
    destruct (Rlt_or_le x y) as [H|H].
    *

      apply Rlt_le in H.
      rewrite Rplus_comm.
      now apply round_round_plus_radix_ge_3_aux2.
    *
 now apply round_round_plus_radix_ge_3_aux2.
Qed.

Lemma round_round_minus_radix_ge_3_aux0 :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (fexp1 (mag x) <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof using .
intros fexp1 fexp2 Hexp x y Py Hyx Hln Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hyx).
destruct Hexp as (Hexp1,(_,(Hexp3,Hexp4))).
assert (Lyx : (mag y <= mag x)%Z);
  [now apply mag_le; [|apply Rlt_le]|].
destruct (Z.lt_ge_cases (mag x - 2) (mag y)) as [Hlt|Hge].
-

  assert (Hor : (mag y = mag x :> Z) \/ (mag y = mag x - 1 :> Z)%Z) by lia.
  destruct Hor as [Heq|Heqm1].
  +

    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    *
 apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
    *
 rewrite Heq.
      apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
  +

    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    *
 apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
    *
 rewrite Heqm1.
      apply Hexp4.
      apply Zplus_le_compat_r.
      now apply mag_minus.
-

  destruct (mag_minus_disj x y Px Py Hge) as [Lxmy|Lxmy].
  +

    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    *
 apply Hexp4.
      lia.
    *
 now rewrite Lxmy; apply Hexp3.
  +

    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy];
    rewrite Lxmy.
    *
 apply Hexp1.
      replace (_ + _)%Z with (mag x : Z); [|ring].
      now apply Z.le_trans with (mag y).
    *
 apply Hexp1.
      now replace (_ + _)%Z with (mag x : Z); [|ring].
Qed.

Lemma round_round_minus_radix_ge_3_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag (x - y)) <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2  Hexp x y Py Hyx Hln Hln' Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hyx).
destruct Hexp as (Hexp1,(Hexp2,(Hexp3,Hexp4))).
assert (Lyx : (mag y <= mag x)%Z);
  [now apply mag_le; [|apply Rlt_le]|].
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
-
 apply Z.le_trans with (fexp1 (mag (x - y))).
  +
 apply Hexp4; lia.
  +
 lia.
-
 now apply Hexp3.
Qed.

Lemma round_round_minus_radix_ge_3_aux2 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp1 (mag x) - 1)%Z ->
  (mag y <= fexp1 (mag (x - y)) - 1)%Z ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hxy Hly Hly' Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hxy).
destruct Hexp as (_,(_,(_,Hexp4))).
assert (Hf2 : (fexp2 (mag x) <= fexp1 (mag x))%Z);
  [now apply Hexp4; lia|].
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Bpow3 : bpow (- 1) <= / 3).
{
 unfold Raux.bpow, Z.pow_pos; simpl.
  rewrite Zmult_1_r.
  apply Rinv_le; [lra|].
  now apply IZR_le.
}
assert (Ly : y < bpow (mag y)).
{
 apply Rabs_lt_inv.
  apply bpow_mag_gt.
}
unfold round_round_eq.
apply round_round_gt_mid.
-
 exact Vfexp1.
-
 exact Vfexp2.
-
 lra.
-
 apply Hexp4; lia.
-
 cut (fexp1 (mag (x - y)) < mag (x - y))%Z.
lia.
  apply (valid_exp_large fexp1 (mag x - 1)).
  +
 apply (valid_exp_large fexp1 (mag y)); [|lia].
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
  +
 now apply mag_minus_lb; [| |lia].
-
 unfold midp'.
  apply (Rplus_lt_reg_r (/ 2 * ulp beta fexp1 (x - y) - (x - y))).
  ring_simplify.
  replace (_ + _) with (round beta fexp1 Zceil (x - y) - (x - y)) by ring.
  apply Rlt_le_trans with (bpow (fexp1 (mag (x - y)) - 1)).
  +
 apply Rle_lt_trans with y;
    [now apply round_round_minus_aux2_aux|].
    apply (Rlt_le_trans _ _ _ Ly).
    now apply bpow_le.
  +
 rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rgt_minus].
    unfold cexp.
    unfold Zminus at 1; rewrite bpow_plus.
    rewrite Rmult_comm.
    apply Rmult_le_compat_r; [now apply bpow_ge_0|].
    unfold Raux.bpow, Z.pow_pos; simpl.
    rewrite Zmult_1_r; apply Rinv_le; [lra|].
    now apply IZR_le; lia.
-
 intro Hf2'.
  unfold midp'.
  apply (Rplus_lt_reg_r (/ 2 * (ulp beta fexp1 (x - y)
                                - ulp beta fexp2 (x - y)) - (x - y))).
  ring_simplify; rewrite <- Rmult_minus_distr_l.
  replace (_ + _) with (round beta fexp1 Zceil (x - y) - (x - y)) by ring.
  apply Rle_lt_trans with y;
    [now apply round_round_minus_aux2_aux|].
  apply (Rlt_le_trans _ _ _ Ly).
  apply Rle_trans with (bpow (fexp1 (mag (x - y)) - 1));
    [now apply bpow_le|].
  rewrite 2!ulp_neq_0; try now apply Rgt_not_eq, Rgt_minus.
  unfold cexp.
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag (x - y)))));
    [now apply bpow_gt_0|].
  rewrite Rmult_assoc.
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  apply Rle_trans with (/ 3).
  +
 unfold Raux.bpow, Z.pow_pos; simpl.
    rewrite Zmult_1_r; apply Rinv_le; [lra|].
    now apply IZR_le.
  +
 replace (/ 3) with (/ 2 * (2 / 3)) by field.
    apply Rmult_le_compat_l; [lra|].
    apply (Rplus_le_reg_r (- 1)); ring_simplify.
    replace (_ - _) with (- / 3) by field.
    apply Ropp_le_contravar.
    apply Rle_trans with (bpow (- 1)).
    *
 apply bpow_le; lia.
    *
 unfold Raux.bpow, Z.pow_pos; simpl.
      rewrite Zmult_1_r; apply Rinv_le; [lra|].
      now apply IZR_le.
Qed.

Lemma round_round_minus_radix_ge_3_aux3 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y <= x ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hyx Fx Fy.
assert (Px := Rlt_le_trans 0 y x Py Hyx).
unfold round_round_eq.
destruct (Req_dec y x) as [Hy|Hy].
-

  rewrite Hy; replace (x - x) with 0 by ring.
  rewrite round_0.
  +
 reflexivity.
  +
 now apply valid_rnd_N.
-

  assert (Hyx' : y < x); [lra|].
  destruct (Zle_or_lt (mag y) (fexp1 (mag x) - 1)) as [Hly|Hly].
  +

    destruct (Zle_or_lt (mag y) (fexp1 (mag (x - y)) - 1))
      as [Hly'|Hly'].
    *

      now apply round_round_minus_radix_ge_3_aux2.
    *

      {
 rewrite (round_generic beta fexp2).
        -
 reflexivity.
        -
 now apply valid_rnd_N.
        -
 assert (Hf1 : (fexp1 (mag (x - y)) <= mag y)%Z) by lia.
          now apply (round_round_minus_radix_ge_3_aux1 fexp1).
}
  +
 rewrite (round_generic beta fexp2).
    *
 reflexivity.
    *
 now apply valid_rnd_N.
    *
 assert (Hf1 : (fexp1 (mag x) <= mag y)%Z) by lia.
      now apply (round_round_minus_radix_ge_3_aux0 fexp1).
Qed.

Lemma round_round_minus_radix_ge_3_aux :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Nnx Nny Fx Fy.
unfold round_round_eq.
destruct (Req_dec x 0) as [Zx|Nzx].
-

  rewrite Zx; unfold Rminus; rewrite Rplus_0_l.
  do 3 rewrite round_N_opp.
  rewrite (round_generic beta fexp2).
  *
 reflexivity.
  *
 now apply valid_rnd_N.
  *
 apply (generic_inclusion_mag beta fexp1).
    destruct Hexp as (_,(_,(_,Hexp4))).
    now intros _; apply Hexp4; lia.
    exact Fy.
-

  destruct (Req_dec y 0) as [Zy|Nzy].
  +

    rewrite Zy; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
    rewrite (round_generic beta fexp2).
    *
 reflexivity.
    *
 now apply valid_rnd_N.
    *
 apply (generic_inclusion_mag beta fexp1).
      destruct Hexp as (_,(_,(_,Hexp4))).
      now intros _; apply Hexp4; lia.
      exact Fx.
  +

    assert (Px : 0 < x); [lra|].
    assert (Py : 0 < y); [lra|].
    destruct (Rlt_or_le x y) as [H|H].
    *

      apply Rlt_le in H.
      replace (x - y) with (- (y - x)) by ring.
      do 3 rewrite round_N_opp.
      apply Ropp_eq_compat.
      now apply round_round_minus_radix_ge_3_aux3.
    *

      now apply round_round_minus_radix_ge_3_aux3.
Qed.

Lemma round_round_plus_radix_ge_3 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold round_round_eq.
destruct (Rlt_or_le x 0) as [Sx|Sx]; destruct (Rlt_or_le y 0) as [Sy|Sy].
-

  replace (x + y) with (- (- x - y)); [|ring].
  do 3 rewrite round_N_opp.
  apply Ropp_eq_compat.
  assert (Px : 0 <= - x); [lra|].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fx.
  apply generic_format_opp in Fy.
  now apply round_round_plus_radix_ge_3_aux.
-

  replace (x + y) with (y - (- x)); [|ring].
  assert (Px : 0 <= - x); [lra|].
  apply generic_format_opp in Fx.
  now apply round_round_minus_radix_ge_3_aux.
-

  replace (x + y) with (x - (- y)); [|ring].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fy.
  now apply round_round_minus_radix_ge_3_aux.
-

  now apply round_round_plus_radix_ge_3_aux.
Qed.

Lemma round_round_minus_radix_ge_3 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold Rminus.
apply generic_format_opp in Fy.
now apply round_round_plus_radix_ge_3.
Qed.

Section Double_round_plus_radix_ge_3_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_plus_radix_ge_3_hyp :
  (2 * prec <= prec')%Z ->
  round_round_plus_radix_ge_3_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
intros Hprec.
unfold FLX_exp.
unfold round_round_plus_radix_ge_3_hyp; split; [|split; [|split]];
intros ex ey; try lia.
unfold Prec_gt_0 in prec_gt_0_.
lia.
Qed.

Theorem round_round_plus_radix_ge_3_FLX :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hprec x y Fx Fy.
apply round_round_plus_radix_ge_3.
-
 exact Hbeta.
-
 now apply FLX_exp_valid.
-
 now apply FLX_exp_valid.
-
 now apply FLX_round_round_plus_radix_ge_3_hyp.
-
 now apply generic_format_FLX.
-
 now apply generic_format_FLX.
Qed.

Theorem round_round_minus_radix_ge_3_FLX :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hprec x y Fx Fy.
apply round_round_minus_radix_ge_3.
-
 exact Hbeta.
-
 now apply FLX_exp_valid.
-
 now apply FLX_exp_valid.
-
 now apply FLX_round_round_plus_radix_ge_3_hyp.
-
 now apply generic_format_FLX.
-
 now apply generic_format_FLX.
Qed.

End Double_round_plus_radix_ge_3_FLX.

Section Double_round_plus_radix_ge_3_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_plus_radix_ge_3_hyp :
  (emin' <= emin)%Z -> (2 * prec <= prec')%Z ->
  round_round_plus_radix_ge_3_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof using prec_gt_0_.
intros Hemin Hprec.
unfold FLT_exp.
unfold round_round_plus_radix_ge_3_hyp; split; [|split; [|split]]; intros ex ey.
-
 generalize (Zmax_spec (ex + 1 - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
-
 generalize (Zmax_spec (ex - 1 - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
-
 unfold Prec_gt_0 in prec_gt_0_.
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
Qed.

Theorem round_round_plus_radix_ge_3_FLT :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_plus_radix_ge_3.
-
 exact Hbeta.
-
 now apply FLT_exp_valid.
-
 now apply FLT_exp_valid.
-
 now apply FLT_round_round_plus_radix_ge_3_hyp.
-
 now apply generic_format_FLT.
-
 now apply generic_format_FLT.
Qed.

Theorem round_round_minus_radix_ge_3_FLT :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_minus_radix_ge_3.
-
 exact Hbeta.
-
 now apply FLT_exp_valid.
-
 now apply FLT_exp_valid.
-
 now apply FLT_round_round_plus_radix_ge_3_hyp.
-
 now apply generic_format_FLT.
-
 now apply generic_format_FLT.
Qed.

End Double_round_plus_radix_ge_3_FLT.

Section Double_round_plus_radix_ge_3_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_plus_radix_ge_3_hyp :
  (emin' + prec' <= emin + 1)%Z -> (2 * prec <= prec')%Z ->
  round_round_plus_radix_ge_3_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof using prec_gt_0_ prec_gt_0_'.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in *.
unfold round_round_plus_radix_ge_3_hyp; split; [|split; [|split]]; intros ex ey.
-
 destruct (Z.ltb_spec (ex + 1 - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - 1 - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
Qed.

Theorem round_round_plus_radix_ge_3_FTZ :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_plus_radix_ge_3.
-
 exact Hbeta.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_round_round_plus_radix_ge_3_hyp.
-
 now apply generic_format_FTZ.
-
 now apply generic_format_FTZ.
Qed.

Theorem round_round_minus_radix_ge_3_FTZ :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_minus_radix_ge_3.
-
 exact Hbeta.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_round_round_plus_radix_ge_3_hyp.
-
 now apply generic_format_FTZ.
-
 now apply generic_format_FTZ.
Qed.

End Double_round_plus_radix_ge_3_FTZ.

End Double_round_plus_radix_ge_3.

End Double_round_plus.

Lemma round_round_mid_cases :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  (Rabs (x - midp fexp1 x) <= / 2 * (ulp beta fexp2 x) ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1.
unfold round_round_eq, midp.
set (rd := round beta fexp1 Zfloor x).
set (u1 := ulp beta fexp1 x).
set (u2 := ulp beta fexp2 x).
intros Cmid.
destruct (generic_format_EM beta fexp1 x) as [Fx|Nfx].
-

  rewrite (round_generic beta fexp2); [reflexivity|now apply valid_rnd_N|].
  now apply (generic_inclusion_mag beta fexp1); [lia|].
-

  assert (Hceil : round beta fexp1 Zceil x = rd + u1);
  [now apply round_UP_DN_ulp|].
  assert (Hf2' : (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z) by lia.
  destruct (Rlt_or_le (x - rd) (/ 2 * (u1 - u2))).
  +

    apply round_round_lt_mid_further_place; try assumption.
    unfold midp.
fold rd; fold u1; fold u2.
    apply (Rplus_lt_reg_r (- rd)); ring_simplify.
    now rewrite <- Rmult_minus_distr_l.
  +

    {
 destruct (Rlt_or_le (/ 2 * (u1 + u2)) (x - rd)).
      -

        assert (round beta fexp1 Zceil x - x
                < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
        {
 rewrite Hceil; fold u1; fold u2.
          lra.
}
        apply round_round_gt_mid_further_place; try assumption.
        unfold midp'; lra.
      -

        apply Cmid, Rabs_le; split; lra.
}
Qed.

Section Double_round_sqrt.

Definition round_round_sqrt_hyp fexp1 fexp2 :=
  (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex))%Z)
  /\ (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex - 1))%Z)
  /\ (forall ex, (fexp1 (2 * ex) < 2 * ex)%Z ->
                 (fexp2 ex + ex <= 2 * fexp1 ex - 2)%Z).

Lemma mag_sqrt_disj :
  forall x,
  0 < x ->
  (mag x = 2 * mag (sqrt x) - 1 :> Z)%Z
  \/ (mag x = 2 * mag (sqrt x) :> Z)%Z.
Proof using .
intros x Px.
rewrite (mag_sqrt beta x Px).
generalize (Zdiv2_odd_eqn (mag x + 1)).
destruct Z.odd ; intros ; lia.
Qed.

Lemma round_round_sqrt_aux :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  round_round_sqrt_hyp fexp1 fexp2 ->
  forall x,
  0 < x ->
  (fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1)%Z ->
  generic_format beta fexp1 x ->
  / 2 * ulp beta fexp2 (sqrt x) < Rabs (sqrt x - midp fexp1 (sqrt x)).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 Hexp x Px Hf2 Fx.
assert (Hbeta : (2 <= beta)%Z).
{
 destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
}
set (a := round beta fexp1 Zfloor (sqrt x)).
set (u1 := bpow (fexp1 (mag (sqrt x)))).
set (u2 := bpow (fexp2 (mag (sqrt x)))).
set (b := / 2 * (u1 - u2)).
set (b' := / 2 * (u1 + u2)).
unfold midp; rewrite 2!ulp_neq_0; try now apply Rgt_not_eq, sqrt_lt_R0.
apply Rnot_ge_lt; intro H; apply Rge_le in H.
assert (Fa : generic_format beta fexp1 a).
{
 unfold a.
  apply generic_format_round.
  -
 exact Vfexp1.
  -
 now apply valid_rnd_DN.
}
revert Fa; revert Fx.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (ma := Ztrunc (a * bpow (- fexp1 (mag a)))).
intros Fx Fa.
assert (Nna : 0 <= a).
{
 rewrite <- (round_0 beta fexp1 Zfloor).
  unfold a; apply round_le.
  -
 exact Vfexp1.
  -
 now apply valid_rnd_DN.
  -
 apply sqrt_pos.
}
assert (Phu1 : 0 < / 2 * u1).
{
 apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
}
assert (Phu2 : 0 < / 2 * u2).
{
 apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
}
assert (Pb : 0 < b).
{
 unfold b.
  rewrite <- (Rmult_0_r (/ 2)).
  apply Rmult_lt_compat_l; [lra|].
  apply Rlt_Rminus.
  unfold u2, u1.
  apply bpow_lt.
  lia.
}
assert (Pb' : 0 < b').
{
 now unfold b'; rewrite Rmult_plus_distr_l; apply Rplus_lt_0_compat.
}
assert (Hr : sqrt x <= a + b').
{
 unfold b'; apply (Rplus_le_reg_r (- / 2 * u1 - a)); ring_simplify.
  replace (_ - _) with (sqrt x - (a + / 2 * u1)) by ring.
  now apply Rabs_le_inv.
}
assert (Hl : a + b <= sqrt x).
{
 unfold b; apply (Rplus_le_reg_r (- / 2 * u1 - a)); ring_simplify.
  replace (_ + sqrt _) with (sqrt x - (a + / 2 * u1)) by ring.
  rewrite Ropp_mult_distr_l_reverse.
  now apply Rabs_le_inv in H; destruct H.
}
assert (Hf1 : (2 * fexp1 (mag (sqrt x)) <= fexp1 (mag (x)))%Z);
  [destruct (mag_sqrt_disj x Px) as [H'|H']; rewrite H'; apply Hexp|].
assert (Hlx : (fexp1 (2 * mag (sqrt x)) < 2 * mag (sqrt x))%Z).
{
 destruct (mag_sqrt_disj x Px) as [Hlx|Hlx].
  -
 apply (valid_exp_large fexp1 (mag x)); [|lia].
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
  -
 rewrite <- Hlx.
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
}
assert (Hsl : a * a + u1 * a - u2 * a + b * b <= x).
{
 replace (_ + _) with ((a + b) * (a + b)); [|now unfold b; field].
  rewrite <- sqrt_def; [|now apply Rlt_le].
  assert (H' : 0 <= a + b); [now apply Rlt_le, Rplus_le_lt_0_compat|].
  now apply Rmult_le_compat.
}
assert (Hsr : x <= a * a + u1 * a + u2 * a + b' * b').
{
 replace (_ + _) with ((a + b') * (a + b')); [|now unfold b'; field].
  rewrite <- (sqrt_def x); [|now apply Rlt_le].
  assert (H' : 0 <= sqrt x); [now apply sqrt_pos|].
  now apply Rmult_le_compat.
}
destruct (Req_dec a 0) as [Za|Nza].
-

  apply (Rlt_irrefl 0).
  apply Rlt_le_trans with (b * b); [now apply Rmult_lt_0_compat|].
  apply Rle_trans with x.
  +
 revert Hsl; unfold Rminus; rewrite Za; do 3 rewrite Rmult_0_r.
    now rewrite Ropp_0; do 3 rewrite Rplus_0_l.
  +
 rewrite Fx.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_0_l; bpow_simplify.
    unfold mx.
    rewrite Ztrunc_floor;
      [|now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]].
    apply Req_le, IZR_eq.
    apply Zfloor_imp.
    split; [now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]|simpl].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite Rmult_1_l; bpow_simplify.
    apply Rlt_le_trans with (bpow (2 * fexp1 (mag (sqrt x))));
      [|now apply bpow_le].
    change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l; rewrite Zmult_1_l.
    rewrite bpow_plus.
    rewrite <- (sqrt_def x) at 1; [|now apply Rlt_le].
    assert (sqrt x < bpow (fexp1 (mag (sqrt x))));
      [|now apply Rmult_lt_compat; [apply sqrt_pos|apply sqrt_pos| |]].
    apply (Rle_lt_trans _ _ _ Hr); rewrite Za; rewrite Rplus_0_l.
    unfold b'; change (bpow _) with u1.
    apply Rlt_le_trans with (/ 2 * (u1 + u1)); [|lra].
    apply Rmult_lt_compat_l; [lra|]; apply Rplus_lt_compat_l.
    unfold u2, u1, ulp, cexp; apply bpow_lt; lia.
-

  assert (Pa : 0 < a); [lra|].
  assert (Hla : (mag a = mag (sqrt x) :> Z)).
  {
 unfold a; apply mag_DN.
    -
 exact Vfexp1.
    -
 now fold a.
}
  assert (Hl' : 0 < - (u2 * a) + b * b).
  {
 apply (Rplus_lt_reg_r (u2 * a)); ring_simplify.
    unfold b; ring_simplify.
    apply (Rplus_lt_reg_r (/ 2 * u2 * u1)); field_simplify.
    replace (_ / 2) with (u2 * (a + / 2 * u1)) by field.
    replace (_ / 8) with (/ 4 * (u2 ^ 2 + u1 ^ 2)) by field.
    apply Rlt_le_trans with (u2 * bpow (mag (sqrt x))).
    -
 apply Rmult_lt_compat_l; [now unfold u2, ulp; apply bpow_gt_0|].
      unfold u1; rewrite <- Hla.
      apply Rlt_le_trans with (a + bpow (fexp1 (mag a))).
      +
 apply Rplus_lt_compat_l.
        rewrite <- (Rmult_1_l (bpow _)) at 2.
        apply Rmult_lt_compat_r; [apply bpow_gt_0|lra].
      +
 apply Rle_trans with (a+ ulp beta fexp1 a).
        right; now rewrite ulp_neq_0.
        apply (id_p_ulp_le_bpow _ _ _ _ Pa Fa).
        apply Rabs_lt_inv, bpow_mag_gt.
    -
 apply Rle_trans with (bpow (- 2) * u1 ^ 2).
      +
 unfold pow; rewrite Rmult_1_r.
        unfold u1, u2, ulp, cexp; bpow_simplify; apply bpow_le.
        now apply Hexp.
      +
 apply Rmult_le_compat.
        *
 apply bpow_ge_0.
        *
 apply pow2_ge_0.
        *
 unfold Raux.bpow, Z.pow_pos; simpl; rewrite Zmult_1_r.
          apply Rinv_le; [lra|].
          change 4%Z with (2 * 2)%Z; apply IZR_le, Zmult_le_compat; lia.
        *
 rewrite <- (Rplus_0_l (u1 ^ 2)) at 1; apply Rplus_le_compat_r.
          apply pow2_ge_0.
}
  assert (Hr' : x <= a * a + u1 * a).
  {
 rewrite Hla in Fa.
    rewrite <- Rmult_plus_distr_r.
    unfold u1, ulp, cexp.
    rewrite <- (Rmult_1_l (bpow _)); rewrite Fa; rewrite <- Rmult_plus_distr_r.
    rewrite <- Rmult_assoc; rewrite (Rmult_comm _ (IZR ma)).
    rewrite <- (Rmult_assoc (IZR ma)); bpow_simplify.
    apply (Rmult_le_reg_r (bpow (- 2 * fexp1 (mag (sqrt x)))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite Fx at 1; bpow_simplify.
    rewrite <- IZR_Zpower by lia.
    rewrite <- plus_IZR, <- 2!mult_IZR.
    apply IZR_le, Zlt_succ_le, lt_IZR.
    unfold Z.succ; rewrite plus_IZR; do 2 rewrite mult_IZR; rewrite plus_IZR.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (2 * fexp1 (mag (sqrt x)))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite <- Fx.
    change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l; rewrite Zmult_1_l.
    rewrite bpow_plus; simpl.
    replace (_ * _) with (a * a + u1 * a + u1 * u1);
      [|unfold u1, ulp, cexp; rewrite Fa; ring].
    apply (Rle_lt_trans _ _ _ Hsr).
    rewrite Rplus_assoc; apply Rplus_lt_compat_l.
    apply (Rplus_lt_reg_r (- b' * b' + / 2 * u1 * u2)); ring_simplify.
    replace (_ + _) with ((a + / 2 * u1) * u2) by ring.
    apply Rlt_le_trans with (bpow (mag (sqrt x)) * u2).
    -
 apply Rmult_lt_compat_r; [now unfold u2, ulp; apply bpow_gt_0|].
      apply Rlt_le_trans with (a + u1); [lra|].
      unfold u1; fold (cexp beta fexp1 (sqrt x)).
      rewrite <- cexp_DN; [|exact Vfexp1|exact Pa]; fold a.
      rewrite <- ulp_neq_0; trivial.
      apply id_p_ulp_le_bpow.
      +
 exact Pa.
      +
 now apply round_DN_pt.
      +
 apply Rle_lt_trans with (sqrt x).
        *
 now apply round_DN_pt.
        *
 apply Rabs_lt_inv.
          apply bpow_mag_gt.
    -
 apply Rle_trans with (/ 2 * u1 ^ 2).
      +
 apply Rle_trans with (bpow (- 2) * u1 ^ 2).
        *
 unfold pow; rewrite Rmult_1_r.
          unfold u2, u1, ulp, cexp.
          bpow_simplify.
          apply bpow_le.
          rewrite Zplus_comm.
          now apply Hexp.
        *
 apply Rmult_le_compat_r; [now apply pow2_ge_0|].
          unfold Raux.bpow; simpl; unfold Z.pow_pos; simpl.
          rewrite Zmult_1_r.
          apply Rinv_le; [lra|].
          apply IZR_le.
          rewrite <- (Zmult_1_l 2).
          apply Zmult_le_compat; lia.
      +
 assert (u2 ^ 2 < u1 ^ 2); [|unfold b'; lra].
        unfold pow; do 2 rewrite Rmult_1_r.
        assert (H' : 0 <= u2); [unfold u2, ulp; apply bpow_ge_0|].
        assert (u2 < u1); [|now apply Rmult_lt_compat].
        unfold u1, u2, ulp, cexp; apply bpow_lt; lia.
}
  apply (Rlt_irrefl (a * a + u1 * a)).
  apply Rlt_le_trans with (a * a + u1 * a - u2 * a + b * b).
  +
 rewrite <- (Rplus_0_r (a * a + _)) at 1.
    unfold Rminus; rewrite (Rplus_assoc _ _ (b * b)).
    now apply Rplus_lt_compat_l.
  +
 now apply Rle_trans with x.
Qed.

Lemma round_round_sqrt :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_sqrt_hyp fexp1 fexp2 ->
  forall x,
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (sqrt x).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x Fx.
unfold round_round_eq.
destruct (Rle_or_lt x 0) as [Npx|Px].
-

  rewrite (sqrt_neg _ Npx).
  now rewrite round_0; [|apply valid_rnd_N].
-

  assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; try assumption; lra|].
  assert (Hfsx : (fexp1 (mag (sqrt x)) < mag (sqrt x))%Z).
  {
 destruct (Rle_or_lt x 1) as [Hx|Hx].
    -

      apply (valid_exp_large fexp1 (mag x)); [exact Hfx|].
      apply mag_le; [exact Px|].
      rewrite <- (sqrt_def x) at 1; [|lra].
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l.
      +
 apply sqrt_pos.
      +
 rewrite <- sqrt_1.
        now apply sqrt_le_1_alt.
    -

      generalize ((proj1 (proj2 Hexp)) 1%Z).
      replace (_ - 1)%Z with 1%Z by ring.
      intro Hexp10.
      assert (Hf0 : (fexp1 1 < 1)%Z) by lia.
      clear Hexp10.
      apply (valid_exp_large fexp1 1); [exact Hf0|].
      apply mag_ge_bpow.
      rewrite Zeq_minus; [|reflexivity].
      unfold Raux.bpow; simpl.
      apply Rabs_ge; right.
      rewrite <- sqrt_1.
      apply sqrt_le_1_alt.
      now apply Rlt_le.
}
  assert (Hf2 : (fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1)%Z).
  {
 assert (H : (fexp1 (2 * mag (sqrt x)) < 2 * mag (sqrt x))%Z).
    {
 destruct (mag_sqrt_disj x Px) as [Hlx|Hlx].
      -
 apply (valid_exp_large fexp1 (mag x)); [|lia].
        now apply mag_generic_gt; [|apply Rgt_not_eq|].
      -
 rewrite <- Hlx.
        now apply mag_generic_gt; [|apply Rgt_not_eq|].
}
    generalize ((proj2 (proj2 Hexp)) (mag (sqrt x)) H).
    lia.
}
  apply round_round_mid_cases.
  +
 exact Vfexp1.
  +
 exact Vfexp2.
  +
 now apply sqrt_lt_R0.
  +
 lia.
  +
 lia.
  +
 intros Hmid; exfalso; apply (Rle_not_lt _ _ Hmid).
    apply (round_round_sqrt_aux fexp1 fexp2 Vfexp1 Vfexp2 Hexp x Px Hf2 Fx).
Qed.

Section Double_round_sqrt_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_sqrt_hyp :
  (2 * prec + 2 <= prec')%Z ->
  round_round_sqrt_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
intros Hprec.
unfold FLX_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_sqrt_hyp; split; [|split]; intro ex; lia.
Qed.

Theorem round_round_sqrt_FLX :
  forall choice1 choice2,
  (2 * prec + 2 <= prec')%Z ->
  forall x,
  FLX_format beta prec x ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (sqrt x).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Hprec x Fx.
apply round_round_sqrt.
-
 now apply FLX_exp_valid.
-
 now apply FLX_exp_valid.
-
 now apply FLX_round_round_sqrt_hyp.
-
 now apply generic_format_FLX.
Qed.

End Double_round_sqrt_FLX.

Section Double_round_sqrt_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_sqrt_hyp :
  (emin <= 0)%Z ->
  ((emin' <= emin - prec - 2)%Z
   \/ (2 * emin' <= emin - 4 * prec - 2)%Z) ->
  (2 * prec + 2 <= prec')%Z ->
  round_round_sqrt_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof using prec_gt_0_.
intros Hemin Heminprec Hprec.
unfold FLT_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_sqrt_hyp; split; [|split]; intros ex.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (2 * ex - prec) emin).
  lia.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (2 * ex - 1 - prec) emin).
  lia.
-
 generalize (Zmax_spec (2 * ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ex - prec) emin).
  lia.
Qed.

Theorem round_round_sqrt_FLT :
  forall choice1 choice2,
  (emin <= 0)%Z ->
  ((emin' <= emin - prec - 2)%Z
   \/ (2 * emin' <= emin - 4 * prec - 2)%Z) ->
  (2 * prec + 2 <= prec')%Z ->
  forall x,
  FLT_format beta emin prec x ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Hemin Heminprec Hprec x Fx.
apply round_round_sqrt.
-
 now apply FLT_exp_valid.
-
 now apply FLT_exp_valid.
-
 now apply FLT_round_round_sqrt_hyp.
-
 now apply generic_format_FLT.
Qed.

End Double_round_sqrt_FLT.

Section Double_round_sqrt_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_sqrt_hyp :
  (2 * (emin' + prec') <= emin + prec <= 1)%Z ->
  (2 * prec + 2 <= prec')%Z ->
  round_round_sqrt_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof using prec_gt_0_.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in *.
unfold round_round_sqrt_hyp; split; [|split]; intros ex.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (2 * ex - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (2 * ex - 1 - prec) emin);
  lia.
-
 intro H.
  destruct (Zle_or_lt emin (2 * ex - prec)) as [H'|H'].
  +
 destruct (Z.ltb_spec (ex - prec') emin');
    destruct (Z.ltb_spec (ex - prec) emin);
    lia.
  +
 exfalso.
    rewrite (Zlt_bool_true _ _ H') in H.
    lia.
Qed.

Theorem round_round_sqrt_FTZ :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (2 * (emin' + prec') <= emin + prec <= 1)%Z ->
  (2 * prec + 2 <= prec')%Z ->
  forall x,
  FTZ_format beta emin prec x ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hemin Hprec x Fx.
apply round_round_sqrt.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_round_round_sqrt_hyp.
-
 now apply generic_format_FTZ.
Qed.

End Double_round_sqrt_FTZ.

Section Double_round_sqrt_radix_ge_4.

Definition round_round_sqrt_radix_ge_4_hyp fexp1 fexp2 :=
  (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex))%Z)
  /\ (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex - 1))%Z)
  /\ (forall ex, (fexp1 (2 * ex) < 2 * ex)%Z ->
                 (fexp2 ex + ex <= 2 * fexp1 ex - 1)%Z).

Lemma round_round_sqrt_radix_ge_4_aux :
  (4 <= beta)%Z ->
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  round_round_sqrt_radix_ge_4_hyp fexp1 fexp2 ->
  forall x,
  0 < x ->
  (fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1)%Z ->
  generic_format beta fexp1 x ->
  / 2 * ulp beta fexp2 (sqrt x) < Rabs (sqrt x - midp fexp1 (sqrt x)).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 Hexp x Px Hf2 Fx.
set (a := round beta fexp1 Zfloor (sqrt x)).
set (u1 := bpow (fexp1 (mag (sqrt x)))).
set (u2 := bpow (fexp2 (mag (sqrt x)))).
set (b := / 2 * (u1 - u2)).
set (b' := / 2 * (u1 + u2)).
unfold midp; rewrite 2!ulp_neq_0; try now apply Rgt_not_eq, sqrt_lt_R0.
apply Rnot_ge_lt; intro H; apply Rge_le in H.
assert (Fa : generic_format beta fexp1 a).
{
 unfold a.
  apply generic_format_round.
  -
 exact Vfexp1.
  -
 now apply valid_rnd_DN.
}
revert Fa; revert Fx.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (ma := Ztrunc (a * bpow (- fexp1 (mag a)))).
intros Fx Fa.
assert (Nna : 0 <= a).
{
 rewrite <- (round_0 beta fexp1 Zfloor).
  unfold a; apply round_le.
  -
 exact Vfexp1.
  -
 now apply valid_rnd_DN.
  -
 apply sqrt_pos.
}
assert (Phu1 : 0 < / 2 * u1).
{
 apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
}
assert (Phu2 : 0 < / 2 * u2).
{
 apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
}
assert (Pb : 0 < b).
{
 unfold b.
  rewrite <- (Rmult_0_r (/ 2)).
  apply Rmult_lt_compat_l; [lra|].
  apply Rlt_Rminus.
  unfold u2, u1, ulp, cexp.
  apply bpow_lt.
  lia.
}
assert (Pb' : 0 < b').
{
 now unfold b'; rewrite Rmult_plus_distr_l; apply Rplus_lt_0_compat.
}
assert (Hr : sqrt x <= a + b').
{
 unfold b'; apply (Rplus_le_reg_r (- / 2 * u1 - a)); ring_simplify.
  replace (_ - _) with (sqrt x - (a + / 2 * u1)) by ring.
  now apply Rabs_le_inv.
}
assert (Hl : a + b <= sqrt x).
{
 unfold b; apply (Rplus_le_reg_r (- / 2 * u1 - a)); ring_simplify.
  replace (_ + sqrt _) with (sqrt x - (a + / 2 * u1)) by ring.
  rewrite Ropp_mult_distr_l_reverse.
  now apply Rabs_le_inv in H; destruct H.
}
assert (Hf1 : (2 * fexp1 (mag (sqrt x)) <= fexp1 (mag (x)))%Z);
  [destruct (mag_sqrt_disj x Px) as [H'|H']; rewrite H'; apply Hexp|].
assert (Hlx : (fexp1 (2 * mag (sqrt x)) < 2 * mag (sqrt x))%Z).
{
 destruct (mag_sqrt_disj x Px) as [Hlx|Hlx].
  -
 apply (valid_exp_large fexp1 (mag x)); [|lia].
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
  -
 rewrite <- Hlx.
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
}
assert (Hsl : a * a + u1 * a - u2 * a + b * b <= x).
{
 replace (_ + _) with ((a + b) * (a + b)); [|now unfold b; field].
  rewrite <- sqrt_def; [|now apply Rlt_le].
  assert (H' : 0 <= a + b); [now apply Rlt_le, Rplus_le_lt_0_compat|].
  now apply Rmult_le_compat.
}
assert (Hsr : x <= a * a + u1 * a + u2 * a + b' * b').
{
 replace (_ + _) with ((a + b') * (a + b')); [|now unfold b'; field].
  rewrite <- (sqrt_def x); [|now apply Rlt_le].
  assert (H' : 0 <= sqrt x); [now apply sqrt_pos|].
  now apply Rmult_le_compat.
}
destruct (Req_dec a 0) as [Za|Nza].
-

  apply (Rlt_irrefl 0).
  apply Rlt_le_trans with (b * b); [now apply Rmult_lt_0_compat|].
  apply Rle_trans with x.
  +
 revert Hsl; unfold Rminus; rewrite Za; do 3 rewrite Rmult_0_r.
    now rewrite Ropp_0; do 3 rewrite Rplus_0_l.
  +
 rewrite Fx.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_0_l; bpow_simplify.
    unfold mx.
    rewrite Ztrunc_floor;
      [|now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]].
    apply Req_le, IZR_eq.
    apply Zfloor_imp.
    split; [now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]|simpl].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite Rmult_1_l; bpow_simplify.
    apply Rlt_le_trans with (bpow (2 * fexp1 (mag (sqrt x))));
      [|now apply bpow_le].
    change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l; rewrite Zmult_1_l.
    rewrite bpow_plus.
    rewrite <- (sqrt_def x) at 1; [|now apply Rlt_le].
    assert (sqrt x < bpow (fexp1 (mag (sqrt x))));
      [|now apply Rmult_lt_compat; [apply sqrt_pos|apply sqrt_pos| |]].
    apply (Rle_lt_trans _ _ _ Hr); rewrite Za; rewrite Rplus_0_l.
    unfold b'; change (bpow _) with u1.
    apply Rlt_le_trans with (/ 2 * (u1 + u1)); [|lra].
    apply Rmult_lt_compat_l; [lra|]; apply Rplus_lt_compat_l.
    unfold u2, u1, ulp, cexp; apply bpow_lt; lia.
-

  assert (Pa : 0 < a); [lra|].
  assert (Hla : (mag a = mag (sqrt x) :> Z)).
  {
 unfold a; apply mag_DN.
    -
 exact Vfexp1.
    -
 now fold a.
}
  assert (Hl' : 0 < - (u2 * a) + b * b).
  {
 apply (Rplus_lt_reg_r (u2 * a)); ring_simplify.
    unfold b; ring_simplify.
    apply (Rplus_lt_reg_r (/ 2 * u2 * u1)); field_simplify.
    replace (_ / 2) with (u2 * (a + / 2 * u1)) by field.
    replace (_ / 8) with (/ 4 * (u2 ^ 2 + u1 ^ 2)) by field.
    apply Rlt_le_trans with (u2 * bpow (mag (sqrt x))).
    -
 apply Rmult_lt_compat_l; [now unfold u2, ulp; apply bpow_gt_0|].
      unfold u1; rewrite <- Hla.
      apply Rlt_le_trans with (a + ulp beta fexp1 a).
      +
 apply Rplus_lt_compat_l.
        rewrite <- (Rmult_1_l (ulp _ _ _)).
        rewrite ulp_neq_0; trivial.
        apply Rmult_lt_compat_r; [apply bpow_gt_0|lra].
      +
 apply (id_p_ulp_le_bpow _ _ _ _ Pa Fa).
        apply Rabs_lt_inv, bpow_mag_gt.
    -
 apply Rle_trans with (bpow (- 1) * u1 ^ 2).
      +
 unfold pow; rewrite Rmult_1_r.
        unfold u1, u2, ulp, cexp; bpow_simplify; apply bpow_le.
        now apply Hexp.
      +
 apply Rmult_le_compat.
        *
 apply bpow_ge_0.
        *
 apply pow2_ge_0.
        *
 unfold Raux.bpow, Z.pow_pos; simpl; rewrite Zmult_1_r.
          apply Rinv_le; [lra|].
          now apply IZR_le.
        *
 rewrite <- (Rplus_0_l (u1 ^ 2)) at 1; apply Rplus_le_compat_r.
          apply pow2_ge_0.
}
  assert (Hr' : x <= a * a + u1 * a).
  {
 rewrite Hla in Fa.
    rewrite <- Rmult_plus_distr_r.
    unfold u1, ulp, cexp.
    rewrite <- (Rmult_1_l (bpow _)); rewrite Fa; rewrite <- Rmult_plus_distr_r.
    rewrite <- Rmult_assoc; rewrite (Rmult_comm _ (IZR ma)).
    rewrite <- (Rmult_assoc (IZR ma)); bpow_simplify.
    apply (Rmult_le_reg_r (bpow (- 2 * fexp1 (mag (sqrt x)))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite Fx at 1; bpow_simplify.
    rewrite <- IZR_Zpower by lia.
    rewrite <- plus_IZR, <- 2!mult_IZR.
    apply IZR_le, Zlt_succ_le, lt_IZR.
    unfold Z.succ; rewrite plus_IZR; do 2 rewrite mult_IZR; rewrite plus_IZR.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (2 * fexp1 (mag (sqrt x)))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite <- Fx.
    change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l; rewrite Zmult_1_l.
    rewrite bpow_plus; simpl.
    replace (_ * _) with (a * a + u1 * a + u1 * u1);
      [|unfold u1, ulp, cexp; rewrite Fa; ring].
    apply (Rle_lt_trans _ _ _ Hsr).
    rewrite Rplus_assoc; apply Rplus_lt_compat_l.
    apply (Rplus_lt_reg_r (- b' * b' + / 2 * u1 * u2)); ring_simplify.
    replace (_ + _) with ((a + / 2 * u1) * u2) by ring.
    apply Rlt_le_trans with (bpow (mag (sqrt x)) * u2).
    -
 apply Rmult_lt_compat_r; [now unfold u2, ulp; apply bpow_gt_0|].
      apply Rlt_le_trans with (a + u1); [lra|].
      unfold u1; fold (cexp beta fexp1 (sqrt x)).
      rewrite <- cexp_DN; [|exact Vfexp1|exact Pa]; fold a.
      rewrite <- ulp_neq_0; trivial.
      apply id_p_ulp_le_bpow.
      +
 exact Pa.
      +
 now apply round_DN_pt.
      +
 apply Rle_lt_trans with (sqrt x).
        *
 now apply round_DN_pt.
        *
 apply Rabs_lt_inv.
          apply bpow_mag_gt.
    -
 apply Rle_trans with (/ 2 * u1 ^ 2).
      +
 apply Rle_trans with (bpow (- 1) * u1 ^ 2).
        *
 unfold pow; rewrite Rmult_1_r.
          unfold u2, u1, ulp, cexp.
          bpow_simplify.
          apply bpow_le.
          rewrite Zplus_comm.
          now apply Hexp.
        *
 apply Rmult_le_compat_r; [now apply pow2_ge_0|].
          unfold Raux.bpow; simpl; unfold Z.pow_pos; simpl.
          rewrite Zmult_1_r.
          apply Rinv_le; [lra|].
          apply IZR_le; lia.
      +
 assert (u2 ^ 2 < u1 ^ 2); [|unfold b'; lra].
        unfold pow; do 2 rewrite Rmult_1_r.
        assert (H' : 0 <= u2); [unfold u2, ulp; apply bpow_ge_0|].
        assert (u2 < u1); [|now apply Rmult_lt_compat].
        unfold u1, u2, ulp, cexp; apply bpow_lt; lia.
}
  apply (Rlt_irrefl (a * a + u1 * a)).
  apply Rlt_le_trans with (a * a + u1 * a - u2 * a + b * b).
  +
 rewrite <- (Rplus_0_r (a * a + _)) at 1.
    unfold Rminus; rewrite (Rplus_assoc _ _ (b * b)).
    now apply Rplus_lt_compat_l.
  +
 now apply Rle_trans with x.
Qed.

Lemma round_round_sqrt_radix_ge_4 :
  (4 <= beta)%Z ->
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_sqrt_radix_ge_4_hyp fexp1 fexp2 ->
  forall x,
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (sqrt x).
Proof using .
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x Fx.
unfold round_round_eq.
destruct (Rle_or_lt x 0) as [Npx|Px].
-

  assert (Hs : sqrt x = 0).
  {
 destruct (Req_dec x 0) as [Zx|Nzx].
    -

      rewrite Zx.
      exact sqrt_0.
    -

      unfold sqrt.
      destruct Rcase_abs.
      +
 reflexivity.
      +
 exfalso; lra.
}
  rewrite Hs.
  rewrite round_0.
  +
 reflexivity.
  +
 now apply valid_rnd_N.
-

  assert (Hfx : (fexp1 (mag x) < mag x)%Z);
    [now apply mag_generic_gt; try assumption; lra|].
  assert (Hfsx : (fexp1 (mag (sqrt x)) < mag (sqrt x))%Z).
  {
 destruct (Rle_or_lt x 1) as [Hx|Hx].
    -

      apply (valid_exp_large fexp1 (mag x)); [exact Hfx|].
      apply mag_le; [exact Px|].
      rewrite <- (sqrt_def x) at 1; [|lra].
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l.
      +
 apply sqrt_pos.
      +
 rewrite <- sqrt_1.
        now apply sqrt_le_1_alt.
    -

      generalize ((proj1 (proj2 Hexp)) 1%Z).
      replace (_ - 1)%Z with 1%Z by ring.
      intro Hexp10.
      assert (Hf0 : (fexp1 1 < 1)%Z) by lia.
      clear Hexp10.
      apply (valid_exp_large fexp1 1); [exact Hf0|].
      apply mag_ge_bpow.
      rewrite Zeq_minus; [|reflexivity].
      unfold Raux.bpow; simpl.
      apply Rabs_ge; right.
      rewrite <- sqrt_1.
      apply sqrt_le_1_alt.
      now apply Rlt_le.
}
  assert (Hf2 : (fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1)%Z).
  {
 assert (H : (fexp1 (2 * mag (sqrt x)) < 2 * mag (sqrt x))%Z).
    {
 destruct (mag_sqrt_disj x Px) as [Hlx|Hlx].
      -
 apply (valid_exp_large fexp1 (mag x)); [|lia].
        now apply mag_generic_gt; [|apply Rgt_not_eq|].
      -
 rewrite <- Hlx.
        now apply mag_generic_gt; [|apply Rgt_not_eq|].
}
    generalize ((proj2 (proj2 Hexp)) (mag (sqrt x)) H).
    lia.
}
  apply round_round_mid_cases.
  +
 exact Vfexp1.
  +
 exact Vfexp2.
  +
 now apply sqrt_lt_R0.
  +
 lia.
  +
 lia.
  +
 intros Hmid; exfalso; apply (Rle_not_lt _ _ Hmid).
    apply (round_round_sqrt_radix_ge_4_aux Hbeta fexp1 fexp2 Vfexp1 Vfexp2
                                           Hexp x Px Hf2 Fx).
Qed.

Section Double_round_sqrt_radix_ge_4_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_sqrt_radix_ge_4_hyp :
  (2 * prec + 1 <= prec')%Z ->
  round_round_sqrt_radix_ge_4_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
intros Hprec.
unfold FLX_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_sqrt_radix_ge_4_hyp; split; [|split]; intro ex; lia.
Qed.

Theorem round_round_sqrt_radix_ge_4_FLX :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x,
  FLX_format beta prec x ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (sqrt x).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hprec x Fx.
apply round_round_sqrt_radix_ge_4.
-
 exact Hbeta.
-
 now apply FLX_exp_valid.
-
 now apply FLX_exp_valid.
-
 now apply FLX_round_round_sqrt_radix_ge_4_hyp.
-
 now apply generic_format_FLX.
Qed.

End Double_round_sqrt_radix_ge_4_FLX.

Section Double_round_sqrt_radix_ge_4_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_sqrt_radix_ge_4_hyp :
  (emin <= 0)%Z ->
  ((emin' <= emin - prec - 1)%Z
   \/ (2 * emin' <= emin - 4 * prec)%Z) ->
  (2 * prec + 1 <= prec')%Z ->
  round_round_sqrt_radix_ge_4_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof using prec_gt_0_.
intros Hemin Heminprec Hprec.
unfold FLT_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_sqrt_radix_ge_4_hyp; split; [|split]; intros ex.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (2 * ex - prec) emin).
  lia.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (2 * ex - 1 - prec) emin).
  lia.
-
 generalize (Zmax_spec (2 * ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ex - prec) emin).
  lia.
Qed.

Theorem round_round_sqrt_radix_ge_4_FLT :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (emin <= 0)%Z ->
  ((emin' <= emin - prec - 1)%Z
   \/ (2 * emin' <= emin - 4 * prec)%Z) ->
  (2 * prec + 1 <= prec')%Z ->
  forall x,
  FLT_format beta emin prec x ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hemin Heminprec Hprec x Fx.
apply round_round_sqrt_radix_ge_4.
-
 exact Hbeta.
-
 now apply FLT_exp_valid.
-
 now apply FLT_exp_valid.
-
 now apply FLT_round_round_sqrt_radix_ge_4_hyp.
-
 now apply generic_format_FLT.
Qed.

End Double_round_sqrt_radix_ge_4_FLT.

Section Double_round_sqrt_radix_ge_4_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_sqrt_radix_ge_4_hyp :
  (2 * (emin' + prec') <= emin + prec <= 1)%Z ->
  (2 * prec + 1 <= prec')%Z ->
  round_round_sqrt_radix_ge_4_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof using prec_gt_0_.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in *.
unfold round_round_sqrt_radix_ge_4_hyp; split; [|split]; intros ex.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (2 * ex - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (2 * ex - 1 - prec) emin);
  lia.
-
 intro H.
  destruct (Zle_or_lt emin (2 * ex - prec)) as [H'|H'].
  +
 destruct (Z.ltb_spec (ex - prec') emin');
    destruct (Z.ltb_spec (ex - prec) emin);
    lia.
  +
 exfalso.
    rewrite (Zlt_bool_true _ _ H') in H.
    lia.
Qed.

Theorem round_round_sqrt_radix_ge_4_FTZ :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (2 * (emin' + prec') <= emin + prec <= 1)%Z ->
  (2 * prec + 1 <= prec')%Z ->
  forall x,
  FTZ_format beta emin prec x ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof using prec_gt_0_ prec_gt_0_'.
intros Hbeta choice1 choice2 Hemin Hprec x Fx.
apply round_round_sqrt_radix_ge_4.
-
 exact Hbeta.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_round_round_sqrt_radix_ge_4_hyp.
-
 now apply generic_format_FTZ.
Qed.

End Double_round_sqrt_radix_ge_4_FTZ.

End Double_round_sqrt_radix_ge_4.

End Double_round_sqrt.

Section Double_round_div.

Lemma round_round_eq_mid_beta_even :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (exists n, (beta = 2 * n :> Z)%Z) ->
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  x = midp fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Ebeta x Px Hf2 Hf1.
unfold round_round_eq.
unfold midp.
set (rd := round beta fexp1 Zfloor x).
set (u := ulp beta fexp1 x).
intro H; apply (Rplus_eq_compat_l (- rd)) in H.
ring_simplify in H; revert H.
rewrite Rplus_comm; fold (Rminus x rd).
intro Xmid.
destruct Ebeta as (n,Ebeta).
assert (Hbeta : (2 <= beta)%Z).
{
 destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
}
apply (Rplus_eq_compat_l rd) in Xmid; ring_simplify in Xmid.
rewrite (round_generic beta fexp2); [reflexivity|now apply valid_rnd_N|].
set (f := Float beta (Zfloor (scaled_mantissa beta fexp2 rd)
                      + n * beta ^ (fexp1 (mag x) - 1
                                    - fexp2 (mag x)))
                (cexp beta fexp2 x)).
assert (Hf : F2R f = x).
{
 unfold f, F2R; simpl.
  rewrite plus_IZR.
  rewrite Rmult_plus_distr_r.
  rewrite mult_IZR.
  rewrite IZR_Zpower by lia.
  unfold cexp at 2; bpow_simplify.
  unfold Zminus; rewrite bpow_plus.
  rewrite (Rmult_comm _ (bpow (- 1))).
  rewrite <- (Rmult_assoc (IZR n)).
  change (bpow (- 1)) with (/ IZR (beta * 1)).
  rewrite Zmult_1_r.
  rewrite Ebeta.
  rewrite (mult_IZR 2).
  rewrite Rinv_mult_distr;
    [|simpl; lra | apply IZR_neq; lia].
  rewrite <- Rmult_assoc; rewrite (Rmult_comm (IZR n));
  rewrite (Rmult_assoc _ (IZR n)).
  rewrite Rinv_r;
    [rewrite Rmult_1_r | apply IZR_neq; lia].
  simpl; fold (cexp beta fexp1 x).
  rewrite <- 2!ulp_neq_0; try now apply Rgt_not_eq.
  fold u; rewrite Xmid at 2.
  apply f_equal2; [|reflexivity].
  rewrite ulp_neq_0; try now apply Rgt_not_eq.
  destruct (Req_dec rd 0) as [Zrd|Nzrd].
  -

    rewrite Zrd.
    rewrite scaled_mantissa_0.
    rewrite Zfloor_IZR.
    now rewrite Rmult_0_l.
  -

    assert (Nnrd : 0 <= rd).
    {
 apply round_DN_pt.
      -
 exact Vfexp1.
      -
 apply generic_format_0.
      -
 now apply Rlt_le.
}
    assert (Prd : 0 < rd); [lra|].
    assert (Lrd : (mag rd = mag x :> Z)).
    {
 apply Zle_antisym.
      -
 apply mag_le; [exact Prd|].
        now apply round_DN_pt.
      -
 apply mag_round_ge.
        +
 exact Vfexp1.
        +
 now apply valid_rnd_DN.
        +
 exact Nzrd.
}
    unfold scaled_mantissa.
    unfold rd at 1.
    unfold round, F2R, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite Lrd.
    rewrite <- (IZR_Zpower _ (_ - _)) by lia.
    rewrite <- mult_IZR.
    rewrite (Zfloor_imp (Zfloor (x * bpow (- fexp1 (mag x))) *
                         beta ^ (fexp1 (mag x) - fexp2 (mag x)))).
    +
 rewrite mult_IZR.
      rewrite IZR_Zpower by lia.
      bpow_simplify.
      now unfold rd.
    +
 split; [now apply Rle_refl|].
      rewrite plus_IZR.
      simpl; lra.
}
apply (generic_format_F2R' _ _ x f Hf).
intros _.
apply Z.le_refl.
Qed.

Lemma round_round_really_zero :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (mag x <= fexp1 (mag x) - 2)%Z ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf1.
assert (Hlx : bpow (mag x - 1) <= x < bpow (mag x)).
{
 destruct (mag x) as (ex,Hex); simpl.
  rewrite <- (Rabs_right x); [|now apply Rle_ge; apply Rlt_le].
  apply Hex.
  now apply Rgt_not_eq.
}
unfold round_round_eq.
rewrite (round_N_small_pos beta fexp1 _ x (mag x)); [|exact Hlx|lia].
set (x'' := round beta fexp2 (Znearest choice2) x).
destruct (Req_dec x'' 0) as [Zx''|Nzx''];
  [now rewrite Zx''; rewrite round_0; [|apply valid_rnd_N]|].
destruct (Zle_or_lt (fexp2 (mag x)) (mag x)).
-

  destruct (Rlt_or_le x'' (bpow (mag x))).
  +

    rewrite (round_N_small_pos beta fexp1 _ _ (mag x));
    [reflexivity|split; [|exact H0]|lia].
    apply round_large_pos_ge_bpow; [now apply valid_rnd_N| |now apply Hlx].
    fold x''; assert (0 <= x''); [|lra]; unfold x''.
    rewrite <- (round_0 beta fexp2 (Znearest choice2)).
    now apply round_le; [|apply valid_rnd_N|apply Rlt_le].
  +

    assert (Hx'' : x'' = bpow (mag x)).
    {
 apply Rle_antisym; [|exact H0].
      rewrite <- (round_generic beta fexp2 (Znearest choice2) (bpow _)).
      -
 now apply round_le; [|apply valid_rnd_N|apply Rlt_le].
      -
 now apply generic_format_bpow'.
}
    rewrite Hx''.
    unfold round, F2R, scaled_mantissa, cexp; simpl.
    rewrite mag_bpow.
    assert (Hf11 : (fexp1 (mag x + 1) = fexp1 (mag x) :> Z)%Z);
      [apply Vfexp1; lia|].
    rewrite Hf11.
    apply (Rmult_eq_reg_r (bpow (- fexp1 (mag x))));
      [|now apply Rgt_not_eq; apply bpow_gt_0].
    rewrite Rmult_0_l; bpow_simplify.
    apply IZR_eq.
    apply Znearest_imp.
    simpl; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
    rewrite Rabs_right; [|now apply Rle_ge; apply bpow_ge_0].
    apply Rle_lt_trans with (bpow (- 2)); [now apply bpow_le; lia|].
    unfold Raux.bpow, Z.pow_pos; simpl; rewrite Zmult_1_r.
    assert (Hbeta : (2 <= beta)%Z).
    {
 destruct beta as (beta_val,beta_prop); simpl.
      now apply Zle_bool_imp_le.
}
    apply Rinv_lt_contravar.
    *
 apply Rmult_lt_0_compat; [lra|].
      rewrite mult_IZR; apply Rmult_lt_0_compat;
      apply IZR_lt; lia.
    *
 apply IZR_lt.
      apply (Z.le_lt_trans _ _ _ Hbeta).
      rewrite <- (Zmult_1_r beta) at 1.
      apply Zmult_lt_compat_l; lia.
-

  exfalso; apply Nzx''.
  now apply (round_N_small_pos beta _ _ _ (mag x)).
Qed.

Lemma round_round_zero :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp1 (mag x) = mag x + 1 :> Z)%Z ->
  x < bpow (mag x) - / 2 * ulp beta fexp2 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf1.
unfold round_round_eq.
set (x'' := round beta fexp2 (Znearest choice2) x).
set (u1 := ulp beta fexp1 x).
set (u2 := ulp beta fexp2 x).
intro Hx.
assert (Hlx : bpow (mag x - 1) <= x < bpow (mag x)).
{
 destruct (mag x) as (ex,Hex); simpl.
  rewrite <- (Rabs_right x); [|now apply Rle_ge; apply Rlt_le].
  apply Hex.
  now apply Rgt_not_eq.
}
rewrite (round_N_small_pos beta fexp1 choice1 x (mag x));
  [|exact Hlx|lia].
destruct (Req_dec x'' 0) as [Zx''|Nzx''];
  [now rewrite Zx''; rewrite round_0; [reflexivity|apply valid_rnd_N]|].
rewrite (round_N_small_pos beta _ _ x'' (mag x));
  [reflexivity| |lia].
split.
-
 apply round_large_pos_ge_bpow.
  +
 now apply valid_rnd_N.
  +
 assert (0 <= x''); [|now fold x''; lra].
    rewrite <- (round_0 beta fexp2 (Znearest choice2)).
    now apply round_le; [|apply valid_rnd_N|apply Rlt_le].
  +
 apply Rle_trans with (Rabs x);
    [|now rewrite Rabs_right; [apply Rle_refl|apply Rle_ge; apply Rlt_le]].
    destruct (mag x) as (ex,Hex); simpl; apply Hex.
    now apply Rgt_not_eq.
-
 replace x'' with (x + (x'' - x)) by ring.
  replace (bpow _) with (bpow (mag x) - / 2 * u2 + / 2 * u2) by ring.
  apply Rplus_lt_le_compat; [exact Hx|].
  apply Rabs_le_inv.
  now apply error_le_half_ulp.
Qed.

Lemma round_round_all_mid_cases :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  ((fexp1 (mag x) = mag x + 1 :> Z)%Z ->
   bpow (mag x) - / 2 * ulp beta fexp2 x <= x ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  ((fexp1 (mag x) <= mag x)%Z ->
   midp fexp1 x - / 2 * ulp beta fexp2 x <= x < midp fexp1 x ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  ((fexp1 (mag x) <= mag x)%Z ->
   x = midp fexp1 x ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  ((fexp1 (mag x) <= mag x)%Z ->
   midp fexp1 x < x <= midp fexp1 x + / 2 * ulp beta fexp2 x ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2.
set (x' := round beta fexp1 Zfloor x).
set (u1 := ulp beta fexp1 x).
set (u2 := ulp beta fexp2 x).
intros Cz Clt Ceq Cgt.
destruct (Ztrichotomy (mag x) (fexp1 (mag x) - 1)) as [Hlt|[Heq|Hgt]].
-

  assert (H : (mag x <= fexp1 (mag x) - 2)%Z) by lia.
  now apply round_round_really_zero.
-

  assert (H : (fexp1 (mag x) = (mag x + 1))%Z) by lia.
  destruct (Rlt_or_le x (bpow (mag x) - / 2 * u2)) as [Hlt'|Hge'].
  +
 now apply round_round_zero.
  +
 now apply Cz.
-

  assert (H : (fexp1 (mag x) <= mag x)%Z) by lia.
  destruct (Rtotal_order x (midp fexp1 x)) as [Hlt'|[Heq'|Hgt']].
  +

    destruct (Rlt_or_le x (midp fexp1 x - / 2 * u2)) as [Hlt''|Hle''].
    *
 now apply round_round_lt_mid_further_place; [| | |lia| |].
    *
 now apply Clt; [|split].
  +

    now apply Ceq.
  +

    destruct (Rle_or_lt x (midp fexp1 x + / 2 * u2)) as [Hlt''|Hle''].
    *
 now apply Cgt; [|split].
    *
 {
 destruct (generic_format_EM beta fexp1 x) as [Fx|Nfx].
        -

          unfold round_round_eq; rewrite (round_generic beta fexp2);
          [reflexivity|now apply valid_rnd_N|].
          now apply (generic_inclusion_mag beta fexp1); [lia|].
        -

          assert (Hceil : round beta fexp1 Zceil x = x' + u1);
          [now apply round_UP_DN_ulp|].
          assert (Hf2' : (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z) by lia.
          assert (midp' fexp1 x + / 2 * ulp beta fexp2 x < x);
            [|now apply round_round_gt_mid_further_place].
          revert Hle''; unfold midp, midp'; fold x'.
          rewrite Hceil; fold u1; fold u2.
          lra.
}
Qed.

Lemma mag_div_disj :
  forall x y : R,
  0 < x -> 0 < y ->
  ((mag (x / y) = mag x - mag y :> Z)%Z
   \/ (mag (x / y) = mag x - mag y + 1 :> Z)%Z).
Proof using .
intros x y Px Py.
generalize (mag_div beta x y (Rgt_not_eq _ _ Px) (Rgt_not_eq _ _ Py)).
lia.
Qed.

Definition round_round_div_hyp fexp1 fexp2 :=
  (forall ex, (fexp2 ex <= fexp1 ex - 1)%Z)
  /\ (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
                    (fexp1 (ex - ey) <= ex - ey + 1)%Z ->
                    (fexp2 (ex - ey) <= fexp1 ex - ey)%Z)
  /\ (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
                    (fexp1 (ex - ey + 1) <= ex - ey + 1 + 1)%Z ->
                    (fexp2 (ex - ey + 1) <= fexp1 ex - ey)%Z)
  /\ (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
                    (fexp1 (ex - ey) <= ex - ey)%Z ->
                    (fexp2 (ex - ey) <= fexp1 (ex - ey)
                                        + fexp1 ey - ey)%Z)
  /\ (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
                    (fexp1 (ex - ey) = ex - ey + 1)%Z ->
                    (fexp2 (ex - ey) <= ex - ey - ey + fexp1 ey)%Z).

Lemma round_round_div_aux0 :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  fexp1 (mag (x / y)) = (mag (x / y) + 1)%Z ->
  ~ (bpow (mag (x / y)) - / 2 * ulp beta fexp2 (x / y) <= x / y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Fx Fy Hf1.
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
set (p := bpow (mag (x / y))).
set (u2 := bpow (fexp2 (mag (x / y)))).
revert Fx Fy.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (my := Ztrunc (y * bpow (- fexp1 (mag y)))).
intros Fx Fy.
rewrite ulp_neq_0.
2: apply Rmult_integral_contrapositive_currified; [now apply Rgt_not_eq|idtac].
2: now apply Rinv_neq_0_compat, Rgt_not_eq.
intro Hl.
assert (Hr : x / y < p);
  [now apply Rabs_lt_inv; apply bpow_mag_gt|].
apply (Rlt_irrefl (p - / 2 * u2)).
apply (Rle_lt_trans _ _ _ Hl).
apply (Rmult_lt_reg_r y _ _ Py).
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l; [|now apply Rgt_not_eq]; rewrite Rmult_1_r.
destruct (Zle_or_lt Z0 (fexp1 (mag x) - mag (x / y)
                        - fexp1 (mag y))%Z) as [He|He].
-

  apply Rle_lt_trans with (p * y - p * bpow (fexp1 (mag y))).
  +
 rewrite Fx; rewrite Fy at 1.
    rewrite <- Rmult_assoc.
    rewrite (Rmult_comm p).
    unfold p; bpow_simplify.
    apply (Rmult_le_reg_r (bpow (- mag (x / y) - fexp1 (mag y))));
      [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    rewrite <- IZR_Zpower; [|exact He].
    rewrite <- mult_IZR.
    rewrite <- minus_IZR.
    apply IZR_le.
    apply (Zplus_le_reg_r _ _ 1); ring_simplify.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite mult_IZR.
    rewrite IZR_Zpower; [|exact He].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag y) + mag (x / y))));
      [now apply bpow_gt_0|].
    bpow_simplify.
    rewrite <- Fx.
    rewrite bpow_plus.
    rewrite <- Rmult_assoc; rewrite <- Fy.
    fold p.
    apply (Rmult_lt_reg_r (/ y)); [now apply Rinv_0_lt_compat|].
    field_simplify; lra.
  +
 rewrite Rmult_minus_distr_r.
    unfold Rminus; apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    *
 rewrite <- (Rmult_1_l (u2 * _)).
      rewrite Rmult_assoc.
      {
 apply Rmult_lt_compat.
        -
 lra.
        -
 now apply Rmult_le_pos; [apply bpow_ge_0|apply Rlt_le].
        -
 lra.
        -
 apply Rmult_lt_compat_l; [now apply bpow_gt_0|].
          apply Rabs_lt_inv.
          apply bpow_mag_gt.
}
    *
 unfold u2, p, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite (Zplus_comm (- _)); fold (Zminus (mag (x / y)) (mag y)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      [now apply Hexp; [| |rewrite <- Hxy]|].
      replace (_ - _ + 1)%Z with ((mag x + 1) - mag y)%Z by ring.
      apply Hexp.
      {
 now assert (fexp1 (mag x + 1) <= mag x)%Z;
        [apply valid_exp|lia].
}
      {
 assumption.
}
      replace (_ + 1 - _)%Z with (mag x - mag y + 1)%Z by ring.
      now rewrite <- Hxy.
-

  apply Rle_lt_trans with (p * y - bpow (fexp1 (mag x))).
  +
 rewrite Fx at 1; rewrite Fy at 1.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    rewrite (Rmult_comm p).
    unfold p; bpow_simplify.
    rewrite <- IZR_Zpower by lia.
    rewrite <- mult_IZR.
    rewrite <- minus_IZR.
    apply IZR_le.
    apply (Zplus_le_reg_r _ _ 1); ring_simplify.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite mult_IZR.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite <- Fx.
    rewrite Zplus_comm; rewrite bpow_plus.
    rewrite <- Rmult_assoc; rewrite <- Fy.
    fold p.
    apply (Rmult_lt_reg_r (/ y)); [now apply Rinv_0_lt_compat|].
    field_simplify; lra.
  +
 rewrite Rmult_minus_distr_r.
    unfold Rminus; apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    *
 rewrite <- (Rmult_1_l (u2 * _)).
      rewrite Rmult_assoc.
      {
 apply Rmult_lt_compat.
        -
 lra.
        -
 now apply Rmult_le_pos; [apply bpow_ge_0|apply Rlt_le].
        -
 lra.
        -
 apply Rmult_lt_compat_l; [now apply bpow_gt_0|].
          apply Rabs_lt_inv.
          apply bpow_mag_gt.
}
    *
 unfold u2, p, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite (Zplus_comm (- _)); fold (Zminus (mag (x / y)) (mag y)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      apply Hexp; try assumption; rewrite <- Hxy; rewrite Hf1; apply Z.le_refl.
Qed.

Lemma round_round_div_aux1 :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  (fexp1 (mag (x / y)) <= mag (x / y))%Z ->
  ~ (midp fexp1 (x / y) - / 2 * ulp beta fexp2 (x / y)
     <= x / y
     < midp fexp1 (x / y)).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Fx Fy Hf1.
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (S : (x / y <> 0)%R).
apply Rmult_integral_contrapositive_currified; [now apply Rgt_not_eq|idtac].
now apply Rinv_neq_0_compat, Rgt_not_eq.
cut (~ (/ 2 * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y))
        <= x / y - round beta fexp1 Zfloor (x / y)
        < / 2 * ulp beta fexp1 (x / y))).
{
 intro H; intro H'; apply H; split.
  -
 apply (Rplus_le_reg_l (round beta fexp1 Zfloor (x / y))).
    ring_simplify.
    apply H'.
  -
 apply (Rplus_lt_reg_l (round beta fexp1 Zfloor (x / y))).
    ring_simplify.
    apply H'.
}
set (u1 := bpow (fexp1 (mag (x / y)))).
set (u2 := bpow (fexp2 (mag (x / y)))).
set (x' := round beta fexp1 Zfloor (x / y)).
rewrite 2!ulp_neq_0; trivial.
revert Fx Fy.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (my := Ztrunc (y * bpow (- fexp1 (mag y)))).
intros Fx Fy.
intro Hlr.
apply (Rlt_irrefl (/ 2 * (u1 - u2))).
apply (Rle_lt_trans _ _ _ (proj1 Hlr)).
apply (Rplus_lt_reg_r x'); ring_simplify.
apply (Rmult_lt_reg_r y _ _ Py).
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l; [|now apply Rgt_not_eq]; rewrite Rmult_1_r.
rewrite Rmult_minus_distr_r; rewrite Rmult_plus_distr_r.
apply (Rmult_lt_reg_l 2); [lra|].
rewrite Rmult_minus_distr_l; rewrite Rmult_plus_distr_l.
do 5 rewrite <- Rmult_assoc.
rewrite Rinv_r; [|lra]; do 2 rewrite Rmult_1_l.
destruct (Zle_or_lt Z0 (fexp1 (mag x) - fexp1 (mag (x / y))
                     - fexp1 (mag y))%Z) as [He|He].
-

  apply Rle_lt_trans with (2 * x' * y + u1 * y
                                        - bpow (fexp1 (mag (x / y))
                                                + fexp1 (mag y))).
  +
 rewrite Fx at 1; rewrite Fy at 1 2.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag (x / y))
                                 - fexp1 (mag y))));
      [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r; rewrite (Rmult_plus_distr_r (_ * _ * _)).
    bpow_simplify.
    replace (2 * x' * _ * _)
    with (2 * IZR my * x' * bpow (- fexp1 (mag (x / y)))) by ring.
    rewrite (Rmult_comm u1).
    unfold x', u1, round, F2R, ulp, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite <- IZR_Zpower; [|exact He].
    do 4 rewrite <- mult_IZR.
    rewrite <- plus_IZR.
    rewrite <- minus_IZR.
    apply IZR_le.
    apply (Zplus_le_reg_r _ _ 1); ring_simplify.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite plus_IZR.
    do 4 rewrite mult_IZR; simpl.
    rewrite IZR_Zpower; [|exact He].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag (x / y))
                                 + fexp1 (mag y))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite Rmult_assoc.
    rewrite <- Fx.
    rewrite (Rmult_plus_distr_r _ _ (Raux.bpow _ _)).
    rewrite Rmult_assoc.
    rewrite bpow_plus.
    rewrite <- (Rmult_assoc (IZR (Zfloor _))).
    change (IZR (Zfloor _) * _) with x'.
    do 2 rewrite (Rmult_comm _ (bpow (fexp1 (mag y)))).
    rewrite Rmult_assoc.
    do 2 rewrite <- (Rmult_assoc (IZR my)).
    rewrite <- Fy.
    change (bpow _) with u1.
    apply (Rmult_lt_reg_l (/ 2)); [lra|].
    rewrite Rmult_plus_distr_l.
    do 4 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|lra]; do 2 rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (- y * x')); ring_simplify.
    apply (Rmult_lt_reg_l (/ y)); [now apply Rinv_0_lt_compat|].
    rewrite Rmult_minus_distr_l.
    do 3 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|now apply Rgt_not_eq]; do 2 rewrite Rmult_1_l.
    now rewrite Rmult_comm.
  +
 apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    *
 {
 apply Rmult_lt_compat_l.
        -
 apply bpow_gt_0.
        -
 apply Rabs_lt_inv.
          apply bpow_mag_gt.
}
    *
 unfold u2, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite <- Zplus_assoc; rewrite (Zplus_comm (- _)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      [now apply Hexp; [| |rewrite <- Hxy]|].
      replace (_ - _ + 1)%Z with ((mag x + 1) - mag y)%Z by ring.
      apply Hexp.
      {
 now assert (fexp1 (mag x + 1) <= mag x)%Z;
        [apply valid_exp|lia].
}
      {
 assumption.
}
      replace (_ + 1 - _)%Z with (mag x - mag y + 1)%Z by ring.
      now rewrite <- Hxy.
-

  apply Rle_lt_trans with (2 * x' * y + u1 * y - bpow (fexp1 (mag x))).
  +
 rewrite Fx at 1; rewrite Fy at 1 2.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r; rewrite (Rmult_plus_distr_r (_ * _ * _)).
    bpow_simplify.
    replace (2 * x' * _ * _)
    with (2 * IZR my * x' * bpow (fexp1 (mag y) - fexp1 (mag x))) by ring.
    rewrite (Rmult_comm u1).
    unfold x', u1, round, F2R, ulp, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite <- (IZR_Zpower _ (_ - _)%Z) by lia.
    do 5 rewrite <- mult_IZR.
    rewrite <- plus_IZR.
    rewrite <- minus_IZR.
    apply IZR_le.
    apply (Zplus_le_reg_r _ _ 1); ring_simplify.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite plus_IZR.
    do 5 rewrite mult_IZR; simpl.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_assoc.
    rewrite <- Fx.
    rewrite (Rmult_plus_distr_r _ _ (Raux.bpow _ _)).
    bpow_simplify.
    rewrite Rmult_assoc.
    rewrite bpow_plus.
    rewrite <- (Rmult_assoc (IZR (Zfloor _))).
    change (IZR (Zfloor _) * _) with x'.
    do 2 rewrite (Rmult_comm _ (bpow (fexp1 (mag y)))).
    rewrite Rmult_assoc.
    do 2 rewrite <- (Rmult_assoc (IZR my)).
    rewrite <- Fy.
    change (bpow _) with u1.
    apply (Rmult_lt_reg_l (/ 2)); [lra|].
    rewrite Rmult_plus_distr_l.
    do 4 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|lra]; do 2 rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (- y * x')); ring_simplify.
    apply (Rmult_lt_reg_l (/ y)); [now apply Rinv_0_lt_compat|].
    rewrite Rmult_minus_distr_l.
    do 3 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|now apply Rgt_not_eq]; do 2 rewrite Rmult_1_l.
    now rewrite Rmult_comm.
  +
 apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    *
 {
 apply Rmult_lt_compat_l.
        -
 apply bpow_gt_0.
        -
 apply Rabs_lt_inv.
          apply bpow_mag_gt.
}
    *
 unfold u2, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite (Zplus_comm (- _)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      apply Hexp; try assumption; rewrite <- Hxy; lia.
Qed.

Lemma round_round_div_aux2 :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  (fexp1 (mag (x / y)) <= mag (x / y))%Z ->
  ~ (midp fexp1 (x / y)
     < x / y
     <= midp fexp1 (x / y) + / 2 * ulp beta fexp2 (x / y)).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Fx Fy Hf1.
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
cut (~ (/ 2 * ulp beta fexp1 (x / y)
        < x / y - round beta fexp1 Zfloor (x / y)
        <= / 2 * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)))).
{
 intro H; intro H'; apply H; split.
  -
 apply (Rplus_lt_reg_l (round beta fexp1 Zfloor (x / y))).
    ring_simplify.
    apply H'.
  -
 apply (Rplus_le_reg_l (round beta fexp1 Zfloor (x / y))).
    ring_simplify.
    apply H'.
}
set (u1 := bpow (fexp1 (mag (x / y)))).
set (u2 := bpow (fexp2 (mag (x / y)))).
set (x' := round beta fexp1 Zfloor (x / y)).
assert (S : (x / y <> 0)%R).
apply Rmult_integral_contrapositive_currified; [now apply Rgt_not_eq|idtac].
now apply Rinv_neq_0_compat, Rgt_not_eq.
rewrite 2!ulp_neq_0; trivial.
revert Fx Fy.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (my := Ztrunc (y * bpow (- fexp1 (mag y)))).
intros Fx Fy.
intro Hlr.
apply (Rlt_irrefl (/ 2 * (u1 + u2))).
apply Rlt_le_trans with (x / y - x'); [|now apply Hlr].
apply (Rplus_lt_reg_r x'); ring_simplify.
apply (Rmult_lt_reg_r y _ _ Py).
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l; [|now apply Rgt_not_eq]; rewrite Rmult_1_r.
do 2 rewrite Rmult_plus_distr_r.
apply (Rmult_lt_reg_l 2); [lra|].
do 2 rewrite Rmult_plus_distr_l.
do 5 rewrite <- Rmult_assoc.
rewrite Rinv_r; [|lra]; do 2 rewrite Rmult_1_l.
destruct (Zle_or_lt Z0 (fexp1 (mag x) - fexp1 (mag (x / y))
                     - fexp1 (mag y))%Z) as [He|He].
-

  apply Rlt_le_trans with (u1 * y + bpow (fexp1 (mag (x / y))
                                          + fexp1 (mag y))
                           + 2 * x' * y).
  +
 apply Rplus_lt_compat_r, Rplus_lt_compat_l.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    *
 {
 apply Rmult_lt_compat_l.
        -
 apply bpow_gt_0.
        -
 apply Rabs_lt_inv.
          apply bpow_mag_gt.
}
    *
 unfold u2, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite <- Zplus_assoc; rewrite (Zplus_comm (- _)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      [now apply Hexp; [| |rewrite <- Hxy]|].
      replace (_ - _ + 1)%Z with ((mag x + 1) - mag y)%Z by ring.
      apply Hexp.
      {
 now assert (fexp1 (mag x + 1) <= mag x)%Z;
        [apply valid_exp|lia].
}
      {
 assumption.
}
      replace (_ + 1 - _)%Z with (mag x - mag y + 1)%Z by ring.
      now rewrite <- Hxy.
  +
 apply Rge_le; rewrite Fx at 1; apply Rle_ge.
    replace (u1 * y) with (u1 * (IZR my * bpow (fexp1 (mag y))));
      [|now apply eq_sym; rewrite Fy at 1].
    replace (2 * x' * y) with (2 * x' * (IZR my * bpow (fexp1 (mag y))));
      [|now apply eq_sym; rewrite Fy at 1].
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag (x / y))
                                 - fexp1 (mag y))));
      [now apply bpow_gt_0|].
    do 2 rewrite Rmult_plus_distr_r.
    bpow_simplify.
    rewrite (Rmult_comm u1).
    unfold u1, ulp, cexp; bpow_simplify.
    rewrite (Rmult_assoc 2).
    rewrite (Rmult_comm x').
    rewrite (Rmult_assoc 2).
    unfold x', round, F2R, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite <- (IZR_Zpower _ (_ - _)%Z); [|exact He].
    do 4 rewrite <- mult_IZR.
    do 2 rewrite <- plus_IZR.
    apply IZR_le.
    rewrite Zplus_comm, Zplus_assoc.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite plus_IZR.
    do 4 rewrite mult_IZR; simpl.
    rewrite IZR_Zpower; [|exact He].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag y))));
      [now apply bpow_gt_0|].
    rewrite Rmult_plus_distr_r.
    rewrite (Rmult_comm _ (IZR _)).
    do 2 rewrite Rmult_assoc.
    rewrite <- Fy.
    bpow_simplify.
    unfold Zminus; rewrite bpow_plus.
    rewrite (Rmult_assoc _ (IZR mx)).
    rewrite <- (Rmult_assoc (IZR mx)).
    rewrite <- Fx.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag (x / y)))));
      [now apply bpow_gt_0|].
    rewrite Rmult_plus_distr_r.
    bpow_simplify.
    rewrite (Rmult_comm _ y).
    do 2 rewrite Rmult_assoc.
    change (IZR (Zfloor _) * _) with x'.
    change (bpow _) with u1.
    apply (Rmult_lt_reg_l (/ 2)); [lra|].
    rewrite Rmult_plus_distr_l.
    do 4 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|lra]; do 2 rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (- y * x')); ring_simplify.
    apply (Rmult_lt_reg_l (/ y)); [now apply Rinv_0_lt_compat|].
    rewrite Rmult_plus_distr_l.
    do 3 rewrite <- Rmult_assoc.
    rewrite Ropp_mult_distr_r_reverse.
    rewrite Ropp_mult_distr_l_reverse.
    rewrite Rinv_l; [|now apply Rgt_not_eq]; do 2 rewrite Rmult_1_l.
    rewrite (Rmult_comm (/ y)).
    now rewrite (Rplus_comm (- x')).
-

  apply Rlt_le_trans with (2 * x' * y + u1 * y + bpow (fexp1 (mag x))).
  +
 rewrite Rplus_comm, Rplus_assoc; do 2 apply Rplus_lt_compat_l.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    *
 apply Rmult_lt_compat_l.
      now apply bpow_gt_0.
      now apply Rabs_lt_inv; apply bpow_mag_gt.
    *
 unfold u2, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite (Zplus_comm (- _)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      apply Hexp; try assumption; rewrite <- Hxy; lia.
  +
 apply Rge_le; rewrite Fx at 1; apply Rle_ge.
    rewrite Fy at 1 2.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    do 2 rewrite Rmult_plus_distr_r.
    bpow_simplify.
    replace (2 * x' * _ * _)
    with (2 * IZR my * x' * bpow (fexp1 (mag y) - fexp1 (mag x))) by ring.
    rewrite (Rmult_comm u1).
    unfold x', u1, round, F2R, ulp, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite <- (IZR_Zpower _ (_ - _)%Z) by lia.
    do 5 rewrite <- mult_IZR.
    do 2 rewrite <- plus_IZR.
    apply IZR_le.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite plus_IZR.
    do 5 rewrite mult_IZR; simpl.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite (Rmult_assoc _ (IZR mx)).
    rewrite <- Fx.
    rewrite Rmult_plus_distr_r.
    bpow_simplify.
    rewrite bpow_plus.
    rewrite Rmult_assoc.
    rewrite <- (Rmult_assoc (IZR _)).
    change (IZR _ * bpow _) with x'.
    do 2 rewrite (Rmult_comm _ (bpow (fexp1 (mag y)))).
    rewrite Rmult_assoc.
    do 2 rewrite <- (Rmult_assoc (IZR my)).
    rewrite <- Fy.
    change (bpow _) with u1.
    apply (Rmult_lt_reg_l (/ 2)); [lra|].
    rewrite Rmult_plus_distr_l.
    do 4 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|lra]; do 2 rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (- y * x')); ring_simplify.
    apply (Rmult_lt_reg_l (/ y)); [now apply Rinv_0_lt_compat|].
    rewrite Rmult_plus_distr_l.
    do 3 rewrite <- Rmult_assoc.
    rewrite Ropp_mult_distr_r_reverse.
    rewrite Ropp_mult_distr_l_reverse.
    rewrite Rinv_l; [|now apply Rgt_not_eq]; do 2 rewrite Rmult_1_l.
    rewrite (Rmult_comm (/ y)).
    now rewrite (Rplus_comm (- x')).
Qed.

Lemma round_round_div_aux :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (exists n, (beta = 2 * n :> Z)%Z) ->
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x / y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Ebeta Hexp x y Px Py Fx Fy.
assert (Pxy : 0 < x / y).
{
 apply Rmult_lt_0_compat; [exact Px|].
  now apply Rinv_0_lt_compat.
}
apply round_round_all_mid_cases.
-
 exact Vfexp1.
-
 exact Vfexp2.
-
 exact Pxy.
-
 apply Hexp.
-
 intros Hf1 Hlxy.
  exfalso.
  now apply (round_round_div_aux0 fexp1 fexp2 _ _ choice1 choice2 Hexp x y).
-
 intros Hf1 Hlxy.
  exfalso.
  now apply (round_round_div_aux1 fexp1 fexp2 _ _ choice1 choice2 Hexp x y).
-
 intro H.
  apply round_round_eq_mid_beta_even; try assumption.
  apply Hexp.
-
 intros Hf1 Hlxy.
  exfalso.
  now apply (round_round_div_aux2 fexp1 fexp2 _ _ choice1 choice2 Hexp x y).
Qed.

Lemma round_round_div :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (exists n, (beta = 2 * n :> Z)%Z) ->
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  y <> 0 ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x / y).
Proof using .
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Ebeta Hexp x y Nzy Fx Fy.
unfold round_round_eq.
destruct (Rtotal_order x 0) as [Nx|[Zx|Px]].
-

  destruct (Rtotal_order y 0) as [Ny|[Zy|Py]].
  +

    rewrite <- (Ropp_involutive x).
    rewrite <- (Ropp_involutive y).
    rewrite Ropp_div.
    unfold Rdiv; rewrite <- Ropp_inv_permute; [|lra].
    rewrite Ropp_mult_distr_r_reverse.
    rewrite Ropp_involutive.
    fold ((- x) / (- y)).
    apply Ropp_lt_contravar in Nx.
    apply Ropp_lt_contravar in Ny.
    rewrite Ropp_0 in Nx, Ny.
    apply generic_format_opp in Fx.
    apply generic_format_opp in Fy.
    now apply round_round_div_aux.
  +

    now exfalso; apply Nzy.
  +

    rewrite <- (Ropp_involutive x).
    rewrite Ropp_div.
    do 3 rewrite round_N_opp.
    apply Ropp_eq_compat.
    apply Ropp_lt_contravar in Nx.
    rewrite Ropp_0 in Nx.
    apply generic_format_opp in Fx.
    now apply round_round_div_aux.
-

  rewrite Zx.
  unfold Rdiv; rewrite Rmult_0_l.
  now rewrite round_0; [|apply valid_rnd_N].
-

  destruct (Rtotal_order y 0) as [Ny|[Zy|Py]].
  +

    rewrite <- (Ropp_involutive y).
    unfold Rdiv; rewrite <- Ropp_inv_permute; [|lra].
    rewrite Ropp_mult_distr_r_reverse.
    do 3 rewrite round_N_opp.
    apply Ropp_eq_compat.
    apply Ropp_lt_contravar in Ny.
    rewrite Ropp_0 in Ny.
    apply generic_format_opp in Fy.
    now apply round_round_div_aux.
  +

    now exfalso; apply Nzy.
  +

    now apply round_round_div_aux.
Qed.

Section Double_round_div_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_div_hyp :
  (2 * prec <= prec')%Z ->
  round_round_div_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
intros Hprec.
unfold Prec_gt_0 in prec_gt_0_.
unfold FLX_exp.
unfold round_round_div_hyp.
split; [now intro ex; lia|].
split; [|split; [|split]]; intros ex ey; lia.
Qed.

Theorem round_round_div_FLX :
  forall choice1 choice2,
  (exists n, (beta = 2 * n :> Z)%Z) ->
  (2 * prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x / y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Ebeta Hprec x y Nzy Fx Fy.
apply round_round_div.
-
 now apply FLX_exp_valid.
-
 now apply FLX_exp_valid.
-
 exact Ebeta.
-
 now apply FLX_round_round_div_hyp.
-
 exact Nzy.
-
 now apply generic_format_FLX.
-
 now apply generic_format_FLX.
Qed.

End Double_round_div_FLX.

Section Double_round_div_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_div_hyp :
  (emin' <= emin - prec - 2)%Z ->
  (2 * prec <= prec')%Z ->
  round_round_div_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof using prec_gt_0_.
intros Hemin Hprec.
unfold FLT_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_div_hyp.
split; [intro ex|split; [|split; [|split]]; intros ex ey].
-
 generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ex - prec) emin).
  lia.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec') emin').
  lia.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ey - prec) emin).
  generalize (Zmax_spec (ex - ey + 1 - prec) emin).
  generalize (Zmax_spec (ex - ey + 1 - prec') emin').
  lia.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec') emin').
  lia.
-
 generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec') emin').
  lia.
Qed.

Theorem round_round_div_FLT :
  forall choice1 choice2,
  (exists n, (beta = 2 * n :> Z)%Z) ->
  (emin' <= emin - prec - 2)%Z ->
  (2 * prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x / y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Ebeta Hemin Hprec x y Nzy Fx Fy.
apply round_round_div.
-
 now apply FLT_exp_valid.
-
 now apply FLT_exp_valid.
-
 exact Ebeta.
-
 now apply FLT_round_round_div_hyp.
-
 exact Nzy.
-
 now apply generic_format_FLT.
-
 now apply generic_format_FLT.
Qed.

End Double_round_div_FLT.

Section Double_round_div_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_div_hyp :
  (emin' + prec' <= emin - 1)%Z ->
  (2 * prec <= prec')%Z ->
  round_round_div_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof using prec_gt_0_.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_div_hyp.
split; [intro ex|split; [|split; [|split]]; intros ex ey].
-
 destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ex - prec) emin);
  lia.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec') emin');
  lia.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey + 1 - prec) emin);
  destruct (Z.ltb_spec (ex - ey + 1 - prec') emin');
  lia.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec') emin');
  lia.
-
 destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec') emin');
  lia.
Qed.

Theorem round_round_div_FTZ :
  forall choice1 choice2,
  (exists n, (beta = 2 * n :> Z)%Z) ->
  (emin' + prec' <= emin - 1)%Z ->
  (2 * prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x / y).
Proof using prec_gt_0_ prec_gt_0_'.
intros choice1 choice2 Ebeta Hemin Hprec x y Nzy Fx Fy.
apply round_round_div.
-
 now apply FTZ_exp_valid.
-
 now apply FTZ_exp_valid.
-
 exact Ebeta.
-
 now apply FTZ_round_round_div_hyp.
-
 exact Nzy.
-
 now apply generic_format_FTZ.
-
 now apply generic_format_FTZ.
Qed.

End Double_round_div_FTZ.

End Double_round_div.

End Double_round.


Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Core Flocq.Calc.Operations.

Definition Zrnd_odd x :=  match Req_EM_T x (IZR (Zfloor x))  with
  | left _   => Zfloor x
  | right _  => match (Z.even (Zfloor x)) with
      | true => Zceil x
      | false => Zfloor x
     end
  end.

Global Instance valid_rnd_odd : Valid_rnd Zrnd_odd.
Proof.
split.

intros x y Hxy.
assert (Zfloor x <= Zrnd_odd y)%Z.

apply Z.le_trans with (Zfloor y).
now apply Zfloor_le.
unfold Zrnd_odd; destruct (Req_EM_T  y (IZR (Zfloor y))).
now apply Z.le_refl.
case (Z.even (Zfloor y)).
apply le_IZR.
apply Rle_trans with y.
apply Zfloor_lb.
apply Zceil_ub.
now apply Z.le_refl.
unfold Zrnd_odd at 1.

destruct (Req_EM_T  x (IZR (Zfloor x))) as [Hx|Hx].

apply H.

case_eq (Z.even (Zfloor x)); intros Hx2.
2: apply H.
unfold Zrnd_odd; destruct (Req_EM_T  y (IZR (Zfloor y))) as [Hy|Hy].
apply Zceil_glb.
now rewrite <- Hy.
case_eq (Z.even (Zfloor y)); intros Hy2.
now apply Zceil_le.
apply Zceil_glb.
assert (H0:(Zfloor x <= Zfloor y)%Z) by now apply Zfloor_le.
case (Zle_lt_or_eq _ _  H0); intros H1.
apply Rle_trans with (1:=Zceil_ub _).
rewrite Zceil_floor_neq.
apply IZR_le; lia.
now apply sym_not_eq.
contradict Hy2.
rewrite <- H1, Hx2; discriminate.

intros n; unfold Zrnd_odd.
rewrite Zfloor_IZR, Zceil_IZR.
destruct (Req_EM_T  (IZR n) (IZR n)); trivial.
case (Z.even n); trivial.
Qed.

Lemma Zrnd_odd_Zodd: forall x, x <> (IZR (Zfloor x)) ->
  (Z.even (Zrnd_odd x)) = false.
Proof.
intros x Hx; unfold Zrnd_odd.
destruct (Req_EM_T  x (IZR (Zfloor x))) as [H|H].
now contradict H.
case_eq (Z.even (Zfloor x)).

intros H'.
rewrite Zceil_floor_neq.
rewrite Z.even_add, H'.
reflexivity.
now apply sym_not_eq.
trivial.
Qed.

Lemma Zfloor_plus: forall (n:Z) y,
  (Zfloor (IZR n+y) = n + Zfloor y)%Z.
Proof.
intros n y; unfold Zfloor.
unfold Zminus; rewrite Zplus_assoc; f_equal.
apply sym_eq, tech_up.
rewrite plus_IZR.
apply Rplus_lt_compat_l.
apply archimed.
rewrite plus_IZR, Rplus_assoc.
apply Rplus_le_compat_l.
apply Rplus_le_reg_r with (-y)%R.
ring_simplify (y+1+-y)%R.
apply archimed.
Qed.

Lemma Zceil_plus: forall (n:Z) y,
  (Zceil (IZR n+y) = n + Zceil y)%Z.
Proof.
intros n y; unfold Zceil.
rewrite Ropp_plus_distr, <- Ropp_Ropp_IZR.
rewrite Zfloor_plus.
ring.
Qed.

Lemma Zeven_abs: forall z, Z.even (Z.abs z) = Z.even z.
Proof.
intros z; case (Zle_or_lt z 0); intros H1.
rewrite Z.abs_neq; try assumption.
apply Z.even_opp.
rewrite Z.abs_eq; auto with zarith.
Qed.

Lemma Zrnd_odd_plus: forall x y, (x = IZR (Zfloor x)) ->
    Z.even (Zfloor x) = true ->
   (IZR (Zrnd_odd (x+y)) = x+IZR (Zrnd_odd y))%R.
Proof.
intros x y Hx H.
unfold Zrnd_odd; rewrite Hx, Zfloor_plus.
case (Req_EM_T y (IZR (Zfloor y))); intros Hy.
rewrite Hy; repeat rewrite <- plus_IZR.
repeat rewrite Zfloor_IZR.
case (Req_EM_T _ _); intros K; easy.
case (Req_EM_T _ _); intros K.
contradict Hy.
apply Rplus_eq_reg_l with (IZR (Zfloor x)).
now rewrite K, plus_IZR.
rewrite Z.even_add, H; simpl.
case (Z.even (Zfloor y)).
now rewrite Zceil_plus, plus_IZR.
now rewrite plus_IZR.
Qed.

Section Fcore_rnd_odd.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }.

Notation format := (generic_format beta fexp).
Notation canonical := (canonical beta fexp).
Notation cexp := (cexp beta fexp).

Definition Rnd_odd_pt (x f : R) :=
  format f /\ ((f = x)%R \/
    ((Rnd_DN_pt format x f \/ Rnd_UP_pt format x f) /\
    exists g : float beta, f = F2R g /\ canonical g /\ Z.even (Fnum g) = false)).

Definition Rnd_odd (rnd : R -> R) :=
  forall x : R, Rnd_odd_pt x (rnd x).

Theorem Rnd_odd_pt_opp_inv :   forall x f : R,
  Rnd_odd_pt (-x) (-f) -> Rnd_odd_pt x f.
Proof using .
Proof with auto with typeclass_instances.
intros x f (H1,H2).
split.
replace f with (-(-f))%R by ring.
now apply generic_format_opp.
destruct H2.
left.
replace f with (-(-f))%R by ring.
rewrite H; ring.
right.
destruct H as (H2,(g,(Hg1,(Hg2,Hg3)))).
split.
destruct H2.
right.
replace f with (-(-f))%R by ring.
replace x with (-(-x))%R by ring.
apply Rnd_UP_pt_opp...
apply generic_format_opp.
left.
replace f with (-(-f))%R by ring.
replace x with (-(-x))%R by ring.
apply Rnd_DN_pt_opp...
apply generic_format_opp.
exists (Float beta (-Fnum g) (Fexp g)).
split.
rewrite F2R_Zopp.
replace f with (-(-f))%R by ring.
rewrite Hg1; reflexivity.
split.
now apply canonical_opp.
simpl.
now rewrite Z.even_opp.
Qed.

Theorem round_odd_opp :
  forall x,
  round beta fexp Zrnd_odd (-x) = (- round beta fexp Zrnd_odd x)%R.
Proof using .
intros x; unfold round.
rewrite <- F2R_Zopp.
unfold F2R; simpl.
apply f_equal2; apply f_equal.
rewrite scaled_mantissa_opp.
generalize (scaled_mantissa beta fexp x); intros r.
unfold Zrnd_odd.
case (Req_EM_T (- r) (IZR (Zfloor (- r)))).
case (Req_EM_T r (IZR (Zfloor r))).
intros Y1 Y2.
apply eq_IZR.
now rewrite opp_IZR, <- Y1, <-Y2.
intros Y1 Y2.
absurd (r=IZR (Zfloor r)); trivial.
pattern r at 2; replace r with (-(-r))%R by ring.
rewrite Y2, <- opp_IZR.
rewrite Zfloor_IZR.
rewrite opp_IZR, <- Y2.
ring.
case (Req_EM_T r (IZR (Zfloor r))).
intros Y1 Y2.
absurd (-r=IZR (Zfloor (-r)))%R; trivial.
pattern r at 2; rewrite Y1.
rewrite <- opp_IZR, Zfloor_IZR.
now rewrite opp_IZR, <- Y1.
intros Y1 Y2.
unfold Zceil; rewrite Ropp_involutive.
replace  (Z.even (Zfloor (- r))) with (negb (Z.even (Zfloor r))).
case (Z.even (Zfloor r));  simpl; ring.
apply trans_eq with (Z.even (Zceil r)).
rewrite Zceil_floor_neq.
rewrite Z.even_add.
destruct (Z.even (Zfloor r)); reflexivity.
now apply sym_not_eq.
rewrite <- (Z.even_opp (Zfloor (- r))).
reflexivity.
apply cexp_opp.
Qed.

Theorem round_odd_pt :
  forall x,
  Rnd_odd_pt x (round beta fexp Zrnd_odd x).
Proof using exists_NE_ valid_exp.
Proof with auto with typeclass_instances.
cut (forall x : R, (0 < x)%R -> Rnd_odd_pt x (round beta fexp Zrnd_odd x)).
intros H x; case (Rle_or_lt 0 x).
intros H1; destruct H1.
now apply H.
rewrite <- H0.
rewrite round_0...
split.
apply generic_format_0.
now left.
intros Hx; apply Rnd_odd_pt_opp_inv.
rewrite <- round_odd_opp.
apply H.
auto with real.

intros x Hxp.
generalize (generic_format_round beta fexp Zrnd_odd x).
set (o:=round beta fexp Zrnd_odd x).
intros Ho.
split.
assumption.

case (Req_dec o x); intros Hx.
now left.
right.
assert (o=round beta fexp Zfloor x \/ o=round beta fexp Zceil x).
unfold o, round, F2R;simpl.
case (Zrnd_DN_or_UP Zrnd_odd  (scaled_mantissa beta fexp x))...
intros H; rewrite H; now left.
intros H; rewrite H; now right.
split.
destruct H; rewrite H.
left; apply round_DN_pt...
right; apply round_UP_pt...

unfold o, Zrnd_odd, round.
case (Req_EM_T (scaled_mantissa beta fexp x)
     (IZR (Zfloor (scaled_mantissa beta fexp x)))).
intros T.
absurd (o=x); trivial.
apply round_generic...
unfold generic_format, F2R; simpl.
rewrite <- (scaled_mantissa_mult_bpow beta fexp) at 1.
apply f_equal2; trivial; rewrite T at 1.
apply f_equal, sym_eq, Ztrunc_floor.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
intros L.
case_eq (Z.even (Zfloor (scaled_mantissa beta fexp x))).

generalize (generic_format_round beta fexp Zceil x).
unfold generic_format.
set (f:=round beta fexp Zceil x).
set (ef := cexp f).
set (mf := Ztrunc (scaled_mantissa beta fexp f)).
exists (Float beta mf ef).
unfold canonical.
rewrite <- H0.
repeat split; try assumption.
apply trans_eq with (negb (Z.even (Zfloor (scaled_mantissa beta fexp x)))).
2: rewrite H1; reflexivity.
apply trans_eq with (negb (Z.even (Fnum
  (Float beta  (Zfloor (scaled_mantissa beta fexp x)) (cexp x))))).
2: reflexivity.
case (Rle_lt_or_eq_dec 0 (round beta fexp Zfloor x)).
rewrite <- round_0 with beta fexp Zfloor...
apply round_le...
now left.
intros Y.
generalize (DN_UP_parity_generic beta fexp)...
unfold DN_UP_parity_prop.
intros T; apply T with x; clear T.
unfold generic_format.
rewrite <- (scaled_mantissa_mult_bpow beta fexp x) at 1.
unfold F2R; simpl.
apply Rmult_neq_compat_r.
apply Rgt_not_eq, bpow_gt_0.
rewrite Ztrunc_floor.
assumption.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
unfold canonical.
simpl.
apply sym_eq, cexp_DN...
unfold canonical.
rewrite <- H0; reflexivity.
reflexivity.
apply trans_eq with (round beta fexp Ztrunc (round beta fexp Zceil x)).
reflexivity.
apply round_generic...
intros Y.
replace  (Fnum {| Fnum := Zfloor (scaled_mantissa beta fexp x); Fexp := cexp x |})
   with (Fnum (Float beta 0 (fexp (mag beta 0)))).
generalize (DN_UP_parity_generic beta fexp)...
unfold DN_UP_parity_prop.
intros T; apply T with x; clear T.
unfold generic_format.
rewrite <- (scaled_mantissa_mult_bpow beta fexp x) at 1.
unfold F2R; simpl.
apply Rmult_neq_compat_r.
apply Rgt_not_eq, bpow_gt_0.
rewrite Ztrunc_floor.
assumption.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
apply canonical_0.
unfold canonical.
rewrite <- H0; reflexivity.
rewrite <- Y; unfold F2R; simpl; ring.
apply trans_eq with (round beta fexp Ztrunc (round beta fexp Zceil x)).
reflexivity.
apply round_generic...
simpl.
apply eq_IZR, Rmult_eq_reg_r with (bpow (cexp x)).
unfold round, F2R in Y; simpl in Y; rewrite <- Y.
simpl; ring.
apply Rgt_not_eq, bpow_gt_0.

intros Y.
case (Rle_lt_or_eq_dec 0 (round beta fexp Zfloor x)).
rewrite <- round_0 with beta fexp Zfloor...
apply round_le...
now left.
intros Hrx.
set (ef := cexp x).
set (mf := Zfloor (scaled_mantissa beta fexp x)).
exists (Float beta mf ef).
unfold canonical.
repeat split; try assumption.
simpl.
apply trans_eq with (cexp (round beta fexp Zfloor x )).
apply sym_eq, cexp_DN...
reflexivity.
intros Hrx; contradict Y.
replace (Zfloor (scaled_mantissa beta fexp x)) with 0%Z.
simpl; discriminate.
apply eq_IZR, Rmult_eq_reg_r with (bpow (cexp x)).
unfold round, F2R in Hrx; simpl in Hrx; rewrite <- Hrx.
simpl; ring.
apply Rgt_not_eq, bpow_gt_0.
Qed.

Theorem Rnd_odd_pt_unique :
  forall x f1 f2 : R,
  Rnd_odd_pt x f1 -> Rnd_odd_pt x f2 ->
  f1 = f2.
Proof using exists_NE_ valid_exp.
intros x f1 f2 (Ff1,H1) (Ff2,H2).

case (generic_format_EM beta fexp x); intros L.
apply trans_eq with x.
case H1; try easy.
intros (J,_); case J; intros J'.
apply Rnd_DN_pt_idempotent with format; assumption.
apply Rnd_UP_pt_idempotent with format; assumption.
case H2; try easy.
intros (J,_); case J; intros J'; apply sym_eq.
apply Rnd_DN_pt_idempotent with format; assumption.
apply Rnd_UP_pt_idempotent with format; assumption.

destruct H1 as [H1|(H1,H1')].
contradict L; now rewrite <- H1.
destruct H2 as [H2|(H2,H2')].
contradict L; now rewrite <- H2.
destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
apply Rnd_DN_pt_unique with format x; assumption.
destruct H1' as (ff,(K1,(K2,K3))).
destruct H2' as (gg,(L1,(L2,L3))).
absurd (true = false); try discriminate.
rewrite <- L3.
apply trans_eq with (negb (Z.even (Fnum ff))).
rewrite K3; easy.
apply sym_eq.
generalize (DN_UP_parity_generic beta fexp).
unfold DN_UP_parity_prop; intros T; apply (T x); clear T; try assumption...
rewrite <- K1; apply Rnd_DN_pt_unique with (generic_format beta fexp) x; try easy...
now apply round_DN_pt...
rewrite <- L1; apply Rnd_UP_pt_unique with (generic_format beta fexp) x; try easy...
now apply round_UP_pt...

destruct H1' as (ff,(K1,(K2,K3))).
destruct H2' as (gg,(L1,(L2,L3))).
absurd (true = false); try discriminate.
rewrite <- K3.
apply trans_eq with (negb (Z.even (Fnum gg))).
rewrite L3; easy.
apply sym_eq.
generalize (DN_UP_parity_generic beta fexp).
unfold DN_UP_parity_prop; intros T; apply (T x); clear T; try assumption...
rewrite <- L1; apply Rnd_DN_pt_unique with (generic_format beta fexp) x; try easy...
now apply round_DN_pt...
rewrite <- K1; apply Rnd_UP_pt_unique with (generic_format beta fexp) x; try easy...
now apply round_UP_pt...
apply Rnd_UP_pt_unique with format x; assumption.
Qed.

Theorem Rnd_odd_pt_monotone :
  round_pred_monotone (Rnd_odd_pt).
Proof using exists_NE_ valid_exp.
Proof with auto with typeclass_instances.
intros x y f g H1 H2 Hxy.
apply Rle_trans with (round beta fexp Zrnd_odd x).
right; apply Rnd_odd_pt_unique with x; try assumption.
apply round_odd_pt.
apply Rle_trans with (round beta fexp Zrnd_odd y).
apply round_le...
right; apply Rnd_odd_pt_unique with y; try assumption.
apply round_odd_pt.
Qed.

End Fcore_rnd_odd.

Section Odd_prop_aux.

Variable beta : radix.
Hypothesis Even_beta: Z.even (radix_val beta)=true.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Variable fexpe : Z -> Z.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }.

Context { valid_expe : Valid_exp fexpe }.
Context { exists_NE_e : Exists_NE beta fexpe }.

Hypothesis fexpe_fexp: forall e, (fexpe e <= fexp e -2)%Z.

Lemma generic_format_fexpe_fexp: forall x,
 generic_format beta fexp x ->  generic_format beta fexpe x.
Proof using fexpe_fexp.
intros x Hx.
apply generic_inclusion_mag with fexp; trivial; intros Hx2.
generalize (fexpe_fexp (mag beta x)).
lia.
Qed.

Lemma exists_even_fexp_lt: forall (c:Z->Z), forall (x:R),
      (exists f:float beta, F2R f = x /\ (c (mag beta x) < Fexp f)%Z) ->
      exists f:float beta, F2R f =x /\ canonical beta c f /\ Z.even (Fnum f) = true.
Proof using Even_beta.
Proof with auto with typeclass_instances.
intros c x (g,(Hg1,Hg2)).
exists (Float beta
     (Fnum g*Z.pow (radix_val beta) (Fexp g - c (mag beta x)))
     (c (mag beta x))).
assert (F2R (Float beta
     (Fnum g*Z.pow (radix_val beta) (Fexp g - c (mag beta x)))
     (c (mag beta x))) = x).
unfold F2R; simpl.
rewrite mult_IZR, IZR_Zpower.
rewrite Rmult_assoc, <- bpow_plus.
rewrite <- Hg1; unfold F2R.
apply f_equal, f_equal.
ring.
lia.
split; trivial.
split.
unfold canonical, cexp.
now rewrite H.
simpl.
rewrite Z.even_mul.
rewrite Z.even_pow.
rewrite Even_beta.
apply Bool.orb_true_intro.
now right.
lia.
Qed.

Variable choice:Z->bool.
Variable x:R.

Variable d u: float beta.
Hypothesis Hd: Rnd_DN_pt (generic_format beta fexp) x (F2R d).
Hypothesis Cd: canonical beta fexp d.
Hypothesis Hu: Rnd_UP_pt (generic_format beta fexp) x (F2R u).
Hypothesis Cu: canonical beta fexp u.

Hypothesis xPos: (0 < x)%R.

Let m:= ((F2R d+F2R u)/2)%R.

Lemma d_eq: F2R d= round beta fexp Zfloor x.
Proof using Hd valid_exp.
Proof with auto with typeclass_instances.
apply Rnd_DN_pt_unique with (generic_format beta fexp) x...
apply round_DN_pt...
Qed.

Lemma u_eq: F2R u= round beta fexp Zceil x.
Proof using Hu valid_exp.
Proof with auto with typeclass_instances.
apply Rnd_UP_pt_unique with (generic_format beta fexp) x...
apply round_UP_pt...
Qed.

Lemma d_ge_0: (0 <= F2R d)%R.
Proof using Hd valid_exp xPos.
Proof with auto with typeclass_instances.
rewrite d_eq; apply round_ge_generic...
apply generic_format_0.
now left.
Qed.

Lemma mag_d:  (0< F2R d)%R ->
    (mag beta (F2R d) = mag beta x :>Z).
Proof using Hd valid_exp.
Proof with auto with typeclass_instances.
intros Y.
rewrite d_eq; apply mag_DN...
now rewrite <- d_eq.
Qed.

Lemma Fexp_d: (0 < F2R d)%R -> Fexp d =fexp (mag beta x).
Proof using Cd Hd valid_exp.
Proof with auto with typeclass_instances.
intros Y.
now rewrite Cd, <- mag_d.
Qed.

Lemma format_bpow_x: (0 < F2R d)%R
    -> generic_format beta fexp  (bpow (mag beta x)).
Proof using Cd Hd valid_exp.
Proof with auto with typeclass_instances.
intros Y.
apply generic_format_bpow.
apply valid_exp.
rewrite <- Fexp_d; trivial.
apply Z.lt_le_trans with  (mag beta (F2R d))%Z.
rewrite Cd; apply mag_generic_gt...
now apply Rgt_not_eq.
apply Hd.
apply mag_le; trivial.
apply Hd.
Qed.

Lemma format_bpow_d: (0 < F2R d)%R ->
  generic_format beta fexp (bpow (mag beta (F2R d))).
Proof using Cd valid_exp.
Proof with auto with typeclass_instances.
intros Y; apply generic_format_bpow.
apply valid_exp.
apply mag_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonical.
Qed.

Lemma d_le_m: (F2R d <= m)%R.
Proof using Hd Hu.
assert (F2R d <= F2R u)%R.
  apply Rle_trans with x.
  apply Hd.
  apply Hu.
unfold m.
lra.
Qed.

Lemma m_le_u: (m <= F2R u)%R.
Proof using Hd Hu.
assert (F2R d <= F2R u)%R.
  apply Rle_trans with x.
  apply Hd.
  apply Hu.
unfold m.
lra.
Qed.

Lemma mag_m: (0 < F2R d)%R -> (mag beta m =mag beta (F2R d) :>Z).
Proof using Cd Hd Hu valid_exp.
Proof with auto with typeclass_instances.
intros dPos; apply mag_unique_pos.
split.
apply Rle_trans with (F2R d).
destruct (mag beta (F2R d)) as (e,He).
simpl.
rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
apply d_le_m.
case m_le_u; intros H.
apply Rlt_le_trans with (1:=H).
rewrite u_eq.
apply round_le_generic...
apply generic_format_bpow.
apply valid_exp.
apply mag_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonical.
case (Rle_or_lt x (bpow (mag beta (F2R d)))); trivial; intros Z.
absurd ((bpow (mag beta (F2R d)) <= (F2R d)))%R.
apply Rlt_not_le.
destruct  (mag beta (F2R d)) as (e,He).
simpl in *; rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
apply Rle_trans with (round beta fexp Zfloor x).
2: right; apply sym_eq, d_eq.
apply round_ge_generic...
apply generic_format_bpow.
apply valid_exp.
apply mag_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonical.
now left.
replace m with (F2R d).
destruct (mag beta (F2R d)) as (e,He).
simpl in *; rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
unfold m in H |- *.
lra.
Qed.

Lemma mag_m_0: (0 = F2R d)%R
    -> (mag beta m =mag beta (F2R u)-1:>Z)%Z.
Proof using Hd Hu valid_exp xPos.
Proof with auto with typeclass_instances.
intros Y.
apply mag_unique_pos.
unfold m; rewrite <- Y, Rplus_0_l.
rewrite u_eq.
destruct (mag beta x) as (e,He).
rewrite Rabs_pos_eq in He by now apply Rlt_le.
rewrite round_UP_small_pos with (ex:=e).
rewrite mag_bpow.
ring_simplify (fexp e + 1 - 1)%Z.
split.
unfold Zminus; rewrite bpow_plus.
unfold Rdiv; apply Rmult_le_compat_l.
apply bpow_ge_0.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r; apply Rinv_le.
exact Rlt_0_2.
apply IZR_le.
specialize (radix_gt_1 beta).
lia.
apply Rlt_le_trans with (bpow (fexp e)*1)%R.
2: right; ring.
unfold Rdiv; apply Rmult_lt_compat_l.
apply bpow_gt_0.
lra.
now apply He, Rgt_not_eq.
apply exp_small_round_0_pos with beta (Zfloor) x...
now apply He, Rgt_not_eq.
now rewrite <- d_eq, Y.
Qed.

Lemma u'_eq:  (0 < F2R d)%R -> exists f:float beta, F2R f = F2R u /\ (Fexp f = Fexp d)%Z.
Proof using Cd Hd Hu valid_exp.
Proof with auto with typeclass_instances.
intros Y.
rewrite u_eq; unfold round.
eexists; repeat split.
simpl; now rewrite Fexp_d.
Qed.

Lemma m_eq :
  (0 < F2R d)%R ->
  exists f:float beta,
  F2R f = m /\ (Fexp f = fexp (mag beta x) - 1)%Z.
Proof using Cd Even_beta Hd Hu valid_exp.
Proof with auto with typeclass_instances.
intros Y.
specialize (Zeven_ex (radix_val beta)); rewrite Even_beta.
intros (b, Hb); rewrite Zplus_0_r in Hb.
destruct u'_eq as (u', (Hu'1,Hu'2)); trivial.
exists (Fmult (Float beta b (-1)) (Fplus d u'))%R.
split.
rewrite F2R_mult, F2R_plus, Hu'1.
unfold m; rewrite Rmult_comm.
unfold Rdiv; apply f_equal.
unfold F2R; simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Hb, mult_IZR.
simpl; field.
apply Rgt_not_eq, Rmult_lt_reg_l with (1 := Rlt_0_2).
rewrite Rmult_0_r, <- (mult_IZR 2), <-Hb.
apply radix_pos.
apply trans_eq with (-1+Fexp (Fplus d u'))%Z.
unfold Fmult.
destruct  (Fplus d u'); reflexivity.
rewrite Zplus_comm; unfold Zminus; apply f_equal2.
2: reflexivity.
rewrite Fexp_Fplus.
rewrite Z.min_l.
now rewrite Fexp_d.
rewrite Hu'2; lia.
Qed.

Lemma m_eq_0: (0 = F2R d)%R ->  exists f:float beta,
   F2R f = m /\ (Fexp f = fexp (mag beta (F2R u)) -1)%Z.
Proof using Cu Even_beta Hu.
Proof with auto with typeclass_instances.
intros Y.
specialize (Zeven_ex (radix_val beta)); rewrite Even_beta.
intros (b, Hb); rewrite Zplus_0_r in Hb.
exists (Fmult (Float beta b (-1)) u)%R.
split.
rewrite F2R_mult; unfold m; rewrite <- Y, Rplus_0_l.
rewrite Rmult_comm.
unfold Rdiv; apply f_equal.
unfold F2R; simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Hb, mult_IZR.
simpl; field.
apply Rgt_not_eq, Rmult_lt_reg_l with (1 := Rlt_0_2).
rewrite Rmult_0_r, <- (mult_IZR 2), <-Hb.
apply radix_pos.
apply trans_eq with (-1+Fexp u)%Z.
unfold Fmult.
destruct u; reflexivity.
rewrite Zplus_comm, Cu; unfold Zminus; now apply f_equal2.
Qed.

Lemma fexp_m_eq_0:  (0 = F2R d)%R ->
  (fexp (mag beta (F2R u)-1) < fexp (mag beta (F2R u))+1)%Z.
Proof using Even_beta Hd Hu exists_NE_ valid_exp xPos.
Proof with auto with typeclass_instances.
intros Y.
assert ((fexp (mag beta (F2R u) - 1) <= fexp (mag beta (F2R u))))%Z.
2: lia.
destruct (mag beta x) as (e,He).
rewrite Rabs_right in He.
2: now left.
assert (e <= fexp e)%Z.
apply exp_small_round_0_pos with beta (Zfloor) x...
now apply He, Rgt_not_eq.
now rewrite <- d_eq, Y.
rewrite u_eq, round_UP_small_pos with (ex:=e); trivial.
2: now apply He, Rgt_not_eq.
rewrite mag_bpow.
ring_simplify (fexp e + 1 - 1)%Z.
replace (fexp (fexp e)) with (fexp e).
case exists_NE_; intros V.
contradict V; rewrite Even_beta; discriminate.
rewrite (proj2 (V e)); lia.
apply sym_eq, valid_exp; lia.
Qed.

Lemma Fm:  generic_format beta fexpe m.
Proof using Cd Cu Even_beta Hd Hu exists_NE_ fexpe_fexp valid_exp xPos.
case (d_ge_0); intros Y.

destruct m_eq as (g,(Hg1,Hg2)); trivial.
apply generic_format_F2R' with g.
now apply sym_eq.
intros H; unfold cexp; rewrite Hg2.
rewrite mag_m; trivial.
rewrite <- Fexp_d; trivial.
rewrite Cd.
unfold cexp.
generalize (fexpe_fexp (mag beta (F2R d))).
lia.

destruct m_eq_0 as (g,(Hg1,Hg2)); trivial.
apply generic_format_F2R' with g.
assumption.
intros H; unfold cexp; rewrite Hg2.
rewrite mag_m_0; try assumption.
apply Z.le_trans with (1:=fexpe_fexp _).
generalize (fexp_m_eq_0 Y).
lia.
Qed.

Lemma Zm:
   exists g : float beta, F2R g = m /\ canonical beta fexpe g /\ Z.even (Fnum g) = true.
Proof using Cd Cu Even_beta Hd Hu exists_NE_ fexpe_fexp valid_exp xPos.
Proof with auto with typeclass_instances.
case (d_ge_0); intros Y.

destruct m_eq as (g,(Hg1,Hg2)); trivial.
apply exists_even_fexp_lt.
exists g; split; trivial.
rewrite Hg2.
rewrite mag_m; trivial.
rewrite <- Fexp_d; trivial.
rewrite Cd.
unfold cexp.
generalize (fexpe_fexp  (mag beta (F2R d))).
lia.

destruct m_eq_0 as (g,(Hg1,Hg2)); trivial.
apply exists_even_fexp_lt.
exists g; split; trivial.
rewrite Hg2.
rewrite mag_m_0; trivial.
apply Z.le_lt_trans with (1:=fexpe_fexp _).
generalize (fexp_m_eq_0 Y).
lia.
Qed.

Lemma DN_odd_d_aux :
  forall z, (F2R d <= z < F2R u)%R ->
  Rnd_DN_pt (generic_format beta fexp) z (F2R d).
Proof using Hd Hu valid_exp.
Proof with auto with typeclass_instances.
intros z Hz1.
replace (F2R d) with (round beta fexp Zfloor z).
apply round_DN_pt...
case (Rnd_DN_UP_pt_split _ _ _ _ Hd Hu (round beta fexp Zfloor z)).
apply generic_format_round...
intros Y; apply Rle_antisym; trivial.
apply round_DN_pt...
apply Hd.
apply Hz1.
intros Y ; elim (Rlt_irrefl z).
apply Rlt_le_trans with (1:=proj2 Hz1), Rle_trans with (1:=Y).
apply round_DN_pt...
Qed.

Lemma UP_odd_d_aux :
  forall z, (F2R d < z <= F2R u)%R ->
  Rnd_UP_pt (generic_format beta fexp) z (F2R u).
Proof using Hd Hu valid_exp.
Proof with auto with typeclass_instances.
intros z Hz1.
replace (F2R u) with (round beta fexp Zceil z).
apply round_UP_pt...
case (Rnd_DN_UP_pt_split _ _ _ _ Hd Hu (round beta fexp Zceil z)).
apply generic_format_round...
intros Y ; elim (Rlt_irrefl z).
apply Rle_lt_trans with (2:=proj1 Hz1), Rle_trans with (2:=Y).
apply round_UP_pt...
intros Y; apply Rle_antisym; trivial.
apply round_UP_pt...
apply Hu.
apply Hz1.
Qed.

Lemma round_N_odd_pos :
  round beta fexp (Znearest choice) (round beta fexpe Zrnd_odd x) =
               round beta fexp (Znearest choice) x.
Proof using Cd Cu Even_beta Hd Hu exists_NE_ exists_NE_e fexpe_fexp m valid_exp valid_expe xPos.
Proof with auto with typeclass_instances.
set (o:=round beta fexpe Zrnd_odd x).
case (generic_format_EM beta fexp x); intros Hx.
replace o with x; trivial.
unfold o; apply sym_eq, round_generic...
now apply generic_format_fexpe_fexp.
assert (K1:(F2R d <= o)%R).
apply round_ge_generic...
apply generic_format_fexpe_fexp, Hd.
apply Hd.
assert (K2:(o <= F2R u)%R).
apply round_le_generic...
apply generic_format_fexpe_fexp, Hu.
apply Hu.
assert (P:(x <> m -> o=m -> (forall P:Prop, P))).
intros Y1 Y2.
assert (H:(Rnd_odd_pt beta fexpe x o)).
apply round_odd_pt...
destruct H as (_,H); destruct H.
absurd (x=m)%R; try trivial.
now rewrite <- Y2, H.
destruct H as (_,(k,(Hk1,(Hk2,Hk3)))).
destruct Zm as (k',(Hk'1,(Hk'2,Hk'3))).
absurd (true=false).
discriminate.
rewrite <- Hk3, <- Hk'3.
apply f_equal, f_equal.
apply canonical_unique with fexpe...
now rewrite Hk'1, <- Y2.
assert (generic_format beta fexp o -> (forall P:Prop, P)).
intros Y.
assert (H:(Rnd_odd_pt beta fexpe x o)).
apply round_odd_pt...
destruct H as (_,H); destruct H.
absurd (generic_format beta fexp x); trivial.
now rewrite <- H.
destruct H as (_,(k,(Hk1,(Hk2,Hk3)))).
destruct (exists_even_fexp_lt fexpe o) as (k',(Hk'1,(Hk'2,Hk'3))).
eexists; split.
apply sym_eq, Y.
simpl; unfold cexp.
apply Z.le_lt_trans with (1:=fexpe_fexp _).
lia.
absurd (true=false).
discriminate.
rewrite <- Hk3, <- Hk'3.
apply f_equal, f_equal.
apply canonical_unique with fexpe...
now rewrite Hk'1, <- Hk1.
case K1; clear K1; intros K1.
2: apply H; rewrite <- K1; apply Hd.
case K2; clear K2; intros K2.
2: apply H; rewrite K2; apply Hu.
case (Rle_or_lt  x m); intros Y;[destruct Y|idtac].

apply trans_eq with (F2R d).
apply round_N_eq_DN_pt with (F2R u)...
apply DN_odd_d_aux; split; try left; assumption.
apply UP_odd_d_aux; split; try left; assumption.
assert (o <= (F2R d + F2R u) / 2)%R.
apply round_le_generic...
apply Fm.
now left.
destruct H1; trivial.
apply P.
now apply Rlt_not_eq.
trivial.
apply sym_eq, round_N_eq_DN_pt with (F2R u)...

replace o with x.
reflexivity.
apply sym_eq, round_generic...
rewrite H0; apply Fm.

apply trans_eq with (F2R u).
apply round_N_eq_UP_pt with (F2R d)...
apply DN_odd_d_aux; split; try left; assumption.
apply UP_odd_d_aux; split; try left; assumption.
assert ((F2R d + F2R u) / 2 <= o)%R.
apply round_ge_generic...
apply Fm.
now left.
destruct H0; trivial.
apply P.
now apply Rgt_not_eq.
rewrite <- H0; trivial.
apply sym_eq, round_N_eq_UP_pt with (F2R d)...
Qed.

End Odd_prop_aux.

Section Odd_prop.

Variable beta : radix.
Hypothesis Even_beta: Z.even (radix_val beta)=true.

Variable fexp : Z -> Z.
Variable fexpe : Z -> Z.
Variable choice:Z->bool.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }.

Context { valid_expe : Valid_exp fexpe }.
Context { exists_NE_e : Exists_NE beta fexpe }.

Hypothesis fexpe_fexp: forall e, (fexpe e <= fexp e -2)%Z.

Theorem round_N_odd :
  forall x,
  round beta fexp (Znearest choice) (round beta fexpe Zrnd_odd x) =
               round beta fexp (Znearest choice) x.
Proof using Even_beta exists_NE_ exists_NE_e fexpe_fexp valid_exp valid_expe.
Proof with auto with typeclass_instances.
intros x.
case (total_order_T x 0); intros H; [case H; clear H; intros H | idtac].
rewrite <- (Ropp_involutive x).
rewrite round_odd_opp.
rewrite 2!round_N_opp.
apply f_equal.
destruct (canonical_generic_format beta fexp (round beta fexp Zfloor (-x))) as (d,(Hd1,Hd2)).
apply generic_format_round...
destruct (canonical_generic_format beta fexp (round beta fexp Zceil (-x))) as (u,(Hu1,Hu2)).
apply generic_format_round...
apply round_N_odd_pos with d u...
rewrite <- Hd1; apply round_DN_pt...
rewrite <- Hu1; apply round_UP_pt...
auto with real.

rewrite H; repeat rewrite round_0...

destruct (canonical_generic_format beta fexp (round beta fexp Zfloor x)) as (d,(Hd1,Hd2)).
apply generic_format_round...
destruct (canonical_generic_format beta fexp (round beta fexp Zceil x)) as (u,(Hu1,Hu2)).
apply generic_format_round...
apply round_N_odd_pos with d u...
rewrite <- Hd1; apply round_DN_pt...
rewrite <- Hu1; apply round_UP_pt...
Qed.

End Odd_prop.

Section Odd_propbis.

Variable beta : radix.
Hypothesis Even_beta: Z.even (radix_val beta)=true.

Variable emin prec:Z.
Variable choice:Z->bool.

Hypothesis prec_gt_1: (1 < prec)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation cexp_flt := (cexp beta (FLT_exp emin prec)).
Notation fexpe k := (FLT_exp (emin-k) (prec+k)).

Lemma Zrnd_odd_plus': forall x y,
  (exists n:Z, exists e:Z, (x = IZR n*bpow beta e)%R /\ (1 <= e)%Z) ->
   (IZR (Zrnd_odd (x+y)) = x+IZR (Zrnd_odd y))%R.
Proof using Even_beta.
intros x y (n,(e,(H1,H2))).
apply Zrnd_odd_plus.
rewrite H1.
rewrite <- IZR_Zpower.
2: auto with zarith.
now rewrite <- mult_IZR, Zfloor_IZR.
rewrite H1, <- IZR_Zpower.
2: auto with zarith.
rewrite <- mult_IZR, Zfloor_IZR.
rewrite Z.even_mul.
rewrite Z.even_pow.
2: auto with zarith.
rewrite Even_beta.
apply Bool.orb_true_iff; now right.
Qed.

Theorem mag_round_odd: forall (x:R),
 (emin < mag beta x)%Z ->
  (mag_val beta _ (mag beta (round beta (FLT_exp emin prec) Zrnd_odd x))
      = mag_val beta x (mag beta x))%Z.
Proof using Even_beta prec_gt_1.
Proof with auto with typeclass_instances.
intros x.
assert (T:Prec_gt_0 prec).
unfold Prec_gt_0; auto with zarith.
case (Req_dec x 0); intros Zx.
intros _; rewrite Zx, round_0...
destruct (mag beta x) as (e,He); simpl; intros H.
apply mag_unique; split.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
now apply Z.lt_le_pred.
now apply He.
assert (V:
  (Rabs (round beta (FLT_exp emin prec) Zrnd_odd x) <= bpow beta e)%R).
apply abs_round_le_generic...
apply generic_format_FLT_bpow...
now apply Zlt_le_weak.
left; now apply He.
case V; try easy; intros K.
assert (H0:Rnd_odd_pt beta (FLT_exp emin prec) x (round beta (FLT_exp emin prec) Zrnd_odd x)).
apply round_odd_pt...
destruct H0 as (_,HH); destruct HH as [H0|(H0,(g,(Hg1,(Hg2,Hg3))))].
absurd (Rabs x < bpow beta e)%R.
apply Rle_not_lt; right.
now rewrite <- H0,K.
now apply He.
pose (gg:=Float beta (Zpower beta (e-FLT_exp emin prec (e+1))) (FLT_exp emin prec (e+1))).
assert (Y1: F2R gg = bpow beta e).
unfold F2R; simpl.
rewrite IZR_Zpower.
rewrite <- bpow_plus.
f_equal; ring.
assert (FLT_exp emin prec (e+1) <= e)%Z; [idtac|auto with zarith].
unfold FLT_exp.
apply Z.max_case_strong; auto with zarith.
assert (Y2: canonical beta (FLT_exp emin prec) gg).
unfold canonical; rewrite Y1; unfold gg; simpl.
unfold cexp; now rewrite mag_bpow.
assert (Y3: Fnum gg = Z.abs (Fnum g)).
apply trans_eq with (Fnum (Fabs g)).
2: destruct g; unfold Fabs; now simpl.
f_equal.
apply canonical_unique with (FLT_exp emin prec); try assumption.
destruct g; unfold Fabs; apply canonical_abs; easy.
now rewrite Y1, F2R_abs, <- Hg1,K.
assert (Y4: Z.even (Fnum gg) = true).
unfold gg; simpl.
rewrite Z.even_pow; try assumption.
assert (FLT_exp emin prec (e+1) < e)%Z; [idtac|auto with zarith].
unfold FLT_exp.
apply Z.max_case_strong; auto with zarith.
absurd (true = false).
discriminate.
rewrite <- Hg3.
rewrite <- Zeven_abs.
now rewrite <- Y3.
Qed.

Theorem fexp_round_odd: forall (x:R),
  (cexp_flt (round beta (FLT_exp emin prec) Zrnd_odd x)
      = cexp_flt x)%Z.
Proof using Even_beta prec_gt_1.
Proof with auto with typeclass_instances.
intros x.
assert (G0:Valid_exp (FLT_exp emin prec)).
apply FLT_exp_valid; unfold Prec_gt_0; auto with zarith.
case (Req_dec x 0); intros Zx.
rewrite Zx, round_0...
case (Zle_or_lt (mag beta x) emin).
unfold cexp; destruct (mag beta x) as (e,He); simpl.
intros H; unfold FLT_exp at 4.
rewrite Z.max_r.
2: auto with zarith.
apply Z.max_r.
assert (G: Rabs (round beta (FLT_exp emin prec) Zrnd_odd x) = bpow beta emin).
assert (G1: (Rabs (round beta (FLT_exp emin prec) Zrnd_odd x) <= bpow beta emin)%R).
apply abs_round_le_generic...
apply generic_format_bpow'...
unfold FLT_exp; rewrite Z.max_r; auto with zarith.
left; apply Rlt_le_trans with (bpow beta e).
now apply He.
now apply bpow_le.
assert (G2: (0 <= Rabs (round beta (FLT_exp emin prec) Zrnd_odd x))%R).
apply Rabs_pos.
assert (G3: (Rabs (round beta (FLT_exp emin prec) Zrnd_odd x) <> 0)%R).
assert (H0:Rnd_odd_pt beta (FLT_exp emin prec) x
    (round beta (FLT_exp emin prec) Zrnd_odd x)).
apply round_odd_pt...
destruct H0 as (_,H0); destruct H0 as [H0|(_,(g,(Hg1,(Hg2,Hg3))))].
apply Rgt_not_eq; rewrite H0.
apply Rlt_le_trans with (bpow beta (e-1)).
apply bpow_gt_0.
now apply He.
rewrite Hg1; intros K.
contradict Hg3.
replace (Fnum g) with 0%Z.
easy.
case (Z.eq_dec (Fnum g) Z0); intros W; try easy.
contradict K.
apply Rabs_no_R0.
now apply F2R_neq_0.
apply Rle_antisym; try assumption.
apply Rle_trans with (succ beta (FLT_exp emin prec) 0).
right; rewrite succ_0.
rewrite ulp_FLT_small; try easy.
unfold Prec_gt_0; auto with zarith.
rewrite Rabs_R0; apply bpow_gt_0.
apply succ_le_lt...
apply generic_format_0.
apply generic_format_abs; apply generic_format_round...
case G2; [easy|intros; now contradict G3].
rewrite <- mag_abs.
rewrite G, mag_bpow; auto with zarith.
intros H; unfold cexp.
now rewrite mag_round_odd.
Qed.

End Odd_propbis.
