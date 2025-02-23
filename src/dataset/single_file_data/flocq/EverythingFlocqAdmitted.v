(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-R" "src" "Flocq" "-top" "Everything") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 49 lines to 48 lines, then from 62 lines to 1308 lines, then from 1261 lines to 339 lines, then from 352 lines to 4922 lines, then from 4926 lines to 1721 lines, then from 1734 lines to 2634 lines, then from 2638 lines to 1912 lines, then from 1925 lines to 4487 lines, then from 4460 lines to 2408 lines, then from 2421 lines to 3276 lines, then from 3258 lines to 2626 lines, then from 2639 lines to 2833 lines, then from 2838 lines to 2684 lines, then from 2697 lines to 3082 lines, then from 3087 lines to 2795 lines, then from 2808 lines to 3437 lines, then from 3442 lines to 3049 lines, then from 3062 lines to 30928 lines, then from 30464 lines to 10050 lines, then from 10063 lines to 10650 lines, then from 10654 lines to 10242 lines, then from 10255 lines to 11034 lines, then from 11039 lines to 10544 lines, then from 10553 lines to 12034 lines, then from 12039 lines to 11584 lines, then from 11593 lines to 15454 lines, then from 15459 lines to 13017 lines, then from 13026 lines to 14035 lines, then from 14039 lines to 13421 lines, then from 13430 lines to 13794 lines, then from 13798 lines to 13522 lines, then from 13531 lines to 13753 lines, then from 13758 lines to 13591 lines, then from 13600 lines to 13798 lines, then from 13803 lines to 13655 lines, then from 13664 lines to 14878 lines, then from 14883 lines to 14201 lines, then from 14210 lines to 14256 lines, then from 14261 lines to 14216 lines, then from 14225 lines to 14785 lines, then from 14790 lines to 14417 lines, then from 14426 lines to 14820 lines, then from 14824 lines to 14582 lines, then from 14591 lines to 14723 lines, then from 14728 lines to 14652 lines, then from 14661 lines to 15230 lines, then from 15235 lines to 14774 lines, then from 14783 lines to 17464 lines, then from 17455 lines to 15534 lines, then from 15543 lines to 15726 lines, then from 15731 lines to 15651 lines, then from 15660 lines to 15840 lines, then from 15845 lines to 15720 lines, then from 15729 lines to 18169 lines, then from 18170 lines to 16695 lines, then from 16704 lines to 18411 lines, then from 18413 lines to 17234 lines, then from 17243 lines to 17953 lines, then from 17958 lines to 17551 lines, then from 17560 lines to 18136 lines, then from 18140 lines to 17819 lines, then from 17828 lines to 19009 lines, then from 19014 lines to 18250 lines, then from 18259 lines to 18362 lines, then from 18367 lines to 18326 lines, then from 18335 lines to 20793 lines, then from 20793 lines to 19297 lines, then from 19306 lines to 20343 lines, then from 20348 lines to 19804 lines, then from 19809 lines to 19806 lines *)
(* coqc version 9.1+alpha compiled with OCaml 4.14.2
   coqtop version 9.1+alpha
   Expected coqc runtime on this file: 2.578 sec *)
Require Corelib.Init.Ltac.
Require Stdlib.ZArith.ZArith.
Require Stdlib.Reals.Reals.
Require Stdlib.micromega.Lia.
Require Stdlib.Floats.SpecFloat.
Require Stdlib.ZArith.Zquot.
Require Stdlib.micromega.Psatz.
Require Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Stdlib.Floats.Floats.
Require Stdlib.Lists.List.
Require Stdlib.Arith.PeanoNat.

Inductive False : Prop := .
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.

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
Admitted.

Theorem Zgt_not_eq :
  forall x y : Z,
  (y < x)%Z -> (x <> y)%Z.
Admitted.

End Zmissing.

Section Proof_Irrelevance.

Scheme eq_dep_elim := Induction for eq Sort Type.

Definition eqbool_dep P (h1 : P true) b :=
  match b return P b -> Prop with
  | true => fun (h2 : P true) => h1 = h2
  | false => fun (h2 : P false) => False
  end.

Lemma eqbool_irrelevance : forall (b : bool) (h1 h2 : b = true), h1 = h2.
Admitted.

End Proof_Irrelevance.

Section Even_Odd.

Theorem Zeven_ex :
  forall x, exists p, x = (2 * p + if Z.even x then 0 else 1)%Z.
Admitted.

End Even_Odd.

Section Zpower.

Theorem Zpower_plus :
  forall n k1 k2, (0 <= k1)%Z -> (0 <= k2)%Z ->
  Zpower n (k1 + k2) = (Zpower n k1 * Zpower n k2)%Z.
Admitted.

Theorem Zpower_Zpower_nat :
  forall b e, (0 <= e)%Z ->
  Zpower b e = Zpower_nat b (Z.abs_nat e).
Admitted.

Theorem Zpower_nat_S :
  forall b e,
  Zpower_nat b (S e) = (b * Zpower_nat b e)%Z.
Admitted.

Theorem Zpower_pos_gt_0 :
  forall b p, (0 < b)%Z ->
  (0 < Zpower_pos b p)%Z.
Admitted.

Theorem Zeven_Zpower_odd :
  forall b e, (0 <= e)%Z -> Z.even b = false ->
  Z.even (Zpower b e) = false.
Admitted.

Record radix := { radix_val :> Z ; radix_prop : Zle_bool 2 radix_val = true }.

Theorem radix_val_inj :
  forall r1 r2, radix_val r1 = radix_val r2 -> r1 = r2.
Admitted.

Definition radix2 := Build_radix 2 (refl_equal _).

Variable r : radix.

Theorem radix_gt_0 : (0 < r)%Z.
Proof using .
Admitted.

Theorem radix_gt_1 : (1 < r)%Z.
Proof using .
Admitted.

Theorem Zpower_gt_1 :
  forall p,
  (0 < p)%Z ->
  (1 < Zpower r p)%Z.
Proof using .
Admitted.

Theorem Zpower_gt_0 :
  forall p,
  (0 <= p)%Z ->
  (0 < Zpower r p)%Z.
Proof using .
Admitted.

Theorem Zpower_ge_0 :
  forall e,
  (0 <= Zpower r e)%Z.
Proof using .
Admitted.

Theorem Zpower_le :
  forall e1 e2, (e1 <= e2)%Z ->
  (Zpower r e1 <= Zpower r e2)%Z.
Proof using .
Admitted.

Theorem Zpower_lt :
  forall e1 e2, (0 <= e2)%Z -> (e1 < e2)%Z ->
  (Zpower r e1 < Zpower r e2)%Z.
Proof using .
Admitted.

Theorem Zpower_lt_Zpower :
  forall e1 e2,
  (Zpower r (e1 - 1) < Zpower r e2)%Z ->
  (e1 <= e2)%Z.
Proof using .
Admitted.

Theorem Zpower_gt_id :
  forall n, (n < Zpower r n)%Z.
Proof using .
Admitted.

End Zpower.

Section Div_Mod.

Theorem Zmod_mod_mult :
  forall n a b, (0 < a)%Z -> (0 <= b)%Z ->
  Zmod (Zmod n (a * b)) b = Zmod n b.
Admitted.

Theorem ZOmod_eq :
  forall a b,
  Z.rem a b = (a - Z.quot a b * b)%Z.
Admitted.

Theorem ZOmod_mod_mult :
  forall n a b,
  Z.rem (Z.rem n (a * b)) b = Z.rem n b.
Admitted.

Theorem Zdiv_mod_mult :
  forall n a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Z.div (Zmod n (a * b)) a) = Zmod (Z.div n a) b.
Admitted.

Theorem ZOdiv_mod_mult :
  forall n a b,
  (Z.quot (Z.rem n (a * b)) a) = Z.rem (Z.quot n a) b.
Admitted.

Theorem ZOdiv_small_abs :
  forall a b,
  (Z.abs a < b)%Z -> Z.quot a b = Z0.
Admitted.

Theorem ZOmod_small_abs :
  forall a b,
  (Z.abs a < b)%Z -> Z.rem a b = a.
Admitted.

Theorem ZOdiv_plus :
  forall a b c, (0 <= a * b)%Z ->
  (Z.quot (a + b) c = Z.quot a c + Z.quot b c + Z.quot (Z.rem a c + Z.rem b c) c)%Z.
Admitted.

End Div_Mod.

Section Same_sign.

Theorem Zsame_sign_trans :
  forall v u w, v <> Z0 ->
  (0 <= u * v)%Z -> (0 <= v * w)%Z -> (0 <= u * w)%Z.
Admitted.

Theorem Zsame_sign_trans_weak :
  forall v u w, (v = Z0 -> w = Z0) ->
  (0 <= u * v)%Z -> (0 <= v * w)%Z -> (0 <= u * w)%Z.
Admitted.

Theorem Zsame_sign_imp :
  forall u v,
  (0 < u -> 0 <= v)%Z ->
  (0 < -u -> 0 <= -v)%Z ->
  (0 <= u * v)%Z.
Admitted.

Theorem Zsame_sign_odiv :
  forall u v, (0 <= v)%Z ->
  (0 <= u * Z.quot u v)%Z.
Admitted.

End Same_sign.

Section Zeq_bool.

Inductive Zeq_bool_prop (x y : Z) : bool -> Prop :=
  | Zeq_bool_true_ : x = y -> Zeq_bool_prop x y true
  | Zeq_bool_false_ : x <> y -> Zeq_bool_prop x y false.

Theorem Zeq_bool_spec :
  forall x y, Zeq_bool_prop x y (Zeq_bool x y).
Admitted.

Theorem Zeq_bool_true :
  forall x y, x = y -> Zeq_bool x y = true.
Admitted.

Theorem Zeq_bool_false :
  forall x y, x <> y -> Zeq_bool x y = false.
Admitted.

Theorem Zeq_bool_diag :
  forall x, Zeq_bool x x = true.
Admitted.

Theorem Zeq_bool_opp :
  forall x y,
  Zeq_bool (Z.opp x) y = Zeq_bool x (Z.opp y).
Admitted.

Theorem Zeq_bool_opp' :
  forall x y,
  Zeq_bool (Z.opp x) (Z.opp y) = Zeq_bool x y.
Admitted.

End Zeq_bool.

Section Zle_bool.

Inductive Zle_bool_prop (x y : Z) : bool -> Prop :=
  | Zle_bool_true_ : (x <= y)%Z -> Zle_bool_prop x y true
  | Zle_bool_false_ : (y < x)%Z -> Zle_bool_prop x y false.

Theorem Zle_bool_spec :
  forall x y, Zle_bool_prop x y (Zle_bool x y).
Admitted.

Theorem Zle_bool_true :
  forall x y : Z,
  (x <= y)%Z -> Zle_bool x y = true.
Admitted.

Theorem Zle_bool_false :
  forall x y : Z,
  (y < x)%Z -> Zle_bool x y = false.
Admitted.

Theorem Zle_bool_opp_l :
  forall x y,
  Zle_bool (Z.opp x) y = Zle_bool (Z.opp y) x.
Admitted.

Theorem Zle_bool_opp :
  forall x y,
  Zle_bool (Z.opp x) (Z.opp y) = Zle_bool y x.
Admitted.

Theorem Zle_bool_opp_r :
  forall x y,
  Zle_bool x (Z.opp y) = Zle_bool y (Z.opp x).
Admitted.

End Zle_bool.

Section Zlt_bool.

Inductive Zlt_bool_prop (x y : Z) : bool -> Prop :=
  | Zlt_bool_true_ : (x < y)%Z -> Zlt_bool_prop x y true
  | Zlt_bool_false_ : (y <= x)%Z -> Zlt_bool_prop x y false.

Theorem Zlt_bool_spec :
  forall x y, Zlt_bool_prop x y (Zlt_bool x y).
Admitted.

Theorem Zlt_bool_true :
  forall x y : Z,
  (x < y)%Z -> Zlt_bool x y = true.
Admitted.

Theorem Zlt_bool_false :
  forall x y : Z,
  (y <= x)%Z -> Zlt_bool x y = false.
Admitted.

Theorem negb_Zle_bool :
  forall x y : Z,
  negb (Zle_bool x y) = Zlt_bool y x.
Admitted.

Theorem negb_Zlt_bool :
  forall x y : Z,
  negb (Zlt_bool x y) = Zle_bool y x.
Admitted.

Theorem Zlt_bool_opp_l :
  forall x y,
  Zlt_bool (Z.opp x) y = Zlt_bool (Z.opp y) x.
Admitted.

Theorem Zlt_bool_opp_r :
  forall x y,
  Zlt_bool x (Z.opp y) = Zlt_bool y (Z.opp x).
Admitted.

Theorem Zlt_bool_opp :
  forall x y,
  Zlt_bool (Z.opp x) (Z.opp y) = Zlt_bool y x.
Admitted.

End Zlt_bool.

Section Zcompare.

Inductive Zcompare_prop (x y : Z) : comparison -> Prop :=
  | Zcompare_Lt_ : (x < y)%Z -> Zcompare_prop x y Lt
  | Zcompare_Eq_ : x = y -> Zcompare_prop x y Eq
  | Zcompare_Gt_ : (y < x)%Z -> Zcompare_prop x y Gt.

Theorem Zcompare_spec :
  forall x y, Zcompare_prop x y (Z.compare x y).
Admitted.

Theorem Zcompare_Lt :
  forall x y,
  (x < y)%Z -> Z.compare x y = Lt.
Admitted.

Theorem Zcompare_Eq :
  forall x y,
  (x = y)%Z -> Z.compare x y = Eq.
Admitted.

Theorem Zcompare_Gt :
  forall x y,
  (y < x)%Z -> Z.compare x y = Gt.
Admitted.

End Zcompare.

Section cond_Zopp.

Theorem cond_Zopp_0 :
  forall sx, cond_Zopp sx 0 = 0%Z.
Admitted.

Theorem cond_Zopp_negb :
  forall x y, cond_Zopp (negb x) y = Z.opp (cond_Zopp x y).
Admitted.

Theorem abs_cond_Zopp :
  forall b m,
  Z.abs (cond_Zopp b m) = Z.abs m.
Admitted.

Theorem cond_Zopp_Zlt_bool :
  forall m,
  cond_Zopp (Zlt_bool m 0) m = Z.abs m.
Admitted.

Theorem Zeq_bool_cond_Zopp :
  forall s m n,
  Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n).
Admitted.

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
Admitted.

End fast_pow_pos.

Section faster_div.

Lemma Zdiv_eucl_unique :
  forall a b,
  Z.div_eucl a b = (Z.div a b, Zmod a b).
Admitted.

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
Admitted.

Definition Zpos_div_eucl_aux (a b : positive) :=
  match Pos.compare a b with
  | Lt => (Z0, Zpos a)
  | Eq => (1%Z, Z0)
  | Gt => Zpos_div_eucl_aux1 a b
  end.

Lemma Zpos_div_eucl_aux_correct :
  forall a b,
  Zpos_div_eucl_aux a b = Z.pos_div_eucl a (Zpos b).
Admitted.

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
Admitted.

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
Admitted.

Lemma iter_nat_S :
  forall (p : nat) (x : A),
  iter_nat (S p) x = f (iter_nat p x).
Proof using .
Admitted.

Lemma iter_pos_nat :
  forall (p : positive) (x : A),
  iter_pos f p x = iter_nat (Pos.to_nat p) x.
Proof using .
Admitted.

End Iter.

End Zaux.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Zaux.

Module Export Flocq_DOT_Core_DOT_Raux.
Module Export Flocq.
Module Export Core.
Module Export Raux.

Import Stdlib.micromega.Psatz Stdlib.Reals.Reals Stdlib.ZArith.ZArith.
Import Flocq.Core.Zaux.

Section Rmissing.

Theorem Rle_0_minus :
  forall x y, (x <= y)%R -> (0 <= y - x)%R.
Admitted.

Theorem Rabs_eq_Rabs :
  forall x y : R,
  Rabs x = Rabs y -> x = y \/ x = Ropp y.
Admitted.

Theorem Rabs_minus_le:
  forall x y : R,
  (0 <= y)%R -> (y <= 2*x)%R ->
  (Rabs (x-y) <= x)%R.
Admitted.

Theorem Rabs_eq_R0 x : (Rabs x = 0 -> x = 0)%R.
Admitted.

Theorem Rmult_lt_compat :
  forall r1 r2 r3 r4,
  (0 <= r1)%R -> (0 <= r3)%R -> (r1 < r2)%R -> (r3 < r4)%R ->
  (r1 * r3 < r2 * r4)%R.
Admitted.

Lemma Rmult_neq_reg_r :
  forall r1 r2 r3 : R, (r2 * r1 <> r3 * r1)%R -> r2 <> r3.
Admitted.

Lemma Rmult_neq_compat_r :
  forall r1 r2 r3 : R,
  (r1 <> 0)%R -> (r2 <> r3)%R ->
  (r2 * r1 <> r3 * r1)%R.
Admitted.

Theorem Rmult_min_distr_r :
  forall r r1 r2 : R,
  (0 <= r)%R ->
  (Rmin r1 r2 * r)%R = Rmin (r1 * r) (r2 * r).
Admitted.

Theorem Rmult_min_distr_l :
  forall r r1 r2 : R,
  (0 <= r)%R ->
  (r * Rmin r1 r2)%R = Rmin (r * r1) (r * r2).
Admitted.

Lemma Rmin_opp: forall x y, (Rmin (-x) (-y) = - Rmax x y)%R.
Admitted.

Lemma Rmax_opp: forall x y, (Rmax (-x) (-y) = - Rmin x y)%R.
Admitted.

Theorem exp_le :
  forall x y : R,
  (x <= y)%R -> (exp x <= exp y)%R.
Admitted.

Theorem Rinv_lt :
  forall x y,
  (0 < x)%R -> (x < y)%R -> (/y < /x)%R.
Admitted.

Theorem Rinv_le :
  forall x y,
  (0 < x)%R -> (x <= y)%R -> (/y <= /x)%R.
Admitted.

Theorem sqrt_ge_0 :
  forall x : R,
  (0 <= sqrt x)%R.
Admitted.

Lemma sqrt_neg : forall x, (x <= 0)%R -> (sqrt x = 0)%R.
Admitted.

Lemma Rsqr_le_abs_0_alt :
  forall x y,
  (x² <= y² -> x <= Rabs y)%R.
Admitted.

Theorem Rabs_le_inv :
  forall x y,
  (Rabs x <= y)%R -> (-y <= x <= y)%R.
Admitted.

Theorem Rabs_ge :
  forall x y,
  (y <= -x \/ x <= y)%R -> (x <= Rabs y)%R.
Admitted.

Theorem Rabs_ge_inv :
  forall x y,
  (x <= Rabs y)%R -> (y <= -x \/ x <= y)%R.
Admitted.

Theorem Rabs_lt :
  forall x y,
  (-y < x < y)%R -> (Rabs x < y)%R.
Admitted.

Theorem Rabs_lt_inv :
  forall x y,
  (Rabs x < y)%R -> (-y < x < y)%R.
Admitted.

Theorem Rabs_gt :
  forall x y,
  (y < -x \/ x < y)%R -> (x < Rabs y)%R.
Admitted.

Theorem Rabs_gt_inv :
  forall x y,
  (x < Rabs y)%R -> (y < -x \/ x < y)%R.
Admitted.

End Rmissing.

Section IZR.

Theorem IZR_le_lt :
  forall m n p, (m <= n < p)%Z -> (IZR m <= IZR n < IZR p)%R.
Admitted.

Theorem le_lt_IZR :
  forall m n p, (IZR m <= IZR n < IZR p)%R -> (m <= n < p)%Z.
Admitted.

Theorem neq_IZR :
  forall m n, (IZR m <> IZR n)%R -> (m <> n)%Z.
Admitted.

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
Admitted.

Global Opaque Rcompare.

Theorem Rcompare_Lt :
  forall x y,
  (x < y)%R -> Rcompare x y = Lt.
Admitted.

Theorem Rcompare_Lt_inv :
  forall x y,
  Rcompare x y = Lt -> (x < y)%R.
Admitted.

Theorem Rcompare_not_Lt :
  forall x y,
  (y <= x)%R -> Rcompare x y <> Lt.
Admitted.

Theorem Rcompare_not_Lt_inv :
  forall x y,
  Rcompare x y <> Lt -> (y <= x)%R.
Admitted.

Theorem Rcompare_Eq :
  forall x y,
  x = y -> Rcompare x y = Eq.
Admitted.

Theorem Rcompare_Eq_inv :
  forall x y,
  Rcompare x y = Eq -> x = y.
Admitted.

Theorem Rcompare_Gt :
  forall x y,
  (y < x)%R -> Rcompare x y = Gt.
Admitted.

Theorem Rcompare_Gt_inv :
  forall x y,
  Rcompare x y = Gt -> (y < x)%R.
Admitted.

Theorem Rcompare_not_Gt :
  forall x y,
  (x <= y)%R -> Rcompare x y <> Gt.
Admitted.

Theorem Rcompare_not_Gt_inv :
  forall x y,
  Rcompare x y <> Gt -> (x <= y)%R.
Admitted.

Theorem Rcompare_IZR :
  forall x y, Rcompare (IZR x) (IZR y) = Z.compare x y.
Admitted.

Theorem Rcompare_sym :
  forall x y,
  Rcompare x y = CompOpp (Rcompare y x).
Admitted.

Lemma Rcompare_opp :
  forall x y,
  Rcompare (- x) (- y) = Rcompare y x.
Admitted.

Theorem Rcompare_plus_r :
  forall z x y,
  Rcompare (x + z) (y + z) = Rcompare x y.
Admitted.

Theorem Rcompare_plus_l :
  forall z x y,
  Rcompare (z + x) (z + y) = Rcompare x y.
Admitted.

Theorem Rcompare_mult_r :
  forall z x y,
  (0 < z)%R ->
  Rcompare (x * z) (y * z) = Rcompare x y.
Admitted.

Theorem Rcompare_mult_l :
  forall z x y,
  (0 < z)%R ->
  Rcompare (z * x) (z * y) = Rcompare x y.
Admitted.

Theorem Rcompare_middle :
  forall x d u,
  Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2).
Admitted.

Theorem Rcompare_half_l :
  forall x y, Rcompare (x / 2) y = Rcompare x (2 * y).
Admitted.

Theorem Rcompare_half_r :
  forall x y, Rcompare x (y / 2) = Rcompare (2 * x) y.
Admitted.

Theorem Rcompare_sqr :
  forall x y,
  Rcompare (x * x) (y * y) = Rcompare (Rabs x) (Rabs y).
Admitted.

Theorem Rmin_compare :
  forall x y,
  Rmin x y = match Rcompare x y with Lt => x | Eq => x | Gt => y end.
Admitted.

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
Admitted.

Theorem Rle_bool_true :
  forall x y,
  (x <= y)%R -> Rle_bool x y = true.
Admitted.

Theorem Rle_bool_false :
  forall x y,
  (y < x)%R -> Rle_bool x y = false.
Admitted.

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
Admitted.

Theorem negb_Rlt_bool :
  forall x y,
  negb (Rle_bool x y) = Rlt_bool y x.
Admitted.

Theorem negb_Rle_bool :
  forall x y,
  negb (Rlt_bool x y) = Rle_bool y x.
Admitted.

Theorem Rlt_bool_true :
  forall x y,
  (x < y)%R -> Rlt_bool x y = true.
Admitted.

Theorem Rlt_bool_false :
  forall x y,
  (y <= x)%R -> Rlt_bool x y = false.
Admitted.

Lemma Rlt_bool_opp :
  forall x y,
  Rlt_bool (- x) (- y) = Rlt_bool y x.
Admitted.

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
Admitted.

Theorem Req_bool_true :
  forall x y,
  (x = y)%R -> Req_bool x y = true.
Admitted.

Theorem Req_bool_false :
  forall x y,
  (x <> y)%R -> Req_bool x y = false.
Admitted.

End Req_bool.

Section Floor_Ceil.

Definition Zfloor (x : R) := (up x - 1)%Z.

Theorem Zfloor_lb :
  forall x : R,
  (IZR (Zfloor x) <= x)%R.
Admitted.

Theorem Zfloor_ub :
  forall x : R,
  (x < IZR (Zfloor x) + 1)%R.
Admitted.

Theorem Zfloor_lub :
  forall n x,
  (IZR n <= x)%R ->
  (n <= Zfloor x)%Z.
Admitted.

Theorem Zfloor_imp :
  forall n x,
  (IZR n <= x < IZR (n + 1))%R ->
  Zfloor x = n.
Admitted.

Theorem Zfloor_IZR :
  forall n,
  Zfloor (IZR n) = n.
Admitted.

Theorem Zfloor_le :
  forall x y, (x <= y)%R ->
  (Zfloor x <= Zfloor y)%Z.
Admitted.

Definition Zceil (x : R) := (- Zfloor (- x))%Z.

Theorem Zceil_ub :
  forall x : R,
  (x <= IZR (Zceil x))%R.
Admitted.

Theorem Zceil_lb :
  forall x : R,
  (IZR (Zceil x) < x + 1)%R.
Admitted.

Theorem Zceil_glb :
  forall n x,
  (x <= IZR n)%R ->
  (Zceil x <= n)%Z.
Admitted.

Theorem Zceil_imp :
  forall n x,
  (IZR (n - 1) < x <= IZR n)%R ->
  Zceil x = n.
Admitted.

Theorem Zceil_IZR :
  forall n,
  Zceil (IZR n) = n.
Admitted.

Theorem Zceil_le :
  forall x y, (x <= y)%R ->
  (Zceil x <= Zceil y)%Z.
Admitted.

Theorem Zceil_floor_neq :
  forall x : R,
  (IZR (Zfloor x) <> x)%R ->
  (Zceil x = Zfloor x + 1)%Z.
Admitted.

Definition Ztrunc x := if Rlt_bool x 0 then Zceil x else Zfloor x.

Theorem Ztrunc_IZR :
  forall n,
  Ztrunc (IZR n) = n.
Admitted.

Theorem Ztrunc_floor :
  forall x,
  (0 <= x)%R ->
  Ztrunc x = Zfloor x.
Admitted.

Theorem Ztrunc_ceil :
  forall x,
  (x <= 0)%R ->
  Ztrunc x = Zceil x.
Admitted.

Theorem Ztrunc_le :
  forall x y, (x <= y)%R ->
  (Ztrunc x <= Ztrunc y)%Z.
Admitted.

Theorem Ztrunc_opp :
  forall x,
  Ztrunc (- x) = Z.opp (Ztrunc x).
Admitted.

Theorem Ztrunc_abs :
  forall x,
  Ztrunc (Rabs x) = Z.abs (Ztrunc x).
Admitted.

Theorem Ztrunc_lub :
  forall n x,
  (IZR n <= Rabs x)%R ->
  (n <= Z.abs (Ztrunc x))%Z.
Admitted.

Definition Zaway x := if Rlt_bool x 0 then Zfloor x else Zceil x.

Theorem Zaway_IZR :
  forall n,
  Zaway (IZR n) = n.
Admitted.

Theorem Zaway_ceil :
  forall x,
  (0 <= x)%R ->
  Zaway x = Zceil x.
Admitted.

Theorem Zaway_floor :
  forall x,
  (x <= 0)%R ->
  Zaway x = Zfloor x.
Admitted.

Theorem Zaway_le :
  forall x y, (x <= y)%R ->
  (Zaway x <= Zaway y)%Z.
Admitted.

Theorem Zaway_opp :
  forall x,
  Zaway (- x) = Z.opp (Zaway x).
Admitted.

Theorem Zaway_abs :
  forall x,
  Zaway (Rabs x) = Z.abs (Zaway x).
Admitted.

End Floor_Ceil.

Theorem Rcompare_floor_ceil_middle :
  forall x,
  IZR (Zfloor x) <> x ->
  Rcompare (x - IZR (Zfloor x)) (/ 2) = Rcompare (x - IZR (Zfloor x)) (IZR (Zceil x) - x).
Admitted.

Theorem Rcompare_ceil_floor_middle :
  forall x,
  IZR (Zfloor x) <> x ->
  Rcompare (IZR (Zceil x) - x) (/ 2) = Rcompare (IZR (Zceil x) - x) (x - IZR (Zfloor x)).
Admitted.

Theorem Zfloor_div :
  forall x y,
  y <> Z0 ->
  Zfloor (IZR x / IZR y) = (x / y)%Z.
Admitted.

Theorem Ztrunc_div :
  forall x y, y <> 0%Z ->
  Ztrunc (IZR x / IZR y) = Z.quot x y.
Admitted.

Section pow.

Variable r : radix.

Theorem radix_pos : (0 < IZR r)%R.
Proof using .
Admitted.

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
Admitted.

Theorem bpow_powerRZ :
  forall e,
  bpow e = powerRZ (IZR r) e.
Proof using .
Admitted.

Theorem  bpow_ge_0 :
  forall e : Z, (0 <= bpow e)%R.
Proof using .
Admitted.

Theorem bpow_gt_0 :
  forall e : Z, (0 < bpow e)%R.
Proof using .
Admitted.

Theorem bpow_plus :
  forall e1 e2 : Z, (bpow (e1 + e2) = bpow e1 * bpow e2)%R.
Proof using .
Admitted.

Theorem bpow_1 :
  bpow 1 = IZR r.
Proof using .
Admitted.

Theorem bpow_plus_1 :
  forall e : Z, (bpow (e + 1) = IZR r * bpow e)%R.
Proof using .
Admitted.

Theorem bpow_opp :
  forall e : Z, (bpow (-e) = /bpow e)%R.
Proof using .
Admitted.

Theorem IZR_Zpower_nat :
  forall e : nat,
  IZR (Zpower_nat r e) = bpow (Z_of_nat e).
Proof using .
Admitted.

Theorem IZR_Zpower :
  forall e : Z,
  (0 <= e)%Z ->
  IZR (Zpower r e) = bpow e.
Proof using .
Admitted.

Theorem bpow_lt :
  forall e1 e2 : Z,
  (e1 < e2)%Z -> (bpow e1 < bpow e2)%R.
Proof using .
Admitted.

Theorem lt_bpow :
  forall e1 e2 : Z,
  (bpow e1 < bpow e2)%R -> (e1 < e2)%Z.
Proof using .
Admitted.

Theorem bpow_le :
  forall e1 e2 : Z,
  (e1 <= e2)%Z -> (bpow e1 <= bpow e2)%R.
Proof using .
Admitted.

Theorem le_bpow :
  forall e1 e2 : Z,
  (bpow e1 <= bpow e2)%R -> (e1 <= e2)%Z.
Proof using .
Admitted.

Theorem bpow_inj :
  forall e1 e2 : Z,
  bpow e1 = bpow e2 -> e1 = e2.
Proof using .
Admitted.

Theorem bpow_exp :
  forall e : Z,
  bpow e = exp (IZR e * ln (IZR r)).
Proof using .
Admitted.

Lemma sqrt_bpow :
  forall e,
  sqrt (bpow (2 * e)) = bpow e.
Proof using .
Admitted.

Lemma sqrt_bpow_ge :
  forall e,
  (bpow (e / 2) <= sqrt (bpow e))%R.
Proof using .
Admitted.

Record mag_prop x := {
  mag_val :> Z ;
  _ : (x <> 0)%R -> (bpow (mag_val - 1)%Z <= Rabs x < bpow mag_val)%R
}.

Definition mag :
  forall x : R, mag_prop x.
Proof using .
Admitted.

Theorem bpow_lt_bpow :
  forall e1 e2,
  (bpow (e1 - 1) < bpow e2)%R ->
  (e1 <= e2)%Z.
Proof using .
Admitted.

Theorem bpow_unique :
  forall x e1 e2,
  (bpow (e1 - 1) <= x < bpow e1)%R ->
  (bpow (e2 - 1) <= x < bpow e2)%R ->
  e1 = e2.
Proof using .
Admitted.

Theorem mag_unique :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= Rabs x < bpow e)%R ->
  mag x = e :> Z.
Proof using .
Admitted.

Theorem mag_opp :
  forall x,
  mag (-x) = mag x :> Z.
Proof using .
Admitted.

Theorem mag_abs :
  forall x,
  mag (Rabs x) = mag x :> Z.
Proof using .
Admitted.

Theorem mag_unique_pos :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= x < bpow e)%R ->
  mag x = e :> Z.
Proof using .
Admitted.

Theorem mag_le_abs :
  forall x y,
  (x <> 0)%R -> (Rabs x <= Rabs y)%R ->
  (mag x <= mag y)%Z.
Proof using .
Admitted.

Theorem mag_le :
  forall x y,
  (0 < x)%R -> (x <= y)%R ->
  (mag x <= mag y)%Z.
Proof using .
Admitted.

Lemma lt_mag :
  forall x y,
  (0 < y)%R ->
  (mag x < mag y)%Z -> (x < y)%R.
Proof using .
Admitted.

Theorem mag_bpow :
  forall e, (mag (bpow e) = e + 1 :> Z)%Z.
Proof using .
Admitted.

Theorem mag_mult_bpow :
  forall x e, x <> 0%R ->
  (mag (x * bpow e) = mag x + e :>Z)%Z.
Proof using .
Admitted.

Theorem mag_le_bpow :
  forall x e,
  x <> 0%R ->
  (Rabs x < bpow e)%R ->
  (mag x <= e)%Z.
Proof using .
Admitted.

Theorem mag_gt_bpow :
  forall x e,
  (bpow e <= Rabs x)%R ->
  (e < mag x)%Z.
Proof using .
Admitted.

Theorem mag_ge_bpow :
  forall x e,
  (bpow (e - 1) <= Rabs x)%R ->
  (e <= mag x)%Z.
Proof using .
Admitted.

Theorem bpow_mag_gt :
  forall x,
  (Rabs x < bpow (mag x))%R.
Proof using .
Admitted.

Theorem bpow_mag_le :
  forall x, (x <> 0)%R ->
    (bpow (mag x-1) <= Rabs x)%R.
Proof using .
Admitted.

Theorem mag_le_Zpower :
  forall m e,
  m <> Z0 ->
  (Z.abs m < Zpower r e)%Z->
  (mag (IZR m) <= e)%Z.
Proof using .
Admitted.

Theorem mag_gt_Zpower :
  forall m e,
  m <> Z0 ->
  (Zpower r e <= Z.abs m)%Z ->
  (e < mag (IZR m))%Z.
Proof using .
Admitted.

Lemma mag_mult :
  forall x y,
  (x <> 0)%R -> (y <> 0)%R ->
  (mag x + mag y - 1 <= mag (x * y) <= mag x + mag y)%Z.
Proof using .
Admitted.

Lemma mag_plus :
  forall x y,
  (0 < y)%R -> (y <= x)%R ->
  (mag x <= mag (x + y) <= mag x + 1)%Z.
Proof using .
Admitted.

Lemma mag_minus :
  forall x y,
  (0 < y)%R -> (y < x)%R ->
  (mag (x - y) <= mag x)%Z.
Proof using .
Admitted.

Lemma mag_minus_lb :
  forall x y,
  (0 < x)%R -> (0 < y)%R ->
  (mag y <= mag x - 2)%Z ->
  (mag x - 1 <= mag (x - y))%Z.
Proof using .
Admitted.

Theorem mag_plus_ge :
  forall x y,
  (x <> 0)%R ->
  (mag y <= mag x - 2)%Z ->
  (mag x - 1 <= mag (x + y))%Z.
Proof using .
Admitted.

Lemma mag_div :
  forall x y : R,
  x <> 0%R -> y <> 0%R ->
  (mag x - mag y <= mag (x / y) <= mag x - mag y + 1)%Z.
Proof using .
Admitted.

Lemma mag_sqrt :
  forall x,
  (0 < x)%R ->
  mag (sqrt x) = Z.div2 (mag x + 1) :> Z.
Proof using .
Admitted.

Lemma mag_1 : mag 1 = 1%Z :> Z.
Proof using .
Admitted.

End pow.

Section Bool.

Theorem eqb_sym :
  forall x y, Bool.eqb x y = Bool.eqb y x.
Admitted.

Theorem eqb_false :
  forall x y, x = negb y -> Bool.eqb x y = false.
Admitted.

Theorem eqb_true :
  forall x y, x = y -> Bool.eqb x y = true.
Admitted.

End Bool.

Section cond_Ropp.

Definition cond_Ropp (b : bool) m := if b then Ropp m else m.

Theorem IZR_cond_Zopp :
  forall b m,
  IZR (cond_Zopp b m) = cond_Ropp b (IZR m).
Admitted.

Theorem abs_cond_Ropp :
  forall b m,
  Rabs (cond_Ropp b m) = Rabs m.
Admitted.

Theorem cond_Ropp_Rlt_bool :
  forall m,
  cond_Ropp (Rlt_bool m 0) m = Rabs m.
Admitted.

Theorem Rlt_bool_cond_Ropp :
  forall x sx, (0 < x)%R ->
  Rlt_bool (cond_Ropp sx x) 0 = sx.
Admitted.

Theorem cond_Ropp_involutive :
  forall b x,
  cond_Ropp b (cond_Ropp b x) = x.
Admitted.

Theorem cond_Ropp_inj :
  forall b x y,
  cond_Ropp b x = cond_Ropp b y -> x = y.
Admitted.

Theorem cond_Ropp_mult_l :
  forall b x y,
  cond_Ropp b (x * y) = (cond_Ropp b x * y)%R.
Admitted.

Theorem cond_Ropp_mult_r :
  forall b x y,
  cond_Ropp b (x * y) = (x * cond_Ropp b y)%R.
Admitted.

Theorem cond_Ropp_plus :
  forall b x y,
  cond_Ropp b (x + y) = (cond_Ropp b x + cond_Ropp b y)%R.
Admitted.

End cond_Ropp.

Theorem LPO_min :
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
  {n : nat | P n /\ forall i, (i < n)%nat -> ~ P i} + {forall n, ~ P n}.
Admitted.

Theorem LPO :
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
  {n : nat | P n} + {forall n, ~ P n}.
Admitted.

Lemma LPO_Z : forall P : Z -> Prop, (forall n, P n \/ ~P n) ->
  {n : Z| P n} + {forall n, ~ P n}.
Admitted.

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
Admitted.

Section Fcore_digits.

Variable beta : radix.

Definition Zdigit n k := Z.rem (Z.quot n (Zpower beta k)) beta.

Theorem Zdigit_lt :
  forall n k,
  (k < 0)%Z ->
  Zdigit n k = Z0.
Proof using .
Admitted.

Theorem Zdigit_0 :
  forall k, Zdigit 0 k = Z0.
Proof using .
Admitted.

Theorem Zdigit_opp :
  forall n k,
  Zdigit (-n) k = Z.opp (Zdigit n k).
Proof using .
Admitted.

Theorem Zdigit_ge_Zpower_pos :
  forall e n,
  (0 <= n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof using .
Admitted.

Theorem Zdigit_ge_Zpower :
  forall e n,
  (Z.abs n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof using .
Admitted.

Theorem Zdigit_not_0_pos :
  forall e n, (0 <= e)%Z ->
  (Zpower beta e <= n < Zpower beta (e + 1))%Z ->
  Zdigit n e <> Z0.
Proof using .
Admitted.

Theorem Zdigit_not_0 :
  forall e n, (0 <= e)%Z ->
  (Zpower beta e <= Z.abs n < Zpower beta (e + 1))%Z ->
  Zdigit n e <> Z0.
Proof using .
Admitted.

Theorem Zdigit_mul_pow :
  forall n k k', (0 <= k')%Z ->
  Zdigit (n * Zpower beta k') k = Zdigit n (k - k').
Proof using .
Admitted.

Theorem Zdigit_div_pow :
  forall n k k', (0 <= k)%Z -> (0 <= k')%Z ->
  Zdigit (Z.quot n (Zpower beta k')) k = Zdigit n (k + k').
Proof using .
Admitted.

Theorem Zdigit_mod_pow :
  forall n k k', (k < k')%Z ->
  Zdigit (Z.rem n (Zpower beta k')) k = Zdigit n k.
Proof using .
Admitted.

Theorem Zdigit_mod_pow_out :
  forall n k k', (0 <= k' <= k)%Z ->
  Zdigit (Z.rem n (Zpower beta k')) k = Z0.
Proof using .
Admitted.

Fixpoint Zsum_digit f k :=
  match k with
  | O => Z0
  | S k => (Zsum_digit f k + f (Z_of_nat k) * Zpower beta (Z_of_nat k))%Z
  end.

Theorem Zsum_digit_digit :
  forall n k,
  Zsum_digit (Zdigit n) k = Z.rem n (Zpower beta (Z_of_nat k)).
Proof using .
Admitted.

Theorem Zdigit_ext :
  forall n1 n2,
  (forall k, (0 <= k)%Z -> Zdigit n1 k = Zdigit n2 k) ->
  n1 = n2.
Proof using .
Admitted.

Theorem ZOmod_plus_pow_digit :
  forall u v n, (0 <= u * v)%Z ->
  (forall k, (0 <= k < n)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  Z.rem (u + v) (Zpower beta n) = (Z.rem u (Zpower beta n) + Z.rem v (Zpower beta n))%Z.
Proof using .
Admitted.

Theorem ZOdiv_plus_pow_digit :
  forall u v n, (0 <= u * v)%Z ->
  (forall k, (0 <= k < n)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  Z.quot (u + v) (Zpower beta n) = (Z.quot u (Zpower beta n) + Z.quot v (Zpower beta n))%Z.
Proof using .
Admitted.

Theorem Zdigit_plus :
  forall u v, (0 <= u * v)%Z ->
  (forall k, (0 <= k)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  forall k,
  Zdigit (u + v) k = (Zdigit u k + Zdigit v k)%Z.
Proof using .
Admitted.

Definition Zscale n k :=
  if Zle_bool 0 k then (n * Zpower beta k)%Z else Z.quot n (Zpower beta (-k)).

Theorem Zdigit_scale :
  forall n k k', (0 <= k')%Z ->
  Zdigit (Zscale n k) k' = Zdigit n (k' - k).
Proof using .
Admitted.

Theorem Zscale_0 :
  forall k,
  Zscale 0 k = Z0.
Proof using .
Admitted.

Theorem Zsame_sign_scale :
  forall n k,
  (0 <= n * Zscale n k)%Z.
Proof using .
Admitted.

Theorem Zscale_mul_pow :
  forall n k k', (0 <= k)%Z ->
  Zscale (n * Zpower beta k) k' = Zscale n (k + k').
Proof using .
Admitted.

Theorem Zscale_scale :
  forall n k k', (0 <= k)%Z ->
  Zscale (Zscale n k) k' = Zscale n (k + k').
Proof using .
Admitted.

Definition Zslice n k1 k2 :=
  if Zle_bool 0 k2 then Z.rem (Zscale n (-k1)) (Zpower beta k2) else Z0.

Theorem Zdigit_slice :
  forall n k1 k2 k, (0 <= k < k2)%Z ->
  Zdigit (Zslice n k1 k2) k = Zdigit n (k1 + k).
Proof using .
Admitted.

Theorem Zdigit_slice_out :
  forall n k1 k2 k, (k2 <= k)%Z ->
  Zdigit (Zslice n k1 k2) k = Z0.
Proof using .
Admitted.

Theorem Zslice_0 :
  forall k k',
  Zslice 0 k k' = Z0.
Proof using .
Admitted.

Theorem Zsame_sign_slice :
  forall n k k',
  (0 <= n * Zslice n k k')%Z.
Proof using .
Admitted.

Theorem Zslice_slice :
  forall n k1 k2 k1' k2', (0 <= k1' <= k2)%Z ->
  Zslice (Zslice n k1 k2) k1' k2' = Zslice n (k1 + k1') (Z.min (k2 - k1') k2').
Proof using .
Admitted.

Theorem Zslice_mul_pow :
  forall n k k1 k2, (0 <= k)%Z ->
  Zslice (n * Zpower beta k) k1 k2 = Zslice n (k1 - k) k2.
Proof using .
Admitted.

Theorem Zslice_div_pow :
  forall n k k1 k2, (0 <= k)%Z -> (0 <= k1)%Z ->
  Zslice (Z.quot n (Zpower beta k)) k1 k2 = Zslice n (k1 + k) k2.
Proof using .
Admitted.

Theorem Zslice_scale :
  forall n k k1 k2, (0 <= k1)%Z ->
  Zslice (Zscale n k) k1 k2 = Zslice n (k1 - k) k2.
Proof using .
Admitted.

Theorem Zslice_div_pow_scale :
  forall n k k1 k2, (0 <= k)%Z ->
  Zslice (Z.quot n (Zpower beta k)) k1 k2 = Zscale (Zslice n k (k1 + k2)) (-k1).
Proof using .
Admitted.

Theorem Zplus_slice :
  forall n k l1 l2, (0 <= l1)%Z -> (0 <= l2)%Z ->
  (Zslice n k l1 + Zscale (Zslice n (k + l1) l2) l1)%Z = Zslice n k (l1 + l2).
Proof using .
Admitted.

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
Admitted.

Theorem Zdigits_unique :
  forall n d,
  (Zpower beta (d - 1) <= Z.abs n < Zpower beta d)%Z ->
  Zdigits n = d.
Proof using .
Admitted.

Theorem Zdigits_abs :
  forall n, Zdigits (Z.abs n) = Zdigits n.
Proof using .
Admitted.

Theorem Zdigits_opp :
  forall n, Zdigits (Z.opp n) = Zdigits n.
Proof using .
Admitted.

Theorem Zdigits_cond_Zopp :
  forall s n, Zdigits (cond_Zopp s n) = Zdigits n.
Proof using .
Admitted.

Theorem Zdigits_gt_0 :
  forall n, n <> Z0 -> (0 < Zdigits n)%Z.
Proof using .
Admitted.

Theorem Zdigits_ge_0 :
  forall n, (0 <= Zdigits n)%Z.
Proof using .
Admitted.

Theorem Zdigit_out :
  forall n k, (Zdigits n <= k)%Z ->
  Zdigit n k = Z0.
Proof using .
Admitted.

Theorem Zdigit_digits :
  forall n, n <> Z0 ->
  Zdigit n (Zdigits n - 1) <> Z0.
Proof using .
Admitted.

Theorem Zdigits_slice :
  forall n k l, (0 <= l)%Z ->
  (Zdigits (Zslice n k l) <= l)%Z.
Proof using .
Admitted.

Theorem Zdigits_mult_Zpower :
  forall m e,
  m <> Z0 -> (0 <= e)%Z ->
  Zdigits (m * Zpower beta e) = (Zdigits m + e)%Z.
Proof using .
Admitted.

Theorem Zdigits_Zpower :
  forall e,
  (0 <= e)%Z ->
  Zdigits (Zpower beta e) = (e + 1)%Z.
Proof using .
Admitted.

Theorem Zdigits_le :
  forall x y,
  (0 <= x)%Z -> (x <= y)%Z ->
  (Zdigits x <= Zdigits y)%Z.
Proof using .
Admitted.

Theorem lt_Zdigits :
  forall x y,
  (0 <= y)%Z ->
  (Zdigits x < Zdigits y)%Z ->
  (x < y)%Z.
Proof using .
Admitted.

Theorem Zpower_le_Zdigits :
  forall e x,
  (e < Zdigits x)%Z ->
  (Zpower beta e <= Z.abs x)%Z.
Proof using .
Admitted.

Theorem Zdigits_le_Zpower :
  forall e x,
  (Z.abs x < Zpower beta e)%Z ->
  (Zdigits x <= e)%Z.
Proof using .
Admitted.

Theorem Zpower_gt_Zdigits :
  forall e x,
  (Zdigits x <= e)%Z ->
  (Z.abs x < Zpower beta e)%Z.
Proof using .
Admitted.

Theorem Zdigits_gt_Zpower :
  forall e x,
  (Zpower beta e <= Z.abs x)%Z ->
  (e < Zdigits x)%Z.
Proof using .
Admitted.

Theorem Zdigits_mult_strong :
  forall x y,
  (0 <= x)%Z -> (0 <= y)%Z ->
  (Zdigits (x + y + x * y) <= Zdigits x + Zdigits y)%Z.
Proof using .
Admitted.

Theorem Zdigits_mult :
  forall x y,
  (Zdigits (x * y) <= Zdigits x + Zdigits y)%Z.
Proof using .
Admitted.

Theorem Zdigits_mult_ge :
  forall x y,
  (x <> 0)%Z -> (y <> 0)%Z ->
  (Zdigits x + Zdigits y - 1 <= Zdigits (x * y))%Z.
Proof using .
Admitted.

Theorem Zdigits_div_Zpower :
  forall m e,
  (0 <= m)%Z ->
  (0 <= e <= Zdigits m)%Z ->
  Zdigits (m / Zpower beta e) = (Zdigits m - e)%Z.
Proof using .
Admitted.

Theorem Zdigits_succ_le :
  forall x, (0 <= x)%Z ->
  (Zdigits (x + 1) <= Zdigits x + 1)%Z.
Proof using .
Admitted.

End Fcore_digits.

Section Zdigits2.

Theorem Z_of_nat_S_digits2_Pnat :
  forall m : positive,
  Z_of_nat (S (digits2_Pnat m)) = Zdigits radix2 (Zpos m).
Admitted.

Theorem Zpos_digits2_pos :
  forall m : positive,
  Zpos (digits2_pos m) = Zdigits radix2 (Zpos m).
Admitted.

Lemma Zdigits2_Zdigits :
  forall n, Zdigits2 n = Zdigits radix2 n.
Admitted.

End Zdigits2.

End Digits.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Digits.

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
Admitted.

Theorem le_F2R :
  forall e m1 m2 : Z,
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R ->
  (m1 <= m2)%Z.
Proof using .
Admitted.

Theorem F2R_le :
  forall m1 m2 e : Z,
  (m1 <= m2)%Z ->
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R.
Proof using .
Admitted.

Theorem lt_F2R :
  forall e m1 m2 : Z,
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R ->
  (m1 < m2)%Z.
Proof using .
Admitted.

Theorem F2R_lt :
  forall e m1 m2 : Z,
  (m1 < m2)%Z ->
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R.
Proof using .
Admitted.

Theorem F2R_eq :
  forall e m1 m2 : Z,
  (m1 = m2)%Z ->
  (F2R (Float beta m1 e) = F2R (Float beta m2 e))%R.
Proof using .
Admitted.

Theorem eq_F2R :
  forall e m1 m2 : Z,
  F2R (Float beta m1 e) = F2R (Float beta m2 e) ->
  m1 = m2.
Proof using .
Admitted.

Theorem F2R_Zabs:
  forall m e : Z,
   F2R (Float beta (Z.abs m) e) = Rabs (F2R (Float beta m e)).
Proof using .
Admitted.

Theorem F2R_Zopp :
  forall m e : Z,
  F2R (Float beta (Z.opp m) e) = Ropp (F2R (Float beta m e)).
Proof using .
Admitted.

Theorem F2R_cond_Zopp :
  forall b m e,
  F2R (Float beta (cond_Zopp b m) e) = cond_Ropp b (F2R (Float beta m e)).
Proof using .
Admitted.

Theorem F2R_0 :
  forall e : Z,
  F2R (Float beta 0 e) = 0%R.
Proof using .
Admitted.

Theorem eq_0_F2R :
  forall m e : Z,
  F2R (Float beta m e) = 0%R ->
  m = Z0.
Proof using .
Admitted.

Theorem ge_0_F2R :
  forall m e : Z,
  (0 <= F2R (Float beta m e))%R ->
  (0 <= m)%Z.
Proof using .
Admitted.

Theorem le_0_F2R :
  forall m e : Z,
  (F2R (Float beta m e) <= 0)%R ->
  (m <= 0)%Z.
Proof using .
Admitted.

Theorem gt_0_F2R :
  forall m e : Z,
  (0 < F2R (Float beta m e))%R ->
  (0 < m)%Z.
Proof using .
Admitted.

Theorem lt_0_F2R :
  forall m e : Z,
  (F2R (Float beta m e) < 0)%R ->
  (m < 0)%Z.
Proof using .
Admitted.

Theorem F2R_ge_0 :
  forall f : float beta,
  (0 <= Fnum f)%Z ->
  (0 <= F2R f)%R.
Proof using .
Admitted.

Theorem F2R_le_0 :
  forall f : float beta,
  (Fnum f <= 0)%Z ->
  (F2R f <= 0)%R.
Proof using .
Admitted.

Theorem F2R_gt_0 :
  forall f : float beta,
  (0 < Fnum f)%Z ->
  (0 < F2R f)%R.
Proof using .
Admitted.

Theorem F2R_lt_0 :
  forall f : float beta,
  (Fnum f < 0)%Z ->
  (F2R f < 0)%R.
Proof using .
Admitted.

Theorem F2R_neq_0 :
 forall f : float beta,
  (Fnum f <> 0)%Z ->
  (F2R f <> 0)%R.
Proof using .
Admitted.

Lemma Fnum_ge_0: forall (f : float beta),
  (0 <= F2R f)%R -> (0 <= Fnum f)%Z.
Proof using .
Admitted.

Lemma Fnum_le_0: forall (f : float beta),
  (F2R f <= 0)%R -> (Fnum f <= 0)%Z.
Proof using .
Admitted.

Theorem F2R_bpow :
  forall e : Z,
  F2R (Float beta 1 e) = bpow e.
Proof using .
Admitted.

Theorem bpow_le_F2R :
  forall m e : Z,
  (0 < m)%Z ->
  (bpow e <= F2R (Float beta m e))%R.
Proof using .
Admitted.

Theorem F2R_p1_le_bpow :
  forall m e1 e2 : Z,
  (0 < m)%Z ->
  (F2R (Float beta m e1) < bpow e2)%R ->
  (F2R (Float beta (m + 1) e1) <= bpow e2)%R.
Proof using .
Admitted.

Theorem bpow_le_F2R_m1 :
  forall m e1 e2 : Z,
  (1 < m)%Z ->
  (bpow e2 < F2R (Float beta m e1))%R ->
  (bpow e2 <= F2R (Float beta (m - 1) e1))%R.
Proof using .
Admitted.

Theorem F2R_lt_bpow :
  forall f : float beta, forall e',
  (Z.abs (Fnum f) < Zpower beta (e' - Fexp f))%Z ->
  (Rabs (F2R f) < bpow e')%R.
Proof using .
Admitted.

Theorem F2R_change_exp :
  forall e' m e : Z,
  (e' <= e)%Z ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e')) e').
Proof using .
Admitted.

Theorem F2R_prec_normalize :
  forall m e e' p : Z,
  (Z.abs m < Zpower beta p)%Z ->
  (bpow (e' - 1)%Z <= Rabs (F2R (Float beta m e)))%R ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e' + p)) (e' - p)).
Proof using .
Admitted.

Theorem mag_F2R_bounds :
  forall x m e, (0 < m)%Z ->
  (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R ->
  mag beta x = mag beta (F2R (Float beta m e)) :> Z.
Proof using .
Admitted.

Theorem mag_F2R :
  forall m e : Z,
  m <> Z0 ->
  (mag beta (F2R (Float beta m e)) = mag beta (IZR m) + e :> Z)%Z.
Proof using .
Admitted.

Theorem Zdigits_mag :
  forall n,
  n <> Z0 ->
  Zdigits beta n = mag beta (IZR n).
Proof using .
Admitted.

Theorem mag_F2R_Zdigits :
  forall m e, m <> Z0 ->
  (mag beta (F2R (Float beta m e)) = Zdigits beta m + e :> Z)%Z.
Proof using .
Admitted.

Theorem mag_F2R_bounds_Zdigits :
  forall x m e, (0 < m)%Z ->
  (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R ->
  mag beta x = (Zdigits beta m + e)%Z :> Z.
Proof using .
Admitted.

Theorem float_distribution_pos :
  forall m1 e1 m2 e2 : Z,
  (0 < m1)%Z ->
  (F2R (Float beta m1 e1) < F2R (Float beta m2 e2) < F2R (Float beta (m1 + 1) e1))%R ->
  (e2 < e1)%Z /\ (e1 + mag beta (IZR m1) = e2 + mag beta (IZR m2))%Z.
Proof using .
Admitted.

End Float_prop.

End Float_prop.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Float_prop.

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
Admitted.

Theorem inbetween_unique :
  forall l l',
  inbetween l -> inbetween l' -> l = l'.
Proof using .
Admitted.

Section Fcalc_bracket_any.

Variable l : location.

Theorem inbetween_bounds :
  inbetween l ->
  (d <= x < u)%R.
Proof using Hdu.
Admitted.

Theorem inbetween_bounds_not_Eq :
  inbetween l ->
  l <> loc_Exact ->
  (d < x < u)%R.
Proof using .
Admitted.

End Fcalc_bracket_any.

Theorem inbetween_distance_inexact :
  forall l,
  inbetween (loc_Inexact l) ->
  Rcompare (x - d) (u - x) = l.
Proof using .
Admitted.

Theorem inbetween_distance_inexact_abs :
  forall l,
  inbetween (loc_Inexact l) ->
  Rcompare (Rabs (d - x)) (Rabs (u - x)) = l.
Proof using Hdu.
Admitted.

End Fcalc_bracket.

Theorem inbetween_ex :
  forall d u l,
  (d < u)%R ->
  exists x,
  inbetween d u x l.
Admitted.

Section Fcalc_bracket_step.

Variable start step : R.
Variable nb_steps : Z.
Variable Hstep : (0 < step)%R.

Lemma ordered_steps :
  forall k,
  (start + IZR k * step < start + IZR (k + 1) * step)%R.
Proof using Hstep.
Admitted.

Lemma middle_range :
  forall k,
  ((start + (start + IZR k * step)) / 2 = start + (IZR k / 2 * step))%R.
Proof using .
Admitted.

Hypothesis (Hnb_steps : (1 < nb_steps)%Z).

Lemma inbetween_step_not_Eq :
  forall x k l l',
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  (0 < k < nb_steps)%Z ->
  Rcompare x (start + (IZR nb_steps / 2 * step))%R = l' ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact l').
Proof using Hstep.
Admitted.

Theorem inbetween_step_Lo :
  forall x k l,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  (0 < k)%Z -> (2 * k + 1 < nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Lt).
Proof using Hnb_steps Hstep.
Admitted.

Theorem inbetween_step_Hi :
  forall x k l,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  (nb_steps < 2 * k)%Z -> (k < nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Gt).
Proof using Hnb_steps Hstep.
Admitted.

Theorem inbetween_step_Lo_not_Eq :
  forall x l,
  inbetween start (start + step) x l ->
  l <> loc_Exact ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Lt).
Proof using Hnb_steps Hstep.
Admitted.

Lemma middle_odd :
  forall k,
  (2 * k + 1 = nb_steps)%Z ->
  (((start + IZR k * step) + (start + IZR (k + 1) * step))/2 = start + IZR nb_steps /2 * step)%R.
Proof using .
Admitted.

Theorem inbetween_step_any_Mi_odd :
  forall x k l,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x (loc_Inexact l) ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact l).
Proof using Hnb_steps Hstep.
Admitted.

Theorem inbetween_step_Lo_Mi_Eq_odd :
  forall x k,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x loc_Exact ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Lt).
Proof using Hnb_steps Hstep.
Admitted.

Theorem inbetween_step_Hi_Mi_even :
  forall x k l,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  l <> loc_Exact ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Gt).
Proof using Hnb_steps Hstep.
Admitted.

Theorem inbetween_step_Mi_Mi_even :
  forall x k,
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x loc_Exact ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + IZR nb_steps * step) x (loc_Inexact Eq).
Proof using Hnb_steps Hstep.
Admitted.

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
Admitted.

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
Admitted.

Definition new_location :=
  if Z.even nb_steps then new_location_even else new_location_odd.

Theorem new_location_correct :
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + IZR k * step) (start + IZR (k + 1) * step) x l ->
  inbetween start (start + IZR nb_steps * step) x (new_location k l).
Proof using Hnb_steps Hstep.
Admitted.

End Fcalc_bracket_step.

Section Bracket_plus.

Theorem inbetween_plus_compat :
  forall x d u l t,
  inbetween x d u l ->
  inbetween (x + t) (d + t) (u + t) l.
Admitted.

Theorem inbetween_plus_reg :
  forall x d u l t,
  inbetween (x + t) (d + t) (u + t) l ->
  inbetween x d u l.
Admitted.

End Bracket_plus.

Section Fcalc_bracket_scale.

Theorem inbetween_mult_compat :
  forall x d u l s,
  (0 < s)%R ->
  inbetween x d u l ->
  inbetween (x * s) (d * s) (u * s) l.
Admitted.

Theorem inbetween_mult_reg :
  forall x d u l s,
  (0 < s)%R ->
  inbetween (x * s) (d * s) (u * s) l ->
  inbetween x d u l.
Admitted.

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
Admitted.

Definition inbetween_int m x l :=
  inbetween (IZR m) (IZR (m + 1)) x l.

Theorem inbetween_float_new_location :
  forall x m e l k,
  (0 < k)%Z ->
  inbetween_float m e x l ->
  inbetween_float (Z.div m (Zpower beta k)) (e + k) x (new_location (Zpower beta k) (Zmod m (Zpower beta k)) l).
Proof using .
Admitted.

Theorem inbetween_float_new_location_single :
  forall x m e l,
  inbetween_float m e x l ->
  inbetween_float (Z.div m beta) (e + 1) x (new_location beta (Zmod m beta) l).
Proof using .
Admitted.

Theorem inbetween_float_ex :
  forall m e l,
  exists x,
  inbetween_float m e x l.
Proof using .
Admitted.

Theorem inbetween_float_unique :
  forall x e m l m' l',
  inbetween_float m e x l ->
  inbetween_float m' e x l' ->
  m = m' /\ l = l'.
Proof using .
Admitted.

End Fcalc_bracket_generic.

End Bracket.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Bracket.

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
Admitted.

Theorem round_fun_of_pred :
  forall rnd : R -> R -> Prop,
  round_pred rnd ->
  { f : R -> R | forall x, rnd x (f x) }.
Admitted.

Theorem round_unique :
  forall rnd : R -> R -> Prop,
  round_pred_monotone rnd ->
  forall x f1 f2,
  rnd x f1 ->
  rnd x f2 ->
  f1 = f2.
Admitted.

Theorem Rnd_DN_pt_monotone :
  forall F : R -> Prop,
  round_pred_monotone (Rnd_DN_pt F).
Admitted.

Theorem Rnd_DN_pt_unique :
  forall F : R -> Prop,
  forall x f1 f2 : R,
  Rnd_DN_pt F x f1 -> Rnd_DN_pt F x f2 ->
  f1 = f2.
Admitted.

Theorem Rnd_DN_unique :
  forall F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_DN F rnd1 -> Rnd_DN F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Admitted.

Theorem Rnd_UP_pt_monotone :
  forall F : R -> Prop,
  round_pred_monotone (Rnd_UP_pt F).
Admitted.

Theorem Rnd_UP_pt_unique :
  forall F : R -> Prop,
  forall x f1 f2 : R,
  Rnd_UP_pt F x f1 -> Rnd_UP_pt F x f2 ->
  f1 = f2.
Admitted.

Theorem Rnd_UP_unique :
  forall F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_UP F rnd1 -> Rnd_UP F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Admitted.

Theorem Rnd_UP_pt_opp :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_DN_pt F x f -> Rnd_UP_pt F (-x) (-f).
Admitted.

Theorem Rnd_DN_pt_opp :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_UP_pt F x f -> Rnd_DN_pt F (-x) (-f).
Admitted.

Theorem Rnd_DN_opp :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall rnd1 rnd2 : R -> R,
  Rnd_DN F rnd1 -> Rnd_UP F rnd2 ->
  forall x, rnd1 (- x) = - rnd2 x.
Admitted.

Theorem Rnd_DN_UP_pt_split :
  forall F : R -> Prop,
  forall x d u,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  forall f, F f ->
  (f <= d) \/ (u <= f).
Admitted.

Theorem Rnd_DN_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_DN_pt F x x.
Admitted.

Theorem Rnd_DN_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_DN_pt F x f -> F x ->
  f = x.
Admitted.

Theorem Rnd_UP_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_UP_pt F x x.
Admitted.

Theorem Rnd_UP_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_UP_pt F x f -> F x ->
  f = x.
Admitted.

Theorem Only_DN_or_UP :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  F f -> (fd <= f <= fu)%R ->
  f = fd \/ f = fu.
Admitted.

Theorem Rnd_ZR_abs :
  forall (F : R -> Prop) (rnd: R-> R),
  Rnd_ZR F rnd ->
  forall x : R,  (Rabs (rnd x) <= Rabs x)%R.
Admitted.

Theorem Rnd_ZR_pt_monotone :
  forall F : R -> Prop, F 0 ->
  round_pred_monotone (Rnd_ZR_pt F).
Admitted.

Theorem Rnd_N_pt_DN_or_UP :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N_pt F x f ->
  Rnd_DN_pt F x f \/ Rnd_UP_pt F x f.
Admitted.

Theorem Rnd_N_pt_DN_or_UP_eq :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  Rnd_N_pt F x f ->
  f = fd \/ f = fu.
Admitted.

Theorem Rnd_N_pt_opp_inv :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_N_pt F (-x) (-f) -> Rnd_N_pt F x f.
Admitted.

Theorem Rnd_N_pt_monotone :
  forall F : R -> Prop,
  forall x y f g : R,
  Rnd_N_pt F x f -> Rnd_N_pt F y g ->
  x < y -> f <= g.
Admitted.

Theorem Rnd_N_pt_unique :
  forall F : R -> Prop,
  forall x d u f1 f2 : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  x - d <> u - x ->
  Rnd_N_pt F x f1 ->
  Rnd_N_pt F x f2 ->
  f1 = f2.
Admitted.

Theorem Rnd_N_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_N_pt F x x.
Admitted.

Theorem Rnd_N_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N_pt F x f -> F x ->
  f = x.
Admitted.

Theorem Rnd_N_pt_0 :
  forall F : R -> Prop,
  F 0 ->
  Rnd_N_pt F 0 0.
Admitted.

Theorem Rnd_N_pt_ge_0 :
  forall F : R -> Prop, F 0 ->
  forall x f, 0 <= x ->
  Rnd_N_pt F x f ->
  0 <= f.
Admitted.

Theorem Rnd_N_pt_le_0 :
  forall F : R -> Prop, F 0 ->
  forall x f, x <= 0 ->
  Rnd_N_pt F x f ->
  f <= 0.
Admitted.

Theorem Rnd_N_pt_abs :
  forall F : R -> Prop,
  F 0 ->
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_N_pt F x f -> Rnd_N_pt F (Rabs x) (Rabs f).
Admitted.

Theorem Rnd_N_pt_DN_UP :
  forall F : R -> Prop,
  forall x d u f : R,
  F f ->
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (Rabs (f - x) <= x - d)%R ->
  (Rabs (f - x) <= u - x)%R ->
  Rnd_N_pt F x f.
Admitted.

Theorem Rnd_N_pt_DN :
  forall F : R -> Prop,
  forall x d u : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (x - d <= u - x)%R ->
  Rnd_N_pt F x d.
Admitted.

Theorem Rnd_N_pt_UP :
  forall F : R -> Prop,
  forall x d u : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (u - x <= x - d)%R ->
  Rnd_N_pt F x u.
Admitted.

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
Admitted.

Theorem Rnd_NG_pt_monotone :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unique_prop F P ->
  round_pred_monotone (Rnd_NG_pt F P).
Admitted.

Theorem Rnd_NG_pt_refl :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  forall x, F x -> Rnd_NG_pt F P x x.
Admitted.

Theorem Rnd_NG_pt_opp_inv :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  ( forall x, F x -> F (-x) ) ->
  ( forall x f, P x f -> P (-x) (-f) ) ->
  forall x f : R,
  Rnd_NG_pt F P (-x) (-f) -> Rnd_NG_pt F P x f.
Admitted.

Theorem Rnd_NG_unique :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unique_prop F P ->
  forall rnd1 rnd2 : R -> R,
  Rnd_NG F P rnd1 -> Rnd_NG F P rnd2 ->
  forall x, rnd1 x = rnd2 x.
Admitted.

Theorem Rnd_NA_NG_pt :
  forall F : R -> Prop,
  F 0 ->
  forall x f,
  Rnd_NA_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs x <= Rabs f) x f.
Admitted.

Lemma Rnd_NA_pt_unique_prop :
  forall F : R -> Prop,
  F 0 ->
  Rnd_NG_pt_unique_prop F (fun a b => (Rabs a <= Rabs b)%R).
Admitted.

Theorem Rnd_NA_pt_unique :
  forall F : R -> Prop,
  F 0 ->
  forall x f1 f2 : R,
  Rnd_NA_pt F x f1 -> Rnd_NA_pt F x f2 ->
  f1 = f2.
Admitted.

Theorem Rnd_NA_pt_N :
  forall F : R -> Prop,
  F 0 ->
  forall x f : R,
  Rnd_N_pt F x f ->
  (Rabs x <= Rabs f)%R ->
  Rnd_NA_pt F x f.
Admitted.

Theorem Rnd_NA_unique :
  forall (F : R -> Prop),
  F 0 ->
  forall rnd1 rnd2 : R -> R,
  Rnd_NA F rnd1 -> Rnd_NA F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Admitted.

Theorem Rnd_NA_pt_monotone :
  forall F : R -> Prop,
  F 0 ->
  round_pred_monotone (Rnd_NA_pt F).
Admitted.

Theorem Rnd_NA_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_NA_pt F x x.
Admitted.

Theorem Rnd_NA_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_NA_pt F x f -> F x ->
  f = x.
Admitted.

Theorem Rnd_N0_NG_pt :
  forall F : R -> Prop,
  F 0 ->
  forall x f,
  Rnd_N0_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs f <= Rabs x) x f.
Admitted.

Lemma Rnd_N0_pt_unique_prop :
  forall F : R -> Prop,
  F 0 ->
  Rnd_NG_pt_unique_prop F (fun x f => Rabs f <= Rabs x).
Admitted.

Theorem Rnd_N0_pt_unique :
  forall F : R -> Prop,
  F 0 ->
  forall x f1 f2 : R,
  Rnd_N0_pt F x f1 -> Rnd_N0_pt F x f2 ->
  f1 = f2.
Admitted.

Theorem Rnd_N0_pt_N :
  forall F : R -> Prop,
  F 0 ->
  forall x f : R,
  Rnd_N_pt F x f ->
  (Rabs f <= Rabs x)%R ->
  Rnd_N0_pt F x f.
Admitted.

Theorem Rnd_N0_unique :
  forall (F : R -> Prop),
  F 0 ->
  forall rnd1 rnd2 : R -> R,
  Rnd_N0 F rnd1 -> Rnd_N0 F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Admitted.

Theorem Rnd_N0_pt_monotone :
  forall F : R -> Prop,
  F 0 ->
  round_pred_monotone (Rnd_N0_pt F).
Admitted.

Theorem Rnd_N0_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_N0_pt F x x.
Admitted.

Theorem Rnd_N0_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N0_pt F x f -> F x ->
  f = x.
Admitted.

Theorem round_pred_ge_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> 0 <= x -> 0 <= f.
Admitted.

Theorem round_pred_gt_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> 0 < f -> 0 < x.
Admitted.

Theorem round_pred_le_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> x <= 0 -> f <= 0.
Admitted.

Theorem round_pred_lt_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> f < 0 -> x < 0.
Admitted.

Theorem Rnd_DN_pt_equiv_format :
  forall F1 F2 : R -> Prop,
  forall a b : R,
  F1 a ->
  ( forall x, a <= x <= b -> (F1 x <-> F2 x) ) ->
  forall x f, a <= x <= b -> Rnd_DN_pt F1 x f -> Rnd_DN_pt F2 x f.
Admitted.

Theorem Rnd_UP_pt_equiv_format :
  forall F1 F2 : R -> Prop,
  forall a b : R,
  F1 b ->
  ( forall x, a <= x <= b -> (F1 x <-> F2 x) ) ->
  forall x f, a <= x <= b -> Rnd_UP_pt F1 x f -> Rnd_UP_pt F2 x f.
Admitted.

Inductive satisfies_any (F : R -> Prop) :=
  Satisfies_any :
    F 0 -> ( forall x : R, F x -> F (-x) ) ->
    round_pred_total (Rnd_DN_pt F) -> satisfies_any F.

Theorem satisfies_any_eq :
  forall F1 F2 : R -> Prop,
  ( forall x, F1 x <-> F2 x ) ->
  satisfies_any F1 ->
  satisfies_any F2.
Admitted.

Theorem satisfies_any_imp_DN :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_DN_pt F).
Admitted.

Theorem satisfies_any_imp_UP :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_UP_pt F).
Admitted.

Theorem satisfies_any_imp_ZR :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_ZR_pt F).
Admitted.

Definition NG_existence_prop (F : R -> Prop) (P : R -> R -> Prop) :=
  forall x d u, ~F x -> Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> P x u \/ P x d.

Theorem satisfies_any_imp_NG :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  satisfies_any F ->
  NG_existence_prop F P ->
  round_pred_total (Rnd_NG_pt F P).
Admitted.

Theorem satisfies_any_imp_NA :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_NA_pt F).
Admitted.

Theorem satisfies_any_imp_N0 :
  forall F : R -> Prop,
  F 0 -> satisfies_any F ->
  round_pred (Rnd_N0_pt F).
Admitted.

End RND_prop.

End Round_pred.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Round_pred.

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
Admitted.

Theorem valid_exp_large' :
  forall k l,
  (fexp k < k)%Z -> (l <= k)%Z ->
  (fexp l < k)%Z.
Proof using valid_exp_.
Admitted.

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
Admitted.

Theorem cexp_opp :
  forall x,
  cexp (-x) = cexp x.
Proof using .
Admitted.

Theorem cexp_abs :
  forall x,
  cexp (Rabs x) = cexp x.
Proof using .
Admitted.

Theorem canonical_generic_format :
  forall x,
  generic_format x ->
  exists f : float beta,
  x = F2R f /\ canonical f.
Proof using .
Admitted.

Theorem generic_format_bpow :
  forall e, (fexp (e + 1) <= e)%Z ->
  generic_format (bpow e).
Proof using .
Admitted.

Theorem generic_format_bpow' :
  forall e, (fexp e <= e)%Z ->
  generic_format (bpow e).
Proof using valid_exp_.
Admitted.

Theorem generic_format_F2R :
  forall m e,
  ( m <> 0 -> cexp (F2R (Float beta m e)) <= e )%Z ->
  generic_format (F2R (Float beta m e)).
Proof using .
Admitted.

Lemma generic_format_F2R' :
  forall (x : R) (f : float beta),
  F2R f = x ->
  (x <> 0%R -> (cexp x <= Fexp f)%Z) ->
  generic_format x.
Proof using .
Admitted.

Theorem canonical_opp :
  forall m e,
  canonical (Float beta m e) ->
  canonical (Float beta (-m) e).
Proof using .
Admitted.

Theorem canonical_abs :
  forall m e,
  canonical (Float beta m e) ->
  canonical (Float beta (Z.abs m) e).
Proof using .
Admitted.

Theorem canonical_0 :
  canonical (Float beta 0 (fexp (mag beta 0%R))).
Proof using .
Admitted.

Theorem canonical_unique :
  forall f1 f2,
  canonical f1 ->
  canonical f2 ->
  F2R f1 = F2R f2 ->
  f1 = f2.
Proof using .
Admitted.

Theorem scaled_mantissa_generic :
  forall x,
  generic_format x ->
  scaled_mantissa x = IZR (Ztrunc (scaled_mantissa x)).
Proof using .
Admitted.

Theorem scaled_mantissa_mult_bpow :
  forall x,
  (scaled_mantissa x * bpow (cexp x))%R = x.
Proof using .
Admitted.

Theorem scaled_mantissa_0 :
  scaled_mantissa 0 = 0%R.
Proof using .
Admitted.

Theorem scaled_mantissa_opp :
  forall x,
  scaled_mantissa (-x) = (-scaled_mantissa x)%R.
Proof using .
Admitted.

Theorem scaled_mantissa_abs :
  forall x,
  scaled_mantissa (Rabs x) = Rabs (scaled_mantissa x).
Proof using .
Admitted.

Theorem generic_format_opp :
  forall x, generic_format x -> generic_format (-x).
Proof using .
Admitted.

Theorem generic_format_abs :
  forall x, generic_format x -> generic_format (Rabs x).
Proof using .
Admitted.

Theorem generic_format_abs_inv :
  forall x, generic_format (Rabs x) -> generic_format x.
Proof using .
Admitted.

Theorem cexp_fexp :
  forall x ex,
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
  cexp x = fexp ex.
Proof using .
Admitted.

Theorem cexp_fexp_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  cexp x = fexp ex.
Proof using .
Admitted.

Theorem mantissa_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  (0 < x * bpow (- fexp ex) < 1)%R.
Proof using .
Admitted.

Theorem scaled_mantissa_lt_1 :
  forall x ex,
  (Rabs x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  (Rabs (scaled_mantissa x) < 1)%R.
Proof using valid_exp_.
Admitted.

Theorem scaled_mantissa_lt_bpow :
  forall x,
  (Rabs (scaled_mantissa x) < bpow (mag beta x - cexp x))%R.
Proof using .
Admitted.

Theorem mag_generic_gt :
  forall x, (x <> 0)%R ->
  generic_format x ->
  (cexp x < mag beta x)%Z.
Proof using valid_exp_.
Admitted.

Lemma mantissa_DN_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Zfloor (x * bpow (- fexp ex)) = Z0.
Proof using .
Admitted.

Lemma mantissa_UP_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Zceil (x * bpow (- fexp ex)) = 1%Z.
Proof using .
Admitted.

Theorem generic_format_discrete :
  forall x m,
  let e := cexp x in
  (F2R (Float beta m e) < x < F2R (Float beta (m + 1) e))%R ->
  ~ generic_format x.
Proof using .
Admitted.

Theorem generic_format_canonical :
  forall f, canonical f ->
  generic_format (F2R f).
Proof using .
Admitted.

Theorem generic_format_ge_bpow :
  forall emin,
  ( forall e, (emin <= fexp e)%Z ) ->
  forall x,
  (0 < x)%R ->
  generic_format x ->
  (bpow emin <= x)%R.
Proof using .
Admitted.

Theorem abs_lt_bpow_prec:
  forall prec,
  (forall e, (e - prec <= fexp e)%Z) ->

  forall x,
  (Rabs x < bpow (prec + cexp x))%R.
Proof using .
Admitted.

Theorem generic_format_bpow_inv' :
  forall e,
  generic_format (bpow e) ->
  (fexp (e + 1) <= e)%Z.
Proof using .
Admitted.

Theorem generic_format_bpow_inv :
  forall e,
  generic_format (bpow e) ->
  (fexp e <= e)%Z.
Proof using valid_exp_.
Admitted.

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
Admitted.

Theorem Zrnd_ZR_or_AW :
  forall x, rnd x = Ztrunc x \/ rnd x = Zaway x.
Proof using valid_rnd.
Admitted.

Definition round x :=
  F2R (Float beta (rnd (scaled_mantissa x)) (cexp x)).

Theorem round_bounded_large_pos :
  forall x ex,
  (fexp ex < ex)%Z ->
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (bpow (ex - 1) <= round x <= bpow ex)%R.
Proof using valid_rnd.
Admitted.

Theorem round_bounded_small_pos :
  forall x ex,
  (ex <= fexp ex)%Z ->
  (bpow (ex - 1) <= x < bpow ex)%R ->
  round x = 0%R \/ round x = bpow (fexp ex).
Proof using valid_rnd.
Admitted.

Lemma round_le_pos :
  forall x y, (0 < x)%R -> (x <= y)%R -> (round x <= round y)%R.
Proof using valid_exp_ valid_rnd.
Admitted.

Theorem round_generic :
  forall x,
  generic_format x ->
  round x = x.
Proof using valid_rnd.
Admitted.

Theorem round_0 :
  round 0 = 0%R.
Proof using valid_rnd.
Admitted.

Theorem exp_small_round_0_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  round x = 0%R -> (ex <= fexp ex)%Z .
Proof using valid_rnd.
Admitted.

Lemma generic_format_round_pos :
  forall x,
  (0 < x)%R ->
  generic_format (round x).
Proof using valid_exp_ valid_rnd.
Admitted.

End Fcore_generic_round_pos.

Theorem round_ext :
  forall rnd1 rnd2,
  ( forall x, rnd1 x = rnd2 x ) ->
  forall x,
  round rnd1 x = round rnd2 x.
Proof using .
Admitted.

Section Zround_opp.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Definition Zrnd_opp x := Z.opp (rnd (-x)).

Global Instance valid_rnd_opp : Valid_rnd Zrnd_opp.
Proof using valid_rnd.
Admitted.

Theorem round_opp :
  forall x,
  round rnd (- x) = Ropp (round Zrnd_opp x).
Proof using .
Admitted.

End Zround_opp.

Global Instance valid_rnd_DN : Valid_rnd Zfloor.
Proof using .
Admitted.

Global Instance valid_rnd_UP : Valid_rnd Zceil.
Proof using .
Admitted.

Global Instance valid_rnd_ZR : Valid_rnd Ztrunc.
Proof using .
Admitted.

Global Instance valid_rnd_AW : Valid_rnd Zaway.
Proof using .
Admitted.

Section monotone.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_DN_or_UP :
  forall x,
  round rnd x = round Zfloor x \/ round rnd x = round Zceil x.
Proof using valid_rnd.
Admitted.

Theorem round_ZR_or_AW :
  forall x,
  round rnd x = round Ztrunc x \/ round rnd x = round Zaway x.
Proof using valid_rnd.
Admitted.

Theorem round_le :
  forall x y, (x <= y)%R -> (round rnd x <= round rnd y)%R.
Proof using valid_exp_ valid_rnd.
Admitted.

Theorem round_ge_generic :
  forall x y, generic_format x -> (x <= y)%R -> (x <= round rnd y)%R.
Proof using valid_exp_ valid_rnd.
Admitted.

Theorem round_le_generic :
  forall x y, generic_format y -> (x <= y)%R -> (round rnd x <= y)%R.
Proof using valid_exp_ valid_rnd.
Admitted.

End monotone.

Theorem round_abs_abs :
  forall P : R -> R -> Prop,
  ( forall rnd (Hr : Valid_rnd rnd) x, (0 <= x)%R -> P x (round rnd x) ) ->
  forall rnd {Hr : Valid_rnd rnd} x, P (Rabs x) (Rabs (round rnd x)).
Proof using valid_exp_.
Admitted.

Theorem round_bounded_large :
  forall rnd {Hr : Valid_rnd rnd} x ex,
  (fexp ex < ex)%Z ->
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
  (bpow (ex - 1) <= Rabs (round rnd x) <= bpow ex)%R.
Proof using valid_exp_.
Admitted.

Theorem exp_small_round_0 :
  forall rnd {Hr : Valid_rnd rnd} x ex,
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
   round rnd x = 0%R -> (ex <= fexp ex)%Z .
Proof using valid_exp_.
Admitted.

Section monotone_abs.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem abs_round_ge_generic :
  forall x y, generic_format x -> (x <= Rabs y)%R -> (x <= Rabs (round rnd y))%R.
Proof using valid_exp_ valid_rnd.
Admitted.

Theorem abs_round_le_generic :
  forall x y, generic_format y -> (Rabs x <= y)%R -> (Rabs (round rnd x) <= y)%R.
Proof using valid_exp_ valid_rnd.
Admitted.

End monotone_abs.

Theorem round_DN_opp :
  forall x,
  round Zfloor (-x) = (- round Zceil x)%R.
Proof using .
Admitted.

Theorem round_UP_opp :
  forall x,
  round Zceil (-x) = (- round Zfloor x)%R.
Proof using .
Admitted.

Theorem round_ZR_opp :
  forall x,
  round Ztrunc (- x) = Ropp (round Ztrunc x).
Proof using .
Admitted.

Theorem round_ZR_abs :
  forall x,
  round Ztrunc (Rabs x) = Rabs (round Ztrunc x).
Proof using valid_exp_.
Admitted.

Theorem round_AW_opp :
  forall x,
  round Zaway (- x) = Ropp (round Zaway x).
Proof using .
Admitted.

Theorem round_AW_abs :
  forall x,
  round Zaway (Rabs x) = Rabs (round Zaway x).
Proof using valid_exp_.
Admitted.

Theorem round_ZR_DN :
  forall x,
  (0 <= x)%R ->
  round Ztrunc x = round Zfloor x.
Proof using .
Admitted.

Theorem round_ZR_UP :
  forall x,
  (x <= 0)%R ->
  round Ztrunc x = round Zceil x.
Proof using .
Admitted.

Theorem round_AW_UP :
  forall x,
  (0 <= x)%R ->
  round Zaway x = round Zceil x.
Proof using .
Admitted.

Theorem round_AW_DN :
  forall x,
  (x <= 0)%R ->
  round Zaway x = round Zfloor x.
Proof using .
Admitted.

Theorem generic_format_round :
  forall rnd { Hr : Valid_rnd rnd } x,
  generic_format (round rnd x).
Proof using valid_exp_.
Admitted.

Theorem round_DN_pt :
  forall x,
  Rnd_DN_pt generic_format x (round Zfloor x).
Proof using valid_exp_.
Admitted.

Theorem generic_format_satisfies_any :
  satisfies_any generic_format.
Proof using valid_exp_.
Admitted.

Theorem round_UP_pt :
  forall x,
  Rnd_UP_pt generic_format x (round Zceil x).
Proof using valid_exp_.
Admitted.

Theorem round_ZR_pt :
  forall x,
  Rnd_ZR_pt generic_format x (round Ztrunc x).
Proof using valid_exp_.
Admitted.

Lemma round_DN_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  round Zfloor x = 0%R.
Proof using .
Admitted.

Theorem round_DN_UP_lt :
  forall x, ~ generic_format x ->
  (round Zfloor x < x < round Zceil x)%R.
Proof using valid_exp_.
Admitted.

Lemma round_UP_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  round Zceil x = (bpow (fexp ex)).
Proof using .
Admitted.

Theorem generic_format_EM :
  forall x,
  generic_format x \/ ~generic_format x.
Proof using valid_exp_.
Admitted.

Section round_large.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma round_large_pos_ge_bpow :
  forall x e,
  (0 < round rnd x)%R ->
  (bpow e <= x)%R ->
  (bpow e <= round rnd x)%R.
Proof using valid_rnd.
Admitted.

End round_large.

Theorem mag_round_ZR :
  forall x,
  (round Ztrunc x <> 0)%R ->
  (mag beta (round Ztrunc x) = mag beta x :> Z).
Proof using valid_exp_.
Admitted.

Theorem mag_round :
  forall rnd {Hrnd : Valid_rnd rnd} x,
  (round rnd x <> 0)%R ->
  (mag beta (round rnd x) = mag beta x :> Z) \/
  Rabs (round rnd x) = bpow (Z.max (mag beta x) (fexp (mag beta x))).
Proof using valid_exp_.
Admitted.

Theorem mag_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  (mag beta (round Zfloor x) = mag beta x :> Z).
Proof using valid_exp_.
Admitted.

Theorem cexp_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  cexp (round Zfloor x) = cexp x.
Proof using valid_exp_.
Admitted.

Theorem scaled_mantissa_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  scaled_mantissa (round Zfloor x) = IZR (Zfloor (scaled_mantissa x)).
Proof using valid_exp_.
Admitted.

Theorem generic_N_pt_DN_or_UP :
  forall x f,
  Rnd_N_pt generic_format x f ->
  f = round Zfloor x \/ f = round Zceil x.
Proof using valid_exp_.
Admitted.

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
Admitted.

End not_FTZ.

Section monotone_exp.

Class Monotone_exp :=
  monotone_exp : forall ex ey, (ex <= ey)%Z -> (fexp ex <= fexp ey)%Z.

Context { monotone_exp_ : Monotone_exp }.

Global Instance monotone_exp_not_FTZ : Exp_not_FTZ.
Proof using monotone_exp_ valid_exp_.
Admitted.

Lemma cexp_le_bpow :
  forall (x : R) (e : Z),
  x <> 0%R ->
  (Rabs x < bpow e)%R ->
  (cexp x <= fexp e)%Z.
Proof using monotone_exp_.
Admitted.

Lemma cexp_ge_bpow :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= Rabs x)%R ->
  (fexp e <= cexp x)%Z.
Proof using monotone_exp_.
Admitted.

Lemma lt_cexp_pos :
  forall x y,
  (0 < y)%R ->
  (cexp x < cexp y)%Z ->
  (x < y)%R.
Proof using monotone_exp_.
Admitted.

Theorem lt_cexp :
  forall x y,
  (y <> 0)%R ->
  (cexp x < cexp y)%Z ->
  (Rabs x < Rabs y)%R.
Proof using monotone_exp_.
Admitted.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem mag_round_ge :
  forall x,
  round rnd x <> 0%R ->
  (mag beta x <= mag beta (round rnd x))%Z.
Proof using valid_exp_ valid_rnd.
Admitted.

Theorem cexp_round_ge :
  forall x,
  round rnd x <> 0%R ->
  (cexp x <= cexp (round rnd x))%Z.
Proof using monotone_exp_ valid_exp_ valid_rnd.
Admitted.

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
Admitted.

Theorem Znearest_ge_floor :
  forall x,
  (Zfloor x <= Znearest x)%Z.
Proof using .
Admitted.

Theorem Znearest_le_ceil :
  forall x,
  (Znearest x <= Zceil x)%Z.
Proof using .
Admitted.

Global Instance valid_rnd_N : Valid_rnd Znearest.
Proof using .
Admitted.

Theorem Znearest_N_strict :
  forall x,
  (x - IZR (Zfloor x) <> /2)%R ->
  (Rabs (x - IZR (Znearest x)) < /2)%R.
Proof using .
Admitted.

Theorem Znearest_half :
  forall x,
  (Rabs (x - IZR (Znearest x)) <= /2)%R.
Proof using .
Admitted.

Theorem Znearest_imp :
  forall x n,
  (Rabs (x - IZR n) < /2)%R ->
  Znearest x = n.
Proof using .
Admitted.

Theorem round_N_pt :
  forall x,
  Rnd_N_pt generic_format x (round Znearest x).
Proof using valid_exp_.
Admitted.

Theorem round_N_middle :
  forall x,
  (x - round Zfloor x = round Zceil x - x)%R ->
  round Znearest x = if choice (Zfloor (scaled_mantissa x)) then round Zceil x else round Zfloor x.
Proof using .
Admitted.

Lemma round_N_small_pos :
  forall x,
  forall ex,
  (Raux.bpow beta (ex - 1) <= x < Raux.bpow beta ex)%R ->
  (ex < fexp ex)%Z ->
  (round Znearest x = 0)%R.
Proof using .
Admitted.

End Znearest.

Section rndNA.

Global Instance valid_rnd_NA : Valid_rnd (Znearest (Zle_bool 0)) := valid_rnd_N _.

Theorem round_NA_pt :
  forall x,
  Rnd_NA_pt generic_format x (round (Znearest (Zle_bool 0)) x).
Proof using valid_exp_.
Admitted.

End rndNA.

Notation Znearest0 := (Znearest (fun x => (Zlt_bool x 0))).

Section rndN0.

Global Instance valid_rnd_N0 : Valid_rnd Znearest0 := valid_rnd_N _.

Theorem round_N0_pt :
  forall x,
  Rnd_N0_pt generic_format x (round Znearest0 x).
Proof using valid_exp_.
Admitted.

End rndN0.

Section rndN_opp.

Theorem Znearest_opp :
  forall choice x,
  Znearest choice (- x) = (- Znearest (fun t => negb (choice (- (t + 1))%Z)) x)%Z.
Proof using .
Admitted.

Theorem round_N_opp :
  forall choice,
  forall x,
  round (Znearest choice) (-x) = (- round (Znearest (fun t => negb (choice (- (t + 1))%Z))) x)%R.
Proof using .
Admitted.

Lemma round_N0_opp :
  forall x,
  (round Znearest0 (- x) = - round Znearest0 x)%R.
Proof using .
Admitted.

End rndN_opp.

Lemma round_N_small :
  forall choice,
  forall x,
  forall ex,
  (Raux.bpow beta (ex - 1) <= Rabs x < Raux.bpow beta ex)%R ->
  (ex < fexp ex)%Z ->
  (round (Znearest choice) x = 0)%R.
Proof using .
Admitted.

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
Admitted.

Theorem generic_inclusion_lt_ge :
  forall e1 e2,
  ( forall e, (e1 < e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x < bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using .
Admitted.

Theorem generic_inclusion :
  forall e,
  (fexp2 e <= fexp1 e)%Z ->
  forall x,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using valid_exp1 valid_exp2.
Admitted.

Theorem generic_inclusion_le_ge :
  forall e1 e2,
  (e1 < e2)%Z ->
  ( forall e, (e1 < e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x <= bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using valid_exp1 valid_exp2.
Admitted.

Theorem generic_inclusion_le :
  forall e2,
  ( forall e, (e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (Rabs x <= bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using valid_exp1 valid_exp2.
Admitted.

Theorem generic_inclusion_ge :
  forall e1,
  ( forall e, (e1 < e)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof using .
Admitted.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem generic_round_generic :
  forall x,
  generic_format fexp1 x ->
  generic_format fexp1 (round fexp2 rnd x).
Proof using valid_exp1 valid_exp2 valid_rnd.
Admitted.

End Inclusion.

End Generic.

Notation ZnearestA := (Znearest (Zle_bool 0)).

Section rndNA_opp.

Lemma round_NA_opp :
  forall beta : radix,
  forall (fexp : Z -> Z),
  forall x,
  (round beta fexp ZnearestA (- x) = - round beta fexp ZnearestA x)%R.
Admitted.

End rndNA_opp.

Notation rndDN := Zfloor (only parsing).
Notation rndUP := Zceil (only parsing).
Notation rndZR := Ztrunc (only parsing).
Notation rndNA := ZnearestA (only parsing).

End Generic_fmt.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Generic_fmt.

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
Admitted.

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
Admitted.

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
Admitted.

End Fcalc_div.

End Div.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Div.

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
Admitted.

Theorem Falign_spec_exp:
  forall f1 f2 : float beta,
  snd (Falign f1 f2) = Z.min (Fexp f1) (Fexp f2).
Proof using .
Admitted.

Definition Fopp (f1 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  Float (-m1)%Z e1.

Theorem F2R_opp :
  forall f1 : float beta,
  (F2R (Fopp f1) = -F2R f1)%R.
Proof using .
Admitted.

Definition Fabs (f1 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  Float (Z.abs m1)%Z e1.

Theorem F2R_abs :
  forall f1 : float beta,
  (F2R (Fabs f1) = Rabs (F2R f1))%R.
Proof using .
Admitted.

Definition Fplus (f1 f2 : float beta) : float beta :=
  let '(m1, m2 ,e) := Falign f1 f2 in
  Float (m1 + m2) e.

Theorem F2R_plus :
  forall f1 f2 : float beta,
  F2R (Fplus f1 f2) = (F2R f1 + F2R f2)%R.
Proof using .
Admitted.

Theorem Fplus_same_exp :
  forall m1 m2 e,
  Fplus (Float m1 e) (Float m2 e) = Float (m1 + m2) e.
Proof using .
Admitted.

Theorem Fexp_Fplus :
  forall f1 f2 : float beta,
  Fexp (Fplus f1 f2) = Z.min (Fexp f1) (Fexp f2).
Proof using .
Admitted.

Definition Fminus (f1 f2 : float beta) :=
  Fplus f1 (Fopp f2).

Theorem F2R_minus :
  forall f1 f2 : float beta,
  F2R (Fminus f1 f2) = (F2R f1 - F2R f2)%R.
Proof using .
Admitted.

Theorem Fminus_same_exp :
  forall m1 m2 e,
  Fminus (Float m1 e) (Float m2 e) = Float (m1 - m2) e.
Proof using .
Admitted.

Definition Fmult (f1 f2 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  let '(Float m2 e2) := f2 in
  Float (m1 * m2) (e1 + e2).

Theorem F2R_mult :
  forall f1 f2 : float beta,
  F2R (Fmult f1 f2) = (F2R f1 * F2R f2)%R.
Proof using .
Admitted.

End Float_ops.

End Operations.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Operations.

Module Export Flocq_DOT_Core_DOT_Ulp.
Module Export Flocq.
Module Export Core.
Module Ulp.

Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.micromega.Psatz.
Import Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Float_prop.

Section Fcore_ulp.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Lemma Z_le_dec_aux: forall x y : Z, (x <= y)%Z \/ ~ (x <= y)%Z.
Proof using .
Admitted.

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
Admitted.

Lemma negligible_exp_spec': (negligible_exp = None /\ forall n, (fexp n < n)%Z)
           \/ exists n, (negligible_exp = Some n /\ (n <= fexp n)%Z).
Proof using .
Admitted.

Context { valid_exp : Valid_exp fexp }.

Lemma fexp_negligible_exp_eq: forall n m, (n <= fexp n)%Z -> (m <= fexp m)%Z -> fexp n = fexp m.
Proof using valid_exp.
Admitted.

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
Admitted.

Notation F := (generic_format beta fexp).

Theorem ulp_opp :
  forall x, ulp (- x) = ulp x.
Proof using .
Admitted.

Theorem ulp_abs :
  forall x, ulp (Rabs x) = ulp x.
Proof using .
Admitted.

Theorem ulp_ge_0:
  forall x, (0 <= ulp x)%R.
Proof using .
Admitted.

Theorem ulp_le_id:
  forall x,
    (0 < x)%R ->
    F x ->
    (ulp x <= x)%R.
Proof using .
Admitted.

Theorem ulp_le_abs:
  forall x,
    (x <> 0)%R ->
    F x ->
    (ulp x <= Rabs x)%R.
Proof using .
Admitted.

Theorem round_UP_DN_ulp :
  forall x, ~ F x ->
  round beta fexp Zceil x = (round beta fexp Zfloor x + ulp x)%R.
Proof using .
Admitted.

Theorem ulp_canonical :
  forall m e,
  m <> 0%Z ->
  canonical beta fexp (Float beta m e) ->
  ulp (F2R (Float beta m e)) = bpow e.
Proof using .
Admitted.

Theorem ulp_bpow :
  forall e, ulp (bpow e) = bpow (fexp (e + 1)).
Proof using .
Admitted.

Lemma generic_format_ulp_0 :
  F (ulp 0).
Proof using valid_exp.
Admitted.

Lemma generic_format_bpow_ge_ulp_0 :
  forall e, (ulp 0 <= bpow e)%R ->
  F (bpow e).
Proof using valid_exp.
Admitted.

Lemma generic_format_ulp :
  Exp_not_FTZ fexp ->
  forall x, F (ulp x).
Proof using valid_exp.
Admitted.

Lemma not_FTZ_generic_format_ulp :
  (forall x,  F (ulp x)) ->
  Exp_not_FTZ fexp.
Proof using .
Admitted.

Lemma ulp_ge_ulp_0 :
  Exp_not_FTZ fexp ->
  forall x, (ulp 0 <= ulp x)%R.
Proof using valid_exp.
Admitted.

Lemma not_FTZ_ulp_ge_ulp_0:
  (forall x, (ulp 0 <= ulp x)%R) ->
  Exp_not_FTZ fexp.
Proof using valid_exp.
Admitted.

Lemma ulp_le_pos :
  forall { Hm : Monotone_exp fexp },
  forall x y: R,
  (0 <= x)%R -> (x <= y)%R ->
  (ulp x <= ulp y)%R.
Proof using valid_exp.
Admitted.

Theorem ulp_le :
  forall { Hm : Monotone_exp fexp },
  forall x y: R,
  (Rabs x <= Rabs y)%R ->
  (ulp x <= ulp y)%R.
Proof using valid_exp.
Admitted.

Theorem eq_0_round_0_negligible_exp :
   negligible_exp = None -> forall rnd {Vr: Valid_rnd rnd} x,
     round beta fexp rnd x = 0%R -> x = 0%R.
Proof using valid_exp.
Admitted.

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
Admitted.

Theorem succ_eq_pos :
  forall x, (0 <= x)%R ->
  succ x = (x + ulp x)%R.
Proof using .
Admitted.

Theorem succ_opp :
  forall x, succ (-x) = (- pred x)%R.
Proof using .
Admitted.

Theorem pred_opp :
  forall x, pred (-x) = (- succ x)%R.
Proof using .
Admitted.

Theorem pred_bpow :
  forall e, pred (bpow e) = (bpow e - bpow (fexp e))%R.
Proof using .
Admitted.

Theorem id_m_ulp_ge_bpow :
  forall x e,  F x ->
  x <> ulp x ->
  (bpow e < x)%R ->
  (bpow e <= x - ulp x)%R.
Proof using .
Admitted.

Theorem id_p_ulp_le_bpow :
  forall x e, (0 < x)%R -> F x ->
  (x < bpow e)%R ->
  (x + ulp x <= bpow e)%R.
Proof using .
Admitted.

Lemma generic_format_pred_aux1:
  forall x, (0 < x)%R -> F x ->
  x <> bpow (mag beta x - 1) ->
  F (x - ulp x).
Proof using .
Admitted.

Lemma generic_format_pred_aux2 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x = bpow (e - 1) ->
  F (x - bpow (fexp (e - 1))).
Proof using valid_exp.
Admitted.

Lemma generic_format_succ_aux1 :
  forall x, (0 < x)%R -> F x ->
  F (x + ulp x).
Proof using valid_exp.
Admitted.

Lemma generic_format_pred_pos :
  forall x, F x -> (0 < x)%R ->
  F (pred_pos x).
Proof using valid_exp.
Admitted.

Theorem generic_format_succ :
  forall x, F x ->
  F (succ x).
Proof using valid_exp.
Admitted.

Theorem generic_format_pred :
  forall x, F x ->
  F (pred x).
Proof using valid_exp.
Admitted.

Lemma pred_pos_lt_id :
  forall x, (x <> 0)%R ->
  (pred_pos x < x)%R.
Proof using .
Admitted.

Theorem succ_gt_id :
  forall x, (x <> 0)%R ->
  (x < succ x)%R.
Proof using .
Admitted.

Theorem pred_lt_id :
  forall x,  (x <> 0)%R ->
  (pred x < x)%R.
Proof using .
Admitted.

Theorem succ_ge_id :
  forall x, (x <= succ x)%R.
Proof using .
Admitted.

Theorem pred_le_id :
  forall x, (pred x <= x)%R.
Proof using .
Admitted.

Lemma pred_pos_ge_0 :
  forall x,
  (0 < x)%R -> F x -> (0 <= pred_pos x)%R.
Proof using valid_exp.
Admitted.

Theorem pred_ge_0 :
  forall x,
  (0 < x)%R -> F x -> (0 <= pred x)%R.
Proof using valid_exp.
Admitted.

Lemma pred_pos_plus_ulp_aux1 :
  forall x, (0 < x)%R -> F x ->
  x <> bpow (mag beta x - 1) ->
  ((x - ulp x) + ulp (x-ulp x) = x)%R.
Proof using .
Admitted.

Lemma pred_pos_plus_ulp_aux2 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x =  bpow (e - 1) ->
  (x - bpow (fexp (e-1)) <> 0)%R ->
  ((x - bpow (fexp (e-1))) + ulp (x - bpow (fexp (e-1))) = x)%R.
Proof using valid_exp.
Admitted.

Lemma pred_pos_plus_ulp_aux3 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x =  bpow (e - 1) ->
  (x - bpow (fexp (e-1)) = 0)%R ->
  (ulp 0 = x)%R.
Proof using valid_exp.
Admitted.

Lemma pred_pos_plus_ulp :
  forall x, (0 < x)%R -> F x ->
  (pred_pos x + ulp (pred_pos x) = x)%R.
Proof using valid_exp.
Admitted.

Theorem pred_plus_ulp :
  forall x, (0 < x)%R -> F x ->
  (pred x + ulp (pred x))%R = x.
Proof using valid_exp.
Admitted.

Theorem mag_plus_eps :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  mag beta (x + eps) = mag beta x :> Z.
Proof using .
Admitted.

Theorem round_DN_plus_eps_pos :
  forall x, (0 <= x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  round beta fexp Zfloor (x + eps) = x.
Proof using valid_exp.
Admitted.

Theorem round_UP_plus_eps_pos :
  forall x, (0 <= x)%R -> F x ->
  forall eps, (0 < eps <= ulp x)%R ->
  round beta fexp Zceil (x + eps) = (x + ulp x)%R.
Proof using valid_exp.
Admitted.

Theorem round_UP_pred_plus_eps_pos :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 < eps <= ulp (pred x) )%R ->
  round beta fexp Zceil (pred x + eps) = x.
Proof using valid_exp.
Admitted.

Theorem round_DN_minus_eps_pos :
  forall x,  (0 < x)%R -> F x ->
  forall eps, (0 < eps <= ulp (pred x))%R ->
  round beta fexp Zfloor (x - eps) = pred x.
Proof using valid_exp.
Admitted.

Theorem round_DN_plus_eps:
  forall x, F x ->
  forall eps, (0 <= eps < if (Rle_bool 0 x) then (ulp x)
                                     else (ulp (pred (-x))))%R ->
  round beta fexp Zfloor (x + eps) = x.
Proof using valid_exp.
Admitted.

Theorem round_UP_plus_eps :
  forall x, F x ->
  forall eps, (0 < eps <= if (Rle_bool 0 x) then (ulp x)
                                     else (ulp (pred (-x))))%R ->
  round beta fexp Zceil (x + eps) = (succ x)%R.
Proof using valid_exp.
Admitted.

Lemma le_pred_pos_lt :
  forall x y,
  F x -> F y ->
  (0 <= x < y)%R ->
  (x <= pred_pos y)%R.
Proof using valid_exp.
Admitted.

Lemma succ_le_lt_aux:
  forall x y,
  F x -> F y ->
  (0 <= x)%R -> (x < y)%R ->
  (succ x <= y)%R.
Proof using valid_exp.
Admitted.

Theorem succ_le_lt:
  forall x y,
  F x -> F y ->
  (x < y)%R ->
  (succ x <= y)%R.
Proof using valid_exp.
Admitted.

Theorem pred_ge_gt :
  forall x y,
  F x -> F y ->
  (x < y)%R ->
  (x <= pred y)%R.
Proof using valid_exp.
Admitted.

Theorem succ_gt_ge :
  forall x y,
  (y <> 0)%R ->
  (x <= y)%R ->
  (x < succ y)%R.
Proof using .
Admitted.

Theorem pred_lt_le :
  forall x y,
  (x <> 0)%R ->
  (x <= y)%R ->
  (pred x < y)%R.
Proof using .
Admitted.

Lemma succ_pred_pos :
  forall x, F x -> (0 < x)%R -> succ (pred x) = x.
Proof using valid_exp.
Admitted.

Theorem pred_ulp_0 :
  pred (ulp 0) = 0%R.
Proof using valid_exp.
Admitted.

Theorem succ_0 :
  succ 0 = ulp 0.
Proof using .
Admitted.

Theorem pred_0 :
  pred 0 = Ropp (ulp 0).
Proof using .
Admitted.

Lemma pred_succ_pos :
  forall x, F x -> (0 < x)%R ->
  pred (succ x) = x.
Proof using valid_exp.
Admitted.

Theorem succ_pred :
  forall x, F x ->
  succ (pred x) = x.
Proof using valid_exp.
Admitted.

Theorem pred_succ :
  forall x, F x ->
  pred (succ x) = x.
Proof using valid_exp.
Admitted.

Theorem round_UP_pred_plus_eps :
  forall x, F x ->
  forall eps, (0 < eps <= if Rle_bool x 0 then ulp x
                          else ulp (pred x))%R ->
  round beta fexp Zceil (pred x + eps) = x.
Proof using valid_exp.
Admitted.

Theorem round_DN_minus_eps:
  forall x,  F x ->
  forall eps, (0 < eps <= if (Rle_bool x 0) then (ulp x)
                                     else (ulp (pred x)))%R ->
  round beta fexp Zfloor (x - eps) = pred x.
Proof using valid_exp.
Admitted.

Theorem error_lt_ulp :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < ulp x)%R.
Proof using valid_exp.
Admitted.

Theorem error_le_ulp :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (Rabs (round beta fexp rnd x - x) <= ulp x)%R.
Proof using valid_exp.
Admitted.

Theorem error_le_half_ulp :
  forall choice x,
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * ulp x)%R.
Proof using valid_exp.
Admitted.

Theorem ulp_DN :
  forall x, (0 <= x)%R ->
  ulp (round beta fexp Zfloor x) = ulp x.
Proof using valid_exp.
Admitted.

Theorem round_neq_0_negligible_exp :
  negligible_exp = None -> forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R -> (round beta fexp rnd x <> 0)%R.
Proof using valid_exp.
Admitted.

Theorem error_lt_ulp_round :
  forall { Hm : Monotone_exp fexp } rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < ulp (round beta fexp rnd x))%R.
Proof using valid_exp.
Admitted.

Lemma error_le_ulp_round :
  forall { Hm : Monotone_exp fexp } rnd { Zrnd : Valid_rnd rnd } x,
  (Rabs (round beta fexp rnd x - x) <= ulp (round beta fexp rnd x))%R.
Proof using valid_exp.
Admitted.

Theorem error_le_half_ulp_round :
  forall { Hm : Monotone_exp fexp },
  forall choice x,
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * ulp (round beta fexp (Znearest choice) x))%R.
Proof using valid_exp.
Admitted.

Theorem pred_le :
  forall x y, F x -> F y -> (x <= y)%R ->
  (pred x <= pred y)%R.
Proof using valid_exp.
Admitted.

Theorem succ_le :
  forall x y, F x -> F y -> (x <= y)%R ->
  (succ x <= succ y)%R.
Proof using valid_exp.
Admitted.

Theorem pred_le_inv: forall x y, F x -> F y
   -> (pred x <= pred y)%R -> (x <= y)%R.
Proof using valid_exp.
Admitted.

Theorem succ_le_inv: forall x y, F x -> F y
   -> (succ x <= succ y)%R -> (x <= y)%R.
Proof using valid_exp.
Admitted.

Theorem pred_lt :
  forall x y, F x -> F y -> (x < y)%R ->
  (pred x < pred y)%R.
Proof using valid_exp.
Admitted.

Theorem succ_lt :
  forall x y, F x -> F y -> (x < y)%R ->
  (succ x < succ y)%R.
Proof using valid_exp.
Admitted.

Lemma succ_le_plus_ulp :
  forall { Hm : Monotone_exp fexp } x,
  (succ x <= x + ulp x)%R.
Proof using .
Admitted.

Lemma generic_format_plus_ulp :
  forall { Hm : Monotone_exp fexp } x,
  generic_format beta fexp x ->
  generic_format beta fexp (x + ulp x).
Proof using valid_exp.
Admitted.

Theorem round_DN_ge_UP_gt :
  forall x y, F y ->
  (y < round beta fexp Zceil x -> y <= round beta fexp Zfloor x)%R.
Proof using valid_exp.
Admitted.

Theorem round_UP_le_DN_lt :
  forall x y, F y ->
  (round beta fexp Zfloor x < y -> round beta fexp Zceil x <= y)%R.
Proof using valid_exp.
Admitted.

Theorem pred_UP_le_DN :
  forall x, (pred (round beta fexp Zceil x) <= round beta fexp Zfloor x)%R.
Proof using valid_exp.
Admitted.

Theorem UP_le_succ_DN :
  forall x, (round beta fexp Zceil x <= succ (round beta fexp Zfloor x))%R.
Proof using valid_exp.
Admitted.

Theorem pred_UP_eq_DN :
  forall x,  ~ F x ->
  (pred (round beta fexp Zceil x) = round beta fexp Zfloor x)%R.
Proof using valid_exp.
Admitted.

Theorem succ_DN_eq_UP :
  forall x,  ~ F x ->
  (succ (round beta fexp Zfloor x) = round beta fexp Zceil x)%R.
Proof using valid_exp.
Admitted.

Theorem round_DN_eq :
  forall x d, F d -> (d <= x < succ d)%R ->
  round beta fexp Zfloor x = d.
Proof using valid_exp.
Admitted.

Theorem round_UP_eq :
  forall x u, F u -> (pred u < x <= u)%R ->
  round beta fexp Zceil x = u.
Proof using valid_exp.
Admitted.

Lemma ulp_ulp_0 : forall {H : Exp_not_FTZ fexp},
  ulp (ulp 0) = ulp 0.
Proof using valid_exp.
Admitted.

Lemma ulp_succ_pos :
  forall x, F x -> (0 < x)%R ->
  ulp (succ x) = ulp x \/ succ x = bpow (mag beta x).
Proof using .
Admitted.

Theorem ulp_pred_pos :
  forall x, F x -> (0 < pred x)%R ->
  ulp (pred x) = ulp x \/ x = bpow (mag beta x - 1).
Proof using valid_exp.
Admitted.

Lemma ulp_round_pos :
  forall { Not_FTZ_ : Exp_not_FTZ fexp},
   forall rnd { Zrnd : Valid_rnd rnd } x,
  (0 < x)%R -> ulp (round beta fexp rnd x) = ulp x
     \/ round beta fexp rnd x = bpow (mag beta x).
Proof using valid_exp.
Admitted.

Theorem ulp_round : forall { Not_FTZ_ : Exp_not_FTZ fexp},
   forall rnd { Zrnd : Valid_rnd rnd } x,
     ulp (round beta fexp rnd x) = ulp x
         \/ Rabs (round beta fexp rnd x) = bpow (mag beta x).
Proof using valid_exp.
Admitted.

Lemma succ_round_ge_id :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <= succ (round beta fexp rnd x))%R.
Proof using valid_exp.
Admitted.

Lemma pred_round_le_id :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (pred (round beta fexp rnd x) <= x)%R.
Proof using valid_exp.
Admitted.

Theorem round_N_le_midp: forall choice u v,
  F u -> (v < (u + succ u)/2)%R
      -> (round beta fexp (Znearest choice)  v <= u)%R.
Proof using valid_exp.
Admitted.

Theorem round_N_ge_midp: forall choice u v,
 F u ->  ((u + pred u)/2 < v)%R
      -> (u <= round beta fexp (Znearest choice)  v)%R.
Proof using valid_exp.
Admitted.

Lemma round_N_ge_ge_midp : forall choice u v,
       F u ->
       (u <= round beta fexp (Znearest choice) v)%R ->
       ((u + pred u) / 2 <= v)%R.
Proof using valid_exp.
Admitted.

Lemma round_N_le_le_midp : forall choice u v,
       F u ->
       (round beta fexp (Znearest choice) v <= u)%R ->
       (v <= (u + succ u) / 2)%R.
Proof using valid_exp.
Admitted.

Lemma round_N_eq_DN: forall choice x,
       let d:=round beta fexp Zfloor x in
       let u:=round beta fexp Zceil x in
      (x<(d+u)/2)%R ->
     round beta fexp (Znearest choice) x = d.
Proof using valid_exp.
Admitted.

Lemma round_N_eq_DN_pt: forall choice x d u,
      Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
      (x<(d+u)/2)%R ->
     round beta fexp (Znearest choice) x = d.
Proof using valid_exp.
Admitted.

Lemma round_N_eq_UP: forall choice x,
      let d:=round beta fexp Zfloor x in
      let u:=round beta fexp Zceil x in
     ((d+u)/2 < x)%R ->
     round beta fexp (Znearest choice) x = u.
Proof using valid_exp.
Admitted.

Lemma round_N_eq_UP_pt: forall choice x d u,
      Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
      ((d+u)/2 < x)%R ->
     round beta fexp (Znearest choice) x = u.
Proof using valid_exp.
Admitted.

Lemma round_N_plus_ulp_ge :
  forall { Hm : Monotone_exp fexp } choice1 choice2 x,
  let rx := round beta fexp (Znearest choice2) x in
  (x <= round beta fexp (Znearest choice1) (rx + ulp rx))%R.
Proof using valid_exp.
Admitted.

Lemma round_N_eq_ties: forall c1 c2 x,
   (x - round beta fexp Zfloor x <> round beta fexp Zceil x - x)%R ->
   (round beta fexp (Znearest c1) x = round beta fexp (Znearest c2) x)%R.
Proof using valid_exp.
Admitted.

End Fcore_ulp.

End Ulp.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Ulp.

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
Admitted.

Class Exists_NE :=
  exists_NE : Z.even beta = false \/ forall e,
  ((fexp e < e)%Z -> (fexp (e + 1) < e)%Z) /\ ((e <= fexp e)%Z -> fexp (fexp e + 1) = fexp e).

Context { exists_NE_ : Exists_NE }.

Theorem DN_UP_parity_generic_pos :
  DN_UP_parity_pos_prop.
Proof using exists_NE_ valid_exp.
Admitted.

Theorem DN_UP_parity_generic :
  DN_UP_parity_prop.
Proof using exists_NE_ valid_exp.
Admitted.

Theorem Rnd_NE_pt_total :
  round_pred_total Rnd_NE_pt.
Proof using exists_NE_ valid_exp.
Admitted.

Theorem Rnd_NE_pt_monotone :
  round_pred_monotone Rnd_NE_pt.
Proof using exists_NE_ valid_exp.
Admitted.

Theorem Rnd_NE_pt_round :
  round_pred Rnd_NE_pt.
Proof using exists_NE_ valid_exp.
Admitted.

Lemma round_NE_pt_pos :
  forall x,
  (0 < x)%R ->
  Rnd_NE_pt x (round beta fexp ZnearestE x).
Proof using exists_NE_ valid_exp.
Admitted.

Theorem round_NE_opp :
  forall x,
  round beta fexp ZnearestE (-x) = (- round beta fexp ZnearestE x)%R.
Proof using .
Admitted.

Lemma round_NE_abs:
  forall x : R,
  round beta fexp ZnearestE (Rabs x) = Rabs (round beta fexp ZnearestE x).
Proof using valid_exp.
Admitted.

Theorem round_NE_pt :
  forall x,
  Rnd_NE_pt x (round beta fexp ZnearestE x).
Proof using exists_NE_ valid_exp.
Admitted.

End Fcore_rnd_NE.

Notation rndNE := ZnearestE (only parsing).

End Round_NE.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Round_NE.

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
Admitted.

Theorem generic_format_FIX :
  forall x, FIX_format x -> generic_format beta FIX_exp x.
Proof using .
Admitted.

Theorem FIX_format_generic :
  forall x, generic_format beta FIX_exp x -> FIX_format x.
Proof using .
Admitted.

Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
Proof using .
Admitted.

Global Instance FIX_exp_monotone : Monotone_exp FIX_exp.
Proof using .
Admitted.

Theorem ulp_FIX :
  forall x, ulp beta FIX_exp x = bpow emin.
Proof using .
Admitted.

Global Instance exists_NE_FIX :
      Exists_NE beta FIX_exp.
Proof using .
Admitted.

End RND_FIX.

Theorem round_FIX_IZR :
  forall f x,
  round radix2 (FIX_exp 0) f x = IZR (f x).
Admitted.

End FIX.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_FIX.

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
Admitted.

Theorem FIX_format_FLX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FLX_format x ->
  FIX_format beta (e - prec) x.
Proof using .
Admitted.

Theorem FLX_format_generic :
  forall x, generic_format beta FLX_exp x -> FLX_format x.
Proof using prec_gt_0_.
Admitted.

Theorem generic_format_FLX :
  forall x, FLX_format x -> generic_format beta FLX_exp x.
Proof using .
Admitted.

Theorem FLX_format_satisfies_any :
  satisfies_any FLX_format.
Proof using prec_gt_0_.
Admitted.

Theorem FLX_format_FIX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FIX_format beta (e - prec) x ->
  FLX_format x.
Proof using prec_gt_0_.
Admitted.

Inductive FLXN_format (x : R) : Prop :=
  FLXN_spec (f : float beta) :
    x = F2R f ->
    (x <> 0%R -> Zpower beta (prec - 1) <= Z.abs (Fnum f) < Zpower beta prec)%Z ->
    FLXN_format x.

Theorem generic_format_FLXN :
  forall x, FLXN_format x -> generic_format beta FLX_exp x.
Proof using .
Admitted.

Theorem FLXN_format_generic :
  forall x, generic_format beta FLX_exp x -> FLXN_format x.
Proof using prec_gt_0_.
Admitted.

Theorem FLXN_format_satisfies_any :
  satisfies_any FLXN_format.
Proof using prec_gt_0_.
Admitted.

Lemma negligible_exp_FLX :
   negligible_exp FLX_exp = None.
Proof using prec_gt_0_.
Admitted.

Theorem generic_format_FLX_1 :
  generic_format beta FLX_exp 1.
Proof using prec_gt_0_.
Admitted.

Theorem ulp_FLX_0: (ulp beta FLX_exp 0 = 0)%R.
Proof using prec_gt_0_.
Admitted.

Lemma ulp_FLX_1 : ulp beta FLX_exp 1 = bpow (-prec + 1).
Proof using .
Admitted.

Lemma succ_FLX_1 : (succ beta FLX_exp 1 = 1 + bpow (-prec + 1))%R.
Proof using .
Admitted.

Theorem eq_0_round_0_FLX :
   forall rnd {Vr: Valid_rnd rnd} x,
     round beta FLX_exp rnd x = 0%R -> x = 0%R.
Proof using prec_gt_0_.
Admitted.

Theorem gt_0_round_gt_0_FLX :
   forall rnd {Vr: Valid_rnd rnd} x,
     (0 < x)%R -> (0 < round beta FLX_exp rnd x)%R.
Proof using prec_gt_0_.
Admitted.

Theorem ulp_FLX_le :
  forall x, (ulp beta FLX_exp x <= Rabs x * bpow (1-prec))%R.
Proof using prec_gt_0_.
Admitted.

Theorem ulp_FLX_ge :
  forall x, (Rabs x * bpow (-prec) <= ulp beta FLX_exp x)%R.
Proof using prec_gt_0_.
Admitted.

Lemma ulp_FLX_exact_shift :
  forall x e,
  (ulp beta FLX_exp (x * bpow e) = ulp beta FLX_exp x * bpow e)%R.
Proof using prec_gt_0_.
Admitted.

Lemma succ_FLX_exact_shift :
  forall x e,
  (succ beta FLX_exp (x * bpow e) = succ beta FLX_exp x * bpow e)%R.
Proof using prec_gt_0_.
Admitted.

Lemma pred_FLX_exact_shift :
  forall x e,
  (pred beta FLX_exp (x * bpow e) = pred beta FLX_exp x * bpow e)%R.
Proof using prec_gt_0_.
Admitted.

Global Instance FLX_exp_monotone : Monotone_exp FLX_exp.
Proof using .
Admitted.

Hypothesis NE_prop : Z.even beta = false \/ (1 < prec)%Z.

Global Instance exists_NE_FLX : Exists_NE beta FLX_exp.
Proof using NE_prop.
Admitted.

End RND_FLX.

End FLX.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_FLX.

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
Admitted.

Theorem generic_format_FLT :
  forall x, FLT_format x -> generic_format beta FLT_exp x.
Proof using .
Admitted.

Theorem FLT_format_generic :
  forall x, generic_format beta FLT_exp x -> FLT_format x.
Proof using prec_gt_0_.
Admitted.

Theorem generic_format_FLT_bpow :
  forall e, (emin <= e)%Z -> generic_format beta FLT_exp (bpow e).
Proof using prec_gt_0_.
Admitted.

Theorem FLT_format_bpow :
  forall e, (emin <= e)%Z -> FLT_format (bpow e).
Proof using prec_gt_0_.
Admitted.

Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
Proof using prec_gt_0_.
Admitted.

Theorem cexp_FLT_FLX :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  cexp beta FLT_exp x = cexp beta (FLX_exp prec) x.
Proof using .
Admitted.

Global Instance FLT_exp_monotone : Monotone_exp FLT_exp.
Proof using .
Admitted.

Global Instance exists_NE_FLT :
  (Z.even beta = false \/ (1 < prec)%Z) ->
  Exists_NE beta FLT_exp.
Proof using .
Admitted.

Theorem generic_format_FLT_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  generic_format beta (FLX_exp prec) x ->
  generic_format beta FLT_exp x.
Proof using .
Admitted.

Theorem generic_format_FLX_FLT :
  forall x : R,
  generic_format beta FLT_exp x -> generic_format beta (FLX_exp prec) x.
Proof using .
Admitted.

Theorem round_FLT_FLX : forall rnd x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FLT_exp rnd x = round beta (FLX_exp prec) rnd x.
Proof using .
Admitted.

Theorem cexp_FLT_FIX :
  forall x, x <> 0%R ->
  (Rabs x < bpow (emin + prec))%R ->
  cexp beta FLT_exp x = cexp beta (FIX_exp emin) x.
Proof using .
Admitted.

Theorem generic_format_FIX_FLT :
  forall x : R,
  generic_format beta FLT_exp x ->
  generic_format beta (FIX_exp emin) x.
Proof using .
Admitted.

Theorem generic_format_FLT_FIX :
  forall x : R,
  (Rabs x <= bpow (emin + prec))%R ->
  generic_format beta (FIX_exp emin) x ->
  generic_format beta FLT_exp x.
Proof using prec_gt_0_.
Admitted.

Lemma negligible_exp_FLT :
  exists n, negligible_exp FLT_exp = Some n /\ (n <= emin)%Z.
Proof using prec_gt_0_.
Admitted.

Theorem generic_format_FLT_1 :
  (emin <= 0)%Z ->
  generic_format beta FLT_exp 1.
Proof using prec_gt_0_.
Admitted.

Theorem ulp_FLT_0 :
  ulp beta FLT_exp 0 = bpow emin.
Proof using prec_gt_0_.
Admitted.

Theorem ulp_FLT_small :
  forall x, (Rabs x < bpow (emin + prec))%R ->
  ulp beta FLT_exp x = bpow emin.
Proof using prec_gt_0_.
Admitted.

Theorem ulp_FLT_le :
  forall x, (bpow (emin + prec - 1) <= Rabs x)%R ->
  (ulp beta FLT_exp x <= Rabs x * bpow (1 - prec))%R.
Proof using .
Admitted.

Theorem ulp_FLT_gt :
  forall x, (Rabs x * bpow (-prec) < ulp beta FLT_exp x)%R.
Proof using prec_gt_0_.
Admitted.

Lemma ulp_FLT_exact_shift :
  forall x e,
  (x <> 0)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (ulp beta FLT_exp (x * bpow e) = ulp beta FLT_exp x * bpow e)%R.
Proof using .
Admitted.

Lemma succ_FLT_exact_shift_pos :
  forall x e,
  (0 < x)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
Proof using .
Admitted.

Lemma succ_FLT_exact_shift :
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
  (succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
Proof using .
Admitted.

Lemma pred_FLT_exact_shift :
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
  (pred beta FLT_exp (x * bpow e) = pred beta FLT_exp x * bpow e)%R.
Proof using .
Admitted.

Theorem ulp_FLT_pred_pos :
  forall x,
  generic_format beta FLT_exp x ->
  (0 <= x)%R ->
  ulp beta FLT_exp (pred beta FLT_exp x) = ulp beta FLT_exp x \/
  (x = bpow (mag beta x - 1) /\ ulp beta FLT_exp (pred beta FLT_exp x) = (ulp beta FLT_exp x / IZR beta)%R).
Proof using prec_gt_0_.
Admitted.

End RND_FLT.

End FLT.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_FLT.

Module Export Flocq_DOT_Core_DOT_Core.
Module Export Flocq.
Module Export Core.
Module Core.

Export Flocq.Core.Zaux Flocq.Core.Raux Flocq.Core.Defs Flocq.Core.Digits Flocq.Core.Float_prop Flocq.Core.Round_pred Flocq.Core.Generic_fmt Flocq.Core.Round_NE Flocq.Core.FIX Flocq.Core.FLX Flocq.Core.FLT Flocq.Core.Ulp.

End Core.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_Core.

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
Admitted.

Theorem cexp_inbetween_float_loc_Exact :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x \/ l = loc_Exact <->
   e <= fexp (Zdigits beta m + e) \/ l = loc_Exact)%Z.
Proof using valid_exp.
Admitted.

Theorem inbetween_float_round :
  forall rnd choice,
  ( forall x m l, inbetween_int m x l -> rnd x = choice m l ) ->
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof using .
Admitted.

Definition cond_incr (b : bool) m := if b then (m + 1)%Z else m.

Lemma le_cond_incr_le :
  forall b m, (m <= cond_incr b m <= m + 1)%Z.
Proof using .
Admitted.

Theorem inbetween_float_round_sign :
  forall rnd choice,
  ( forall x m l, inbetween_int m (Rabs x) l ->
    rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l) ) ->
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp rnd x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l)) e).
Proof using .
Admitted.

Theorem inbetween_int_DN :
  forall x m l,
  inbetween_int m x l ->
  Zfloor x = m.
Proof using .
Admitted.

Theorem inbetween_float_DN :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Zfloor x = F2R (Float beta m e).
Proof using .
Admitted.

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
Admitted.

Theorem inbetween_float_DN_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Zfloor x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_DN (Rlt_bool x 0) l) m)) e).
Proof using .
Admitted.

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
Admitted.

Theorem inbetween_float_UP :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Zceil x = F2R (Float beta (cond_incr (round_UP l) m) e).
Proof using .
Admitted.

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
Admitted.

Theorem inbetween_float_UP_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Zceil x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_UP (Rlt_bool x 0) l) m)) e).
Proof using .
Admitted.

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
Admitted.

Theorem inbetween_float_ZR :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Ztrunc x = F2R (Float beta (cond_incr (round_ZR (Zlt_bool m 0) l) m) e).
Proof using .
Admitted.

Theorem inbetween_int_ZR_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Ztrunc x = cond_Zopp (Rlt_bool x 0) m.
Proof using .
Admitted.

Theorem inbetween_float_ZR_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Ztrunc x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) m) e).
Proof using .
Admitted.

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
Admitted.

Theorem inbetween_int_N_sign :
  forall choice x m l,
  inbetween_int m (Rabs x) l ->
  Znearest choice x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (if Rlt_bool x 0 then negb (choice (-(m + 1))%Z) else choice m) l) m).
Proof using .
Admitted.

Theorem inbetween_int_NE :
  forall x m l,
  inbetween_int m x l ->
  ZnearestE x = cond_incr (round_N (negb (Z.even m)) l) m.
Proof using .
Admitted.

Theorem inbetween_float_NE :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp ZnearestE x = F2R (Float beta (cond_incr (round_N (negb (Z.even m)) l) m) e).
Proof using .
Admitted.

Theorem inbetween_int_NE_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  ZnearestE x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (negb (Z.even m)) l) m).
Proof using .
Admitted.

Theorem inbetween_float_NE_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp ZnearestE x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (negb (Z.even m)) l) m)) e).
Proof using .
Admitted.

Theorem inbetween_int_NA :
  forall x m l,
  inbetween_int m x l ->
  ZnearestA x = cond_incr (round_N (Zle_bool 0 m) l) m.
Proof using .
Admitted.

Theorem inbetween_float_NA :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp ZnearestA x = F2R (Float beta (cond_incr (round_N (Zle_bool 0 m) l) m) e).
Proof using .
Admitted.

Theorem inbetween_int_NA_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  ZnearestA x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N true l) m).
Proof using .
Admitted.

Theorem inbetween_float_NA_sign :
  forall x m l,
  let e := cexp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp ZnearestA x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_N true l) m)) e).
Proof using .
Admitted.

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
Admitted.

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
Admitted.

Theorem generic_format_truncate :
  forall m e l,
  (0 <= m)%Z ->
  let '(m', e', l') := truncate (m, e, l) in
  format (F2R (Float beta m' e')).
Proof using .
Admitted.

Theorem truncate_correct_format :
  forall m e,
  m <> Z0 ->
  let x := F2R (Float beta m e) in
  generic_format beta fexp x ->
  (e <= fexp (Zdigits beta m + e))%Z ->
  let '(m', e', l') := truncate (m, e, loc_Exact) in
  x = F2R (Float beta m' e') /\ e' = cexp beta fexp x.
Proof using .
Admitted.

Theorem truncate_correct_partial' :
  forall x m e l,
  (0 < x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x)%Z ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\ e' = cexp beta fexp x.
Proof using valid_exp.
Admitted.

Theorem truncate_correct_partial :
  forall x m e l,
  (0 < x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\ e' = cexp beta fexp x.
Proof using valid_exp.
Admitted.

Theorem truncate_correct' :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x)%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = cexp beta fexp x \/ (l' = loc_Exact /\ format x)).
Proof using valid_exp.
Admitted.

Theorem truncate_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = cexp beta fexp x \/ (l' = loc_Exact /\ format x)).
Proof using valid_exp.
Admitted.

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
Admitted.

Theorem round_trunc_any_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (choice m' l') e').
Proof using inbetween_int_valid valid_exp valid_rnd.
Admitted.

Theorem round_trunc_any_correct' :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= cexp beta fexp x)%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (choice m' l') e').
Proof using inbetween_int_valid valid_exp valid_rnd.
Admitted.

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
Admitted.

Theorem round_trunc_sign_any_correct' :
  forall x m e l,
  inbetween_float beta m e (Rabs x) l ->
  (e <= cexp beta fexp x)%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m' l')) e').
Proof using inbetween_int_valid valid_exp valid_rnd.
Admitted.

Theorem round_trunc_sign_any_correct :
  forall x m e l,
  inbetween_float beta m e (Rabs x) l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m' l')) e').
Proof using inbetween_int_valid valid_exp valid_rnd.
Admitted.

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
Admitted.

End Fcalc_round.

End Round.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Round.

Module Export Flocq_DOT_Calc_DOT_Plus.

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
Admitted.

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
Admitted.

End Plus.

End Flocq_DOT_Calc_DOT_Plus.

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
Admitted.

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
Admitted.

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
Admitted.

End Fcalc_sqrt.

End Sqrt.

End Calc.

End Flocq.

End Flocq_DOT_Calc_DOT_Sqrt.

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
Admitted.

Theorem FLXN_format_FTZ :
  forall x, FTZ_format x -> FLXN_format beta prec x.
Proof using .
Admitted.

Theorem generic_format_FTZ :
  forall x, FTZ_format x -> generic_format beta FTZ_exp x.
Proof using .
Admitted.

Theorem FTZ_format_generic :
  forall x, generic_format beta FTZ_exp x -> FTZ_format x.
Proof using prec_gt_0_.
Admitted.

Theorem FTZ_format_satisfies_any :
  satisfies_any FTZ_format.
Proof using prec_gt_0_.
Admitted.

Theorem FTZ_format_FLXN :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  FLXN_format beta prec x -> FTZ_format x.
Proof using prec_gt_0_.
Admitted.

Theorem ulp_FTZ_0 :
  ulp beta FTZ_exp 0 = bpow (emin+prec-1).
Proof using prec_gt_0_.
Admitted.

Section FTZ_round.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Definition Zrnd_FTZ x :=
  if Rle_bool 1 (Rabs x) then rnd x else Z0.

Global Instance valid_rnd_FTZ : Valid_rnd Zrnd_FTZ.
Proof using valid_rnd.
Admitted.

Theorem round_FTZ_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FTZ_exp Zrnd_FTZ x = round beta (FLX_exp prec) rnd x.
Proof using prec_gt_0_.
Admitted.

Theorem round_FTZ_small :
  forall x : R,
  (Rabs x < bpow (emin + prec - 1))%R ->
  round beta FTZ_exp Zrnd_FTZ x = 0%R.
Proof using valid_rnd.
Admitted.

End FTZ_round.

End RND_FTZ.

End FTZ.

End Core.

End Flocq.

End Flocq_DOT_Core_DOT_FTZ.

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
Admitted.

Lemma relative_error_le_conversion :
  forall x b, (0 <= b)%R ->
  (Rabs (round beta fexp rnd x - x) <= b * Rabs x)%R ->
  exists eps,
  (Rabs eps <= b)%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof using valid_rnd.
Admitted.

Lemma relative_error_le_conversion_inv :
  forall x b,
  (exists eps,
   (Rabs eps <= b)%R /\ round beta fexp rnd x = (x * (1 + eps))%R) ->
  (Rabs (round beta fexp rnd x - x) <= b * Rabs x)%R.
Proof using .
Admitted.

Lemma relative_error_le_conversion_round_inv :
  forall x b,
  (exists eps,
   (Rabs eps <= b)%R /\ x = (round beta fexp rnd x * (1 + eps))%R) ->
  (Rabs (round beta fexp rnd x - x) <= b * Rabs (round beta fexp rnd x))%R.
Proof using .
Admitted.

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
Admitted.

Theorem relative_error_ex :
  forall x,
  (bpow emin <= Rabs x)%R ->
  exists eps,
  (Rabs eps < bpow (-p + 1))%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof using Hmin prop_exp valid_rnd.
Admitted.

Theorem relative_error_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs x)%R.
Proof using Hmin prop_exp valid_rnd.
Admitted.

Theorem relative_error_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps < bpow (-p + 1))%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof using Hmin prop_exp valid_rnd.
Admitted.

Theorem relative_error_round :
  (0 < p)%Z ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs (round beta fexp rnd x))%R.
Proof using Hmin prop_exp valid_rnd.
Admitted.

Theorem relative_error_round_F2R_emin :
  (0 < p)%Z ->
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs (round beta fexp rnd x))%R.
Proof using Hmin prop_exp valid_rnd.
Admitted.

Variable choice : Z -> bool.

Theorem relative_error_N :
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs x)%R.
Proof using Hmin prop_exp.
Admitted.

Theorem relative_error_N_ex :
  forall x,
  (bpow emin <= Rabs x)%R ->
  exists eps,
  (Rabs eps <= /2 * bpow (-p + 1))%R /\ round beta fexp (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hmin prop_exp.
Admitted.

Theorem relative_error_N_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs x)%R.
Proof using Hmin prop_exp.
Admitted.

Theorem relative_error_N_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps <= /2 * bpow (-p + 1))%R /\ round beta fexp (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hmin prop_exp.
Admitted.

Theorem relative_error_N_round :
  (0 < p)%Z ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs (round beta fexp (Znearest choice) x))%R.
Proof using Hmin prop_exp.
Admitted.

Theorem relative_error_N_round_F2R_emin :
  (0 < p)%Z ->
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs (round beta fexp (Znearest choice) x))%R.
Proof using Hmin prop_exp.
Admitted.

End Fprop_relative_generic.

Section Fprop_relative_FLX.

Variable prec : Z.
Variable Hp : Z.lt 0 prec.

Lemma relative_error_FLX_aux :
  forall k, (prec <= k - FLX_exp prec k)%Z.
Proof using .
Admitted.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem relative_error_FLX :
  forall x,
  (x <> 0)%R ->
  (Rabs (round beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof using Hp valid_rnd.
Admitted.

Theorem relative_error_FLX_ex :
  forall x,
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLX_exp prec) rnd x = (x * (1 + eps))%R.
Proof using Hp valid_rnd.
Admitted.

Theorem relative_error_FLX_round :
  forall x,
  (x <> 0)%R ->
  (Rabs (round beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs (round beta (FLX_exp prec) rnd x))%R.
Proof using Hp valid_rnd.
Admitted.

Variable choice : Z -> bool.

Theorem relative_error_N_FLX :
  forall x,
  (Rabs (round beta (FLX_exp prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof using Hp.
Admitted.

Definition u_ro := (/2 * bpow (-prec + 1))%R.

Lemma u_ro_pos : (0 <= u_ro)%R.
Proof using .
Admitted.

Lemma u_ro_lt_1 : (u_ro < 1)%R.
Proof using Hp.
Admitted.

Lemma u_rod1pu_ro_pos : (0 <= u_ro / (1 + u_ro))%R.
Proof using .
Admitted.

Lemma u_rod1pu_ro_le_u_ro : (u_ro / (1 + u_ro) <= u_ro)%R.
Proof using .
Admitted.

Theorem relative_error_N_FLX' :
  forall x,
  (Rabs (round beta (FLX_exp prec) (Znearest choice) x - x)
   <= u_ro / (1 + u_ro) * Rabs x)%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLX_ex :
  forall x,
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLX_exp prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLX'_ex :
  forall x,
  exists eps,
  (Rabs eps <= u_ro / (1 + u_ro))%R /\
  round beta (FLX_exp prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hp.
Admitted.

Lemma relative_error_N_round_ex_derive :
  forall x rx,
  (exists eps, (Rabs eps <= u_ro / (1 + u_ro))%R /\ rx = (x * (1 + eps))%R) ->
  exists eps, (Rabs eps <= u_ro)%R /\ x = (rx * (1 + eps))%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLX_round_ex :
  forall x,
  exists eps,
  (Rabs eps <= u_ro)%R /\
  x = (round beta (FLX_exp prec) (Znearest choice) x * (1 + eps))%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLX_round :
  forall x,
  (Rabs (round beta (FLX_exp prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs(round beta (FLX_exp prec) (Znearest choice) x))%R.
Proof using Hp.
Admitted.

End Fprop_relative_FLX.

Section Fprop_relative_FLT.

Variable emin prec : Z.
Variable Hp : Z.lt 0 prec.

Lemma relative_error_FLT_aux :
  forall k, (emin + prec - 1 < k)%Z -> (prec <= k - FLT_exp emin prec k)%Z.
Proof using .
Admitted.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem relative_error_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof using Hp valid_rnd.
Admitted.

Theorem relative_error_FLT_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof using Hp valid_rnd.
Admitted.

Theorem relative_error_FLT_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) rnd x = (x * (1 + eps))%R.
Proof using Hp valid_rnd.
Admitted.

Theorem relative_error_FLT_ex :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) rnd x = (x * (1 + eps))%R.
Proof using Hp valid_rnd.
Admitted.

Variable choice : Z -> bool.

Theorem relative_error_N_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLT_ex :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLT_round :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (round beta (FLT_exp emin prec) (Znearest choice) x))%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLT_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLT_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLT_round_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (round beta (FLT_exp emin prec) (Znearest choice) x))%R.
Proof using Hp.
Admitted.

Lemma error_N_FLT_aux :
  forall x,
  (0 < x)%R ->
  exists eps, exists  eta,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\
  (Rabs eta <= /2 * bpow (emin))%R      /\
  (eps*eta=0)%R /\
  round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps) + eta)%R.
Proof using Hp.
Admitted.

Theorem relative_error_N_FLT'_ex :
  forall x,
  exists eps eta : R,
  (Rabs eps <= u_ro prec / (1 + u_ro prec))%R /\
  (Rabs eta <= /2 * bpow emin)%R /\
  (eps * eta = 0)%R /\
  round beta (FLT_exp emin prec) (Znearest choice) x
  = (x * (1 + eps) + eta)%R.
Proof using Hp.
Admitted.

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
Admitted.

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
Admitted.

End Fprop_relative.

End Relative.

End AVOID_RESERVED_Prop.

End Flocq.

End Flocq_DOT_Prop_DOT_Relative.

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
Admitted.

Theorem B2SF_SF2B :
  forall x Hx,
  B2SF (SF2B x Hx) = x.
Proof using .
Admitted.

Theorem valid_binary_B2SF :
  forall x,
  valid_binary (B2SF x) = true.
Proof using .
Admitted.

Theorem SF2B_B2SF :
  forall x H,
  SF2B (B2SF x) H = x.
Proof using .
Admitted.

Theorem SF2B_B2SF_valid :
  forall x,
  SF2B (B2SF x) (valid_binary_B2SF x) = x.
Proof using .
Admitted.

Theorem B2R_SF2B :
  forall x Hx,
  B2R (SF2B x Hx) = SF2R radix2 x.
Proof using .
Admitted.

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
Admitted.

Theorem canonical_canonical_mantissa :
  forall (sx : bool) mx ex,
  canonical_mantissa mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof using .
Admitted.

Theorem canonical_bounded :
  forall sx mx ex,
  bounded mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof using .
Admitted.

Lemma emin_lt_emax :
  (emin < emax)%Z.
Proof using prec_gt_0_ prec_lt_emax_.
Admitted.

Lemma fexp_emax :
  fexp emax = (emax - prec)%Z.
Proof using prec_gt_0_ prec_lt_emax_.
Admitted.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof using .
Admitted.

Theorem FLT_format_B2R :
  forall x,
  FLT_format radix2 emin prec (B2R x).
Proof using prec_gt_0_.
Admitted.

Theorem B2SF_inj :
  forall x y : binary_float,
  B2SF x = B2SF y ->
  x = y.
Proof using .
Admitted.

Theorem SF2B'_B2SF :
  forall x,
  SF2B' (B2SF x) = x.
Proof using .
Admitted.

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
Admitted.

Theorem is_finite_strict_SF2B :
  forall x Hx,
  is_finite_strict (SF2B x Hx) = is_finite_strict_SF x.
Proof using .
Admitted.

Theorem B2R_inj:
  forall x y : binary_float,
  is_finite_strict x = true ->
  is_finite_strict y = true ->
  B2R x = B2R y ->
  x = y.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

Theorem is_finite_SF_B2SF :
  forall x,
  is_finite_SF (B2SF x) = is_finite x.
Proof using .
Admitted.

Theorem B2R_Bsign_inj:
  forall x y : binary_float,
    is_finite x = true ->
    is_finite y = true ->
    B2R x = B2R y ->
    Bsign x = Bsign y ->
    x = y.
Proof using .
Admitted.

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
Admitted.

Theorem is_nan_SF_B2SF :
  forall x,
  is_nan_SF (B2SF x) = is_nan x.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

Theorem B2R_Bopp :
  forall x,
  B2R (Bopp x) = (- B2R x)%R.
Proof using .
Admitted.

Theorem is_nan_Bopp :
  forall x,
  is_nan (Bopp x) = is_nan x.
Proof using .
Admitted.

Theorem is_finite_Bopp :
  forall x,
  is_finite (Bopp x) = is_finite x.
Proof using .
Admitted.

Theorem is_finite_strict_Bopp :
  forall x,
  is_finite_strict (Bopp x) = is_finite_strict x.
Proof using .
Admitted.

Lemma Bsign_Bopp :
  forall x, is_nan x = false -> Bsign (Bopp x) = negb (Bsign x).
Proof using .
Admitted.

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
Admitted.

Theorem is_nan_Babs :
  forall x,
  is_nan (Babs x) = is_nan x.
Proof using .
Admitted.

Theorem is_finite_Babs :
  forall x,
  is_finite (Babs x) = is_finite x.
Proof using .
Admitted.

Theorem is_finite_strict_Babs :
  forall x,
  is_finite_strict (Babs x) = is_finite_strict x.
Proof using .
Admitted.

Theorem Bsign_Babs :
  forall x,
  Bsign (Babs x) = false.
Proof using .
Admitted.

Theorem Babs_idempotent :
  forall (x: binary_float),
  Babs (Babs x) = Babs x.
Proof using .
Admitted.

Theorem Babs_Bopp :
  forall x,
  Babs (Bopp x) = Babs x.
Proof using .
Admitted.

Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  SFcompare (B2SF f1) (B2SF f2).

Theorem Bcompare_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bcompare f1 f2 = Some (Rcompare (B2R f1) (B2R f2)).
Proof using .
Admitted.

Theorem Bcompare_swap :
  forall x y,
  Bcompare y x = match Bcompare x y with Some c => Some (CompOpp c) | None => None end.
Proof using .
Admitted.

Definition Beqb (f1 f2 : binary_float) : bool := SFeqb (B2SF f1) (B2SF f2).

Theorem Beqb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Beqb f1 f2 = Req_bool (B2R f1) (B2R f2).
Proof using .
Admitted.

Theorem Beqb_refl :
  forall f, Beqb f f = negb (is_nan f).
Proof using .
Admitted.

Definition Bltb (f1 f2 : binary_float) : bool := SFltb (B2SF f1) (B2SF f2).

Theorem Bltb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bltb f1 f2 = Rlt_bool (B2R f1) (B2R f2).
Proof using .
Admitted.

Definition Bleb (f1 f2 : binary_float) : bool := SFleb (B2SF f1) (B2SF f2).

Theorem Bleb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bleb f1 f2 = Rle_bool (B2R f1) (B2R f2).
Proof using .
Admitted.

Theorem bounded_le_emax_minus_prec :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex)
   <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof using prec_gt_0_.
Admitted.

Theorem bounded_lt_emax :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R.
Proof using .
Admitted.

Theorem bounded_ge_emin :
  forall mx ex,
  bounded mx ex = true ->
  (bpow radix2 emin <= F2R (Float radix2 (Zpos mx) ex))%R.
Proof using .
Admitted.

Theorem abs_B2R_le_emax_minus_prec :
  forall x,
  (Rabs (B2R x) <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof using prec_gt_0_.
Admitted.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof using .
Admitted.

Theorem abs_B2R_ge_emin :
  forall x,
  is_finite_strict x = true ->
  (bpow radix2 emin <= Rabs (B2R x))%R.
Proof using .
Admitted.

Theorem bounded_canonical_lt_emax :
  forall mx ex,
  canonical radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R ->
  bounded mx ex = true.
Proof using prec_gt_0_ prec_lt_emax_.
Admitted.

Theorem shr_m_shr_record_of_loc :
  forall m l,
  shr_m (shr_record_of_loc m l) = m.
Proof using .
Admitted.

Theorem loc_of_shr_record_of_loc :
  forall m l,
  loc_of_shr_record (shr_record_of_loc m l) = l.
Proof using .
Admitted.

Lemma inbetween_shr_1 :
  forall x mrs e,
  (0 <= shr_m mrs)%Z ->
  inbetween_float radix2 (shr_m mrs) e x (loc_of_shr_record mrs) ->
  inbetween_float radix2 (shr_m (shr_1 mrs)) (e + 1) x (loc_of_shr_record (shr_1 mrs)).
Proof using .
Admitted.

Lemma shr_nat :
  forall mrs e n, (0 <= n)%Z ->
  shr mrs e n = (iter_nat shr_1 (Z.to_nat n) mrs, (e + n)%Z).
Proof using .
Admitted.

Lemma le_shr1_le :
  forall mrs, (0 <= shr_m mrs)%Z ->
  (0 <= shr_m (shr_1 mrs))%Z /\
  (2 * shr_m (shr_1 mrs) <= shr_m mrs < 2 * (shr_m (shr_1 mrs) + 1))%Z.
Proof using .
Admitted.

Theorem inbetween_shr :
  forall x m e l n,
  (0 <= m)%Z ->
  inbetween_float radix2 m e x l ->
  let '(mrs, e') := shr (shr_record_of_loc m l) e n in
  inbetween_float radix2 (shr_m mrs) e' x (loc_of_shr_record mrs).
Proof using .
Admitted.

Lemma le_shr_le :
  forall mrs e n,
  (0 <= shr_m mrs)%Z -> (0 <= n)%Z ->
  (0 <= shr_m (fst (shr mrs e n)))%Z /\
  (2 ^ n * shr_m (fst (shr mrs e n)) <= shr_m mrs < 2 ^ n * (shr_m (fst (shr mrs e n)) + 1))%Z.
Proof using .
Admitted.

Lemma shr_limit :
  forall mrs e n,
  ((0 < shr_m mrs)%Z \/ shr_m mrs = 0%Z /\ (shr_r mrs || shr_s mrs = true)%bool) ->
  (shr_m mrs < radix2 ^ (n - 1))%Z ->
  fst (shr mrs e n) = {| shr_m := 0%Z; shr_r := false; shr_s := true |}.
Proof using .
Admitted.

Theorem shr_truncate :
  forall f m e l,
  Valid_exp f ->
  (0 <= m)%Z ->
  shr (shr_record_of_loc m l) e (f (Zdigits2 m + e) - e)%Z =
  let '(m', e', l') := truncate radix2 f (m, e, l) in (shr_record_of_loc m' l', e').
Proof using .
Admitted.

Notation shr_fexp := (shr_fexp prec emax).

Theorem shr_fexp_truncate :
  forall m e l,
  (0 <= m)%Z ->
  shr_fexp m e l =
  let '(m', e', l') := truncate radix2 fexp (m, e, l) in (shr_record_of_loc m' l', e').
Proof using prec_gt_0_.
Admitted.

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
Admitted.

Lemma round_mode_choice_mode :
  forall md x m l,
  inbetween_int m (Rabs x) l ->
  round_mode md x = cond_Zopp (Rlt_bool x 0) (choice_mode md (Rlt_bool x 0) m l).
Proof using .
Admitted.

Global Instance valid_rnd_round_mode : forall m, Valid_rnd (round_mode m).
Proof using .
Admitted.

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
Admitted.

Theorem binary_overflow_correct :
  forall m s,
  valid_binary (binary_overflow m s) = true.
Proof using prec_gt_0_ prec_lt_emax_.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Theorem shl_align_correct':
  forall mx ex e,
  (e <= ex)%Z ->
  let (mx', ex') := shl_align mx ex e in
  F2R (Float radix2 (Zpos mx') e) = F2R (Float radix2 (Zpos mx) ex) /\
  ex' = e.
Proof using .
Admitted.

Theorem shl_align_correct :
  forall mx ex ex',
  let (mx', ex'') := shl_align mx ex ex' in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex'') /\
  (ex'' <= ex')%Z.
Proof using .
Admitted.

Theorem snd_shl_align :
  forall mx ex ex',
  (ex' <= ex)%Z ->
  snd (shl_align mx ex ex') = ex'.
Proof using .
Admitted.

Definition shl_align_fexp mx ex :=
  shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex)).

Theorem shl_align_fexp_correct :
  forall mx ex,
  let (mx', ex') := shl_align_fexp mx ex in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') /\
  (ex' <= fexp (Zdigits radix2 (Zpos mx') + ex'))%Z.
Proof using .
Admitted.

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
Admitted.

Theorem is_nan_binary_round :
  forall mode sx mx ex,
  is_nan_SF (binary_round mode sx mx ex) = false.
Proof using prec_gt_0_ prec_lt_emax_.
Admitted.

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
Admitted.

Theorem is_nan_binary_normalize :
  forall mode m e szero,
  is_nan (binary_normalize mode m e szero) = false.
Proof using .
Admitted.

Definition Fplus_naive sx mx ex sy my ey ez :=
  (Zplus (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))).

Lemma Fplus_naive_correct :
  forall sx mx ex sy my ey ez,
  (ez <= ex)%Z -> (ez <= ey)%Z ->
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  F2R (Float radix2 (Fplus_naive sx mx ex sy my ey ez) ez) = (x + y)%R.
Proof using .
Admitted.

Lemma sign_plus_overflow :
  forall m sx mx ex sy my ey,
  bounded mx ex = true ->
  bounded my ey = true ->
  let z := (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) + F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey))%R in
  (bpow radix2 emax <= Rabs (round radix2 fexp (round_mode m) z))%R ->
  sx = Rlt_bool z 0 /\ sx = sy.
Proof using prec_gt_0_.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Definition Bone := SF2B _ (proj1 (binary_round_correct mode_NE false 1 0)).

Theorem Bone_correct : B2R Bone = 1%R.
Proof using .
Admitted.

Theorem is_finite_strict_Bone :
  is_finite_strict Bone = true.
Proof using .
Admitted.

Theorem is_nan_Bone :
  is_nan Bone = false.
Proof using .
Admitted.

Theorem is_finite_Bone :
  is_finite Bone = true.
Proof using .
Admitted.

Theorem Bsign_Bone :
  Bsign Bone = false.
Proof using .
Admitted.

Lemma Bmax_float_proof :
  valid_binary
    (S754_finite false (shift_pos (Z.to_pos prec) 1 - 1) (emax - prec))
  = true.
Proof using prec_gt_0_ prec_lt_emax_.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma Bldexp_Bopp_NE x e : Bldexp mode_NE (Bopp x) e = Bopp (Bldexp mode_NE x e).
Proof using .
Admitted.

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
Admitted.

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
Admitted.

Theorem Bfrexp_correct :
  forall f,
  is_finite_strict f = true ->
  let (z, e) := Bfrexp f in
  (B2R f = B2R z * bpow radix2 e)%R /\
  ( (2 < emax)%Z -> (/2 <= Rabs (B2R z) < 1)%R /\ e = mag radix2 (B2R f) ).
Proof using .
Admitted.

Lemma Bulp_correct_aux :
  bounded 1 emin = true.
Proof using prec_gt_0_ prec_lt_emax_.
Admitted.

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
Admitted.

Theorem Bulp_correct :
  forall x,
  is_finite x = true ->
  B2R (Bulp x) = ulp radix2 fexp (B2R x) /\
  is_finite (Bulp x) = true /\
  Bsign (Bulp x) = false.
Proof using .
Admitted.

Theorem is_finite_strict_Bulp :
  forall x,
  is_finite_strict (Bulp x) = is_finite x.
Proof using .
Admitted.

Definition Bulp' x := Bldexp mode_NE Bone (fexp (snd (Bfrexp x))).

Theorem Bulp'_correct :
  (2 < emax)%Z ->
  forall x,
  is_finite x = true ->
  Bulp' x = Bulp x.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

Definition Bpred x := Bopp (Bsucc (Bopp x)).

Theorem is_nan_Bpred :
  forall x,
  is_nan (Bpred x) = is_nan x.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma FF2R_SF2FF :
  forall beta x,
  FF2R beta (SF2FF x) = SF2R beta x.
Admitted.

Definition is_nan_FF f :=
  match f with
  | F754_nan _ _ => true
  | _ => false
  end.

Lemma is_nan_SF2FF :
  forall x,
  is_nan_FF (SF2FF x) = is_nan_SF x.
Admitted.

Lemma is_nan_FF2SF :
  forall x,
  is_nan_SF (FF2SF x) = is_nan_FF x.
Admitted.

Lemma SF2FF_FF2SF :
  forall x,
  is_nan_FF x = false ->
  SF2FF (FF2SF x) = x.
Admitted.

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
Admitted.

Lemma sign_SF2FF :
  forall x,
  sign_FF (SF2FF x) = sign_SF x.
Admitted.

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
Admitted.

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
Admitted.

Lemma B2SF_FF2B :
  forall x Bx,
  B2SF (FF2B x Bx) = FF2SF x.
Proof using .
Admitted.

Lemma B2R_B2BSN :
  forall x, BinarySingleNaN.B2R (B2BSN x) = B2R x.
Proof using .
Admitted.

Lemma FF2SF_B2FF :
  forall x,
  FF2SF (B2FF x) = B2SF x.
Proof using .
Admitted.

Theorem FF2R_B2FF :
  forall x,
  FF2R radix2 (B2FF x) = B2R x.
Proof using .
Admitted.

Theorem B2FF_FF2B :
  forall x Hx,
  B2FF (FF2B x Hx) = x.
Proof using .
Admitted.

Theorem valid_binary_B2FF :
  forall x,
  valid_binary (B2FF x) = true.
Proof using .
Admitted.

Theorem FF2B_B2FF :
  forall x H,
  FF2B (B2FF x) H = x.
Proof using .
Admitted.

Theorem FF2B_B2FF_valid :
  forall x,
  FF2B (B2FF x) (valid_binary_B2FF x) = x.
Proof using .
Admitted.

Theorem B2R_FF2B :
  forall x Hx,
  B2R (FF2B x Hx) = FF2R radix2 x.
Proof using .
Admitted.

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
Admitted.

Theorem canonical_canonical_mantissa :
  forall (sx : bool) mx ex,
  canonical_mantissa mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof using .
Admitted.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof using .
Admitted.

Theorem FLT_format_B2R :
  forall x,
  FLT_format radix2 emin prec (B2R x).
Proof using prec_gt_0_.
Admitted.

Theorem B2FF_inj :
  forall x y : binary_float,
  B2FF x = B2FF y ->
  x = y.
Proof using .
Admitted.

Definition is_finite_strict f :=
  match f with
  | B754_finite _ _ _ _ => true
  | _ => false
  end.

Lemma is_finite_strict_B2BSN :
  forall x, BinarySingleNaN.is_finite_strict (B2BSN x) = is_finite_strict x.
Proof using .
Admitted.

Theorem B2R_inj:
  forall x y : binary_float,
  is_finite_strict x = true ->
  is_finite_strict y = true ->
  B2R x = B2R y ->
  x = y.
Proof using .
Admitted.

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
Admitted.

Definition is_finite f :=
  match f with
  | B754_finite _ _ _ _ => true
  | B754_zero _ => true
  | _ => false
  end.

Lemma is_finite_B2BSN :
  forall x, BinarySingleNaN.is_finite (B2BSN x) = is_finite x.
Proof using .
Admitted.

Theorem is_finite_FF2B :
  forall x Hx,
  is_finite (FF2B x Hx) = is_finite_FF x.
Proof using .
Admitted.

Theorem is_finite_B2FF :
  forall x,
  is_finite_FF (B2FF x) = is_finite x.
Proof using .
Admitted.

Theorem B2R_Bsign_inj:
  forall x y : binary_float,
    is_finite x = true ->
    is_finite y = true ->
    B2R x = B2R y ->
    Bsign x = Bsign y ->
    x = y.
Proof using .
Admitted.

Definition is_nan f :=
  match f with
  | B754_nan _ _ _ => true
  | _ => false
  end.

Lemma is_nan_B2BSN :
  forall x,
  BinarySingleNaN.is_nan (B2BSN x) =  is_nan x.
Proof using .
Admitted.

Theorem is_nan_FF2B :
  forall x Hx,
  is_nan (FF2B x Hx) = is_nan_FF x.
Proof using .
Admitted.

Theorem is_nan_B2FF :
  forall x,
  is_nan_FF (B2FF x) = is_nan x.
Proof using .
Admitted.

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
Admitted.

Theorem B2R_build_nan :
  forall x, B2R (build_nan x) = 0%R.
Proof using .
Admitted.

Theorem is_finite_build_nan :
  forall x, is_finite (build_nan x) = false.
Proof using .
Admitted.

Theorem is_nan_build_nan :
  forall x, is_nan (build_nan x) = true.
Proof using .
Admitted.

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
Admitted.

Lemma B2R_BSN2B :
  forall nan x, B2R (BSN2B nan x) = BinarySingleNaN.B2R x.
Proof using .
Admitted.

Lemma is_finite_BSN2B :
  forall nan x, is_finite (BSN2B nan x) = BinarySingleNaN.is_finite x.
Proof using .
Admitted.

Lemma is_nan_BSN2B :
  forall nan x, is_nan (BSN2B nan x) = BinarySingleNaN.is_nan x.
Proof using .
Admitted.

Lemma Bsign_B2BSN :
  forall x, is_nan x = false -> BinarySingleNaN.Bsign (B2BSN x) = Bsign x.
Proof using .
Admitted.

Lemma Bsign_BSN2B :
  forall nan x, BinarySingleNaN.is_nan x = false ->
  Bsign (BSN2B nan x) = BinarySingleNaN.Bsign x.
Proof using .
Admitted.

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
Admitted.

Lemma B2R_BSN2B' :
  forall x Nx,
  B2R (BSN2B' x Nx) = BinarySingleNaN.B2R x.
Proof using .
Admitted.

Lemma B2FF_BSN2B' :
  forall x Nx,
  B2FF (BSN2B' x Nx) = SF2FF (BinarySingleNaN.B2SF x).
Proof using .
Admitted.

Lemma Bsign_BSN2B' :
  forall x Nx,
  Bsign (BSN2B' x Nx) = BinarySingleNaN.Bsign x.
Proof using .
Admitted.

Lemma is_finite_BSN2B' :
  forall x Nx,
  is_finite (BSN2B' x Nx) = BinarySingleNaN.is_finite x.
Proof using .
Admitted.

Lemma is_nan_BSN2B' :
  forall x Nx,
  is_nan (BSN2B' x Nx) = false.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

Theorem B2R_Bopp :
  forall opp_nan x,
  B2R (Bopp opp_nan x) = (- B2R x)%R.
Proof using .
Admitted.

Theorem is_finite_Bopp :
  forall opp_nan x,
  is_finite (Bopp opp_nan x) = is_finite x.
Proof using .
Admitted.

Lemma Bsign_Bopp :
  forall opp_nan x, is_nan x = false -> Bsign (Bopp opp_nan x) = negb (Bsign x).
Proof using .
Admitted.

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
Admitted.

Theorem is_finite_Babs :
  forall abs_nan x,
  is_finite (Babs abs_nan x) = is_finite x.
Proof using .
Admitted.

Theorem Bsign_Babs :
  forall abs_nan x,
  is_nan x = false ->
  Bsign (Babs abs_nan x) = false.
Proof using .
Admitted.

Theorem Babs_idempotent :
  forall abs_nan (x: binary_float),
  is_nan x = false ->
  Babs abs_nan (Babs abs_nan x) = Babs abs_nan x.
Proof using .
Admitted.

Theorem Babs_Bopp :
  forall abs_nan opp_nan x,
  is_nan x = false ->
  Babs abs_nan (Bopp opp_nan x) = Babs abs_nan x.
Proof using .
Admitted.

Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2).

Theorem Bcompare_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bcompare f1 f2 = Some (Rcompare (B2R f1) (B2R f2)).
Proof using .
Admitted.

Theorem Bcompare_swap :
  forall x y,
  Bcompare y x = match Bcompare x y with Some c => Some (CompOpp c) | None => None end.
Proof using .
Admitted.

Theorem bounded_le_emax_minus_prec :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex)
   <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof using prec_gt_0_.
Admitted.

Theorem bounded_lt_emax :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R.
Proof using .
Admitted.

Theorem bounded_ge_emin :
  forall mx ex,
  bounded mx ex = true ->
  (bpow radix2 emin <= F2R (Float radix2 (Zpos mx) ex))%R.
Proof using .
Admitted.

Theorem abs_B2R_le_emax_minus_prec :
  forall x,
  (Rabs (B2R x) <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof using prec_gt_0_.
Admitted.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof using .
Admitted.

Theorem abs_B2R_ge_emin :
  forall x,
  is_finite_strict x = true ->
  (bpow radix2 emin <= Rabs (B2R x))%R.
Proof using .
Admitted.

Theorem bounded_canonical_lt_emax :
  forall mx ex,
  canonical radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R ->
  bounded mx ex = true.
Proof using prec_gt_0_ prec_lt_emax_.
Admitted.

Notation shr_fexp := (shr_fexp prec emax) (only parsing).

Theorem shr_fexp_truncate :
  forall m e l,
  (0 <= m)%Z ->
  shr_fexp m e l =
  let '(m', e', l') := truncate radix2 fexp (m, e, l) in (shr_record_of_loc m' l', e').
Proof using prec_gt_0_.
Admitted.

Definition binary_overflow m s :=
  SF2FF (binary_overflow prec emax m s).

Lemma eq_binary_overflow_FF2SF :
  forall x m s,
  FF2SF x = BinarySingleNaN.binary_overflow prec emax m s ->
  x = binary_overflow m s.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Definition shl_align_fexp mx ex :=
  shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex)).

Lemma shl_align_fexp_correct :
  forall mx ex,
  let (mx', ex') := shl_align_fexp mx ex in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') /\
  (ex' <= fexp (Zdigits radix2 (Zpos mx') + ex'))%Z.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Definition Bsqrt sqrt_nan m x :=
  BSN2B (sqrt_nan x) (Bsqrt m (B2BSN x)).

Theorem Bsqrt_correct :
  forall sqrt_nan m x,
  B2R (Bsqrt sqrt_nan m x) = round radix2 fexp (round_mode m) (sqrt (B2R x)) /\
  is_finite (Bsqrt sqrt_nan m x) = match x with B754_zero _ => true | B754_finite false _ _ _ => true | _ => false end /\
  (is_nan (Bsqrt sqrt_nan m x) = false -> Bsign (Bsqrt sqrt_nan m x) = Bsign x).
Proof using .
Admitted.

Definition Bnearbyint nearbyint_nan m x :=
  BSN2B (nearbyint_nan x) (Bnearbyint m (B2BSN x)).

Theorem Bnearbyint_correct :
  forall nearbyint_nan md x,
  B2R (Bnearbyint nearbyint_nan md x) = round radix2 (FIX_exp 0) (round_mode md) (B2R x) /\
  is_finite (Bnearbyint nearbyint_nan md x) = is_finite x /\
  (is_nan (Bnearbyint nearbyint_nan md x) = false -> Bsign (Bnearbyint nearbyint_nan md x) = Bsign x).
Proof using .
Admitted.

Definition Btrunc x := Btrunc (B2BSN x).

Theorem Btrunc_correct :
  forall x,
  IZR (Btrunc x) = round radix2 (FIX_exp 0) Ztrunc (B2R x).
Proof using prec_lt_emax_.
Admitted.

Definition Bone :=
  BSN2B' _ (@is_nan_Bone prec emax _ _).

Theorem Bone_correct : B2R Bone = 1%R.
Proof using .
Admitted.

Lemma is_finite_Bone : is_finite Bone = true.
Proof using .
Admitted.

Lemma Bsign_Bone : Bsign Bone = false.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

End Binary.

End Binary.

End IEEE754.

End Flocq.

End Flocq_DOT_IEEE754_DOT_Binary.

Module Export Flocq_DOT_IEEE754_DOT_Bits.

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
Admitted.

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
Admitted.

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
Admitted.

Theorem split_bits_inj :
  forall x y,
  (0 <= x < Zpower 2 (mw + ew + 1))%Z ->
  (0 <= y < Zpower 2 (mw + ew + 1))%Z ->
  split_bits x = split_bits y ->
  x = y.
Proof using He_gt_0 Hm_gt_0.
Admitted.

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
Admitted.

Theorem bits_of_binary_float_range:
  forall x, (0 <= bits_of_binary_float x < 2^(mw+ew+1))%Z.
Proof using He_gt_0 Hm_gt_0.
Admitted.

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
Admitted.

Definition binary_float_of_bits x :=
  FF2B prec emax _ (binary_float_of_bits_aux_correct x).

Theorem binary_float_of_bits_of_binary_float :
  forall x,
  binary_float_of_bits (bits_of_binary_float x) = x.
Proof using .
Admitted.

Theorem bits_of_binary_float_of_bits :
  forall x,
  (0 <= x < 2^(mw+ew+1))%Z ->
  bits_of_binary_float (binary_float_of_bits x) = x.
Proof using .
Admitted.

End Binary_Bits.

Section B32_Bits.

Arguments B754_nan {prec} {emax}.

Definition binary32 := binary_float 24 128.

Let Hprec : (0 < 24)%Z.
admit.
Defined.

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
Admitted.

Let Hprec_emax : (53 < 1024)%Z.
Admitted.

Let Hemax : (3 <= 1024)%Z.
Admitted.

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

End Flocq_DOT_IEEE754_DOT_Bits.

Module Export Flocq_DOT_IEEE754_DOT_PrimFloat.

Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Import Stdlib.ZArith.ZArith Stdlib.Reals.Reals Stdlib.Floats.Floats Stdlib.Floats.SpecFloat.
Import Flocq.Core.Zaux Flocq.IEEE754.BinarySingleNaN.

Definition Prim2B (x : float) : binary_float prec emax :=
  SF2B (Prim2SF x) (Prim2SF_valid x).

Definition B2Prim (x : binary_float prec emax) : float :=
  SF2Prim (B2SF x).

Lemma B2Prim_Prim2B : forall x, B2Prim (Prim2B x) = x.
Admitted.

Lemma Prim2B_B2Prim : forall x, Prim2B (B2Prim x) = x.
Admitted.

Lemma Prim2B_inj : forall x y, Prim2B x = Prim2B y -> x = y.
Admitted.

Lemma B2Prim_inj : forall x y, B2Prim x = B2Prim y -> x = y.
Admitted.

Lemma B2SF_Prim2B : forall x, B2SF (Prim2B x) = Prim2SF x.
Admitted.

Lemma Prim2SF_B2Prim : forall x, Prim2SF (B2Prim x) = B2SF x.
Admitted.

Local Instance Hprec : FLX.Prec_gt_0 prec := eq_refl _.

Local Instance Hmax : Prec_lt_emax prec emax := eq_refl _.

Theorem opp_equiv : forall x, Prim2B (- x) = Bopp (Prim2B x).
Admitted.

Theorem abs_equiv : forall x, Prim2B (abs x) = Babs (Prim2B x).
Admitted.

Theorem compare_equiv :
  forall x y,
  (x ?= y)%float = flatten_cmp_opt (Bcompare (Prim2B x) (Prim2B y)).
Admitted.

Lemma round_nearest_even_equiv s m l :
  round_nearest_even m l = choice_mode mode_NE s m l.
Admitted.

Lemma binary_round_aux_equiv sx mx ex lx :
  SpecFloat.binary_round_aux prec emax sx mx ex lx
  = binary_round_aux prec emax mode_NE sx mx ex lx.
Admitted.

Theorem mul_equiv :
  forall x y,
  Prim2B (x * y) = Bmult mode_NE (Prim2B x) (Prim2B y).
Admitted.

Lemma binary_round_equiv s m e :
  SpecFloat.binary_round prec emax s m e =
  binary_round prec emax mode_NE s m e.
Admitted.

Lemma binary_normalize_equiv m e szero :
  SpecFloat.binary_normalize prec emax m e szero
  = B2SF (binary_normalize prec emax Hprec Hmax mode_NE m e szero).
Admitted.

Theorem add_equiv :
  forall x y,
  Prim2B (x + y) = Bplus mode_NE (Prim2B x) (Prim2B y).
Admitted.

Theorem sub_equiv :
  forall x y,
  Prim2B (x - y) = Bminus mode_NE (Prim2B x) (Prim2B y).
Admitted.

Theorem div_equiv :
  forall x y,
  Prim2B (x / y) = Bdiv mode_NE (Prim2B x) (Prim2B y).
Admitted.

Theorem sqrt_equiv :
  forall x, Prim2B (sqrt x) = Bsqrt mode_NE (Prim2B x).
Admitted.

Theorem normfr_mantissa_equiv :
  forall x,
  to_Z (normfr_mantissa x) = Z.of_N (Bnormfr_mantissa (Prim2B x)).
Admitted.

Theorem ldexp_equiv :
  forall x e,
  Prim2B (Z.ldexp x e) = Bldexp mode_NE (Prim2B x) e.
Admitted.

Theorem ldshiftexp_equiv :
  forall x e,
  Prim2B (ldshiftexp x e) = Bldexp mode_NE (Prim2B x) (to_Z e - shift).
Admitted.

Theorem frexp_equiv :
  forall x : float,
  let (m, e) := Z.frexp x in
  (Prim2B m, e) = Bfrexp (Prim2B x).
Admitted.

Theorem frshiftexp_equiv :
  forall x : float,
  let (m, e) := frshiftexp x in
  (Prim2B m, (to_Z e - shift)%Z) = Bfrexp (Prim2B x).
Admitted.

Theorem infinity_equiv : infinity = B2Prim (B754_infinity false).
Admitted.

Theorem neg_infinity_equiv : neg_infinity = B2Prim (B754_infinity true).
Admitted.

Theorem nan_equiv : nan = B2Prim B754_nan.
Admitted.

Theorem zero_equiv : zero = B2Prim (B754_zero false).
Admitted.

Theorem neg_zero_equiv : neg_zero = B2Prim (B754_zero true).
Admitted.

Theorem one_equiv : one = B2Prim Bone.
Admitted.

Theorem two_equiv : two = B2Prim (Bplus mode_NE Bone Bone).
Admitted.

Theorem ulp_equiv :
  forall x, Prim2B (ulp x) = Bulp' (Prim2B x).
Admitted.

Theorem next_up_equiv :
  forall x, Prim2B (next_up x) = Bsucc (Prim2B x).
Admitted.

Theorem next_down_equiv :
  forall x, Prim2B (next_down x) = Bpred (Prim2B x).
Admitted.

Theorem is_nan_equiv :
  forall x, PrimFloat.is_nan x = is_nan (Prim2B x).
Admitted.

Theorem is_zero_equiv :
  forall x,
  is_zero x = match Prim2B x with B754_zero _ => true | _ => false end.
Admitted.

Theorem is_infinity_equiv :
  forall x,
  is_infinity x = match Prim2B x with B754_infinity _ => true | _ => false end.
Admitted.

Theorem get_sign_equiv : forall x, get_sign x = Bsign (Prim2B x).
Admitted.

Theorem is_finite_equiv :
  forall x, PrimFloat.is_finite x = is_finite (Prim2B x).
Admitted.

Theorem of_int63_equiv :
  forall i,
  Prim2B (of_uint63 i)
  = binary_normalize prec emax Hprec Hmax mode_NE (to_Z i) 0 false.
Admitted.

Theorem eqb_equiv :
  forall x y,
  eqb x y = Beqb (Prim2B x) (Prim2B y).
Admitted.

Theorem ltb_equiv :
  forall x y,
  ltb x y = Bltb (Prim2B x) (Prim2B y).
Admitted.

Theorem leb_equiv :
  forall x y,
  leb x y = Bleb (Prim2B x) (Prim2B y).
Admitted.

End Flocq_DOT_IEEE754_DOT_PrimFloat.

Module Export Flocq_DOT_Pff_DOT_Pff.
Module Export Flocq.
Module Export Pff.
Module Export Pff.

Export Stdlib.Reals.Reals.
Export Stdlib.ZArith.ZArith.
Export Stdlib.Lists.List.
Export Stdlib.Arith.PeanoNat.
Import Stdlib.micromega.Psatz.

Lemma Even_0 : Nat.Even 0.
Admitted.

Lemma Even_1 : ~ Nat.Even 1.
Admitted.

Lemma Odd_0 : ~ Nat.Odd 0.
Admitted.

Lemma Odd_1 : Nat.Odd 1.
Admitted.

Definition Even_Odd_double n :
  (Nat.Even n <-> n = Nat.double (Nat.div2 n)) /\ (Nat.Odd n <-> n = S (Nat.double (Nat.div2 n))).
Admitted.

Definition Even_double n : Nat.Even n -> n = Nat.double (Nat.div2 n).
Proof proj1 (proj1 (Even_Odd_double n)).

Definition Odd_double n : Nat.Odd n -> n = S (Nat.double (Nat.div2 n)).
Proof proj1 (proj2 (Even_Odd_double n)).

Definition Rinv_mult_distr := Rinv_mult_distr.
Definition Rabs_Rinv := Rabs_Rinv.
Definition Rinv_pow := Rinv_pow.
Definition Rinv_involutive := Rinv_involutive.
Definition Rlt_Rminus := Rlt_Rminus.
Definition powerRZ_inv := powerRZ_inv.
Definition powerRZ_neg := powerRZ_neg.

Definition IZR_neq := IZR_neq.

Global Set Asymmetric Patterns.

Ltac CaseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Ltac Casec name := case name; clear name.

Ltac Elimc name := elim name; clear name.

Theorem min_or :
 forall n m : nat, min n m = n /\ n <= m \/ min n m = m /\ m < n.
Admitted.

Theorem convert_not_O : forall p : positive, nat_of_P p <> 0.
Admitted.

Theorem inj_abs :
 forall x : Z, (0 <= x)%Z -> Z_of_nat (Z.abs_nat x) = x.
Admitted.

Theorem inject_nat_convert :
 forall (p : Z) (q : positive),
 p = Zpos q -> Z_of_nat (nat_of_P q) = p.
Admitted.

Theorem ZleLe : forall x y : nat, (Z_of_nat x <= Z_of_nat y)%Z -> x <= y.
Admitted.

Theorem Zlt_Zopp : forall x y : Z, (x < y)%Z -> (- y < - x)%Z.
Admitted.

Theorem Zle_Zopp : forall x y : Z, (x <= y)%Z -> (- y <= - x)%Z.
Admitted.

Theorem Zabs_absolu : forall z : Z, Z.abs z = Z_of_nat (Z.abs_nat z).
Admitted.

Theorem Zpower_nat_O : forall z : Z, Zpower_nat z 0 = Z_of_nat 1.
Admitted.

Theorem Zpower_nat_1 : forall z : Z, Zpower_nat z 1 = z.
Admitted.

Theorem Zmin_Zle :
 forall z1 z2 z3 : Z,
 (z1 <= z2)%Z -> (z1 <= z3)%Z -> (z1 <= Z.min z2 z3)%Z.
Admitted.

Theorem Zopp_Zpred_Zs : forall z : Z, (- Z.pred z)%Z = Z.succ (- z).
Admitted.

Definition Zmax : forall x_ x_ : Z, Z :=
  fun n m : Z =>
  match (n ?= m)%Z with
  | Datatypes.Eq => m
  | Datatypes.Lt => m
  | Datatypes.Gt => n
  end.

Theorem ZmaxLe1 : forall z1 z2 : Z, (z1 <= Zmax z1 z2)%Z.
Admitted.

Theorem ZmaxSym : forall z1 z2 : Z, Zmax z1 z2 = Zmax z2 z1.
Admitted.

Theorem ZmaxLe2 : forall z1 z2 : Z, (z2 <= Zmax z1 z2)%Z.
Admitted.

Theorem Zeq_Zs :
 forall p q : Z, (p <= q)%Z -> (q < Z.succ p)%Z -> p = q.
Admitted.

Theorem Zmin_Zmax : forall z1 z2 : Z, (Z.min z1 z2 <= Zmax z1 z2)%Z.
Admitted.

Theorem Zle_Zmult_comp_r :
 forall x y z : Z, (0 <= z)%Z -> (x <= y)%Z -> (x * z <= y * z)%Z.
Admitted.

Theorem Zle_Zmult_comp_l :
 forall x y z : Z, (0 <= z)%Z -> (x <= y)%Z -> (z * x <= z * y)%Z.
Admitted.

Theorem absolu_Zs :
 forall z : Z, (0 <= z)%Z -> Z.abs_nat (Z.succ z) = S (Z.abs_nat z).
Admitted.

Theorem Zlt_next :
 forall n m : Z, (n < m)%Z -> m = Z.succ n \/ (Z.succ n < m)%Z.
Admitted.

Theorem Zle_next :
 forall n m : Z, (n <= m)%Z -> m = n \/ (Z.succ n <= m)%Z.
Admitted.

Theorem inj_pred :
 forall n : nat, n <> 0 -> Z_of_nat (pred n) = Z.pred (Z_of_nat n).
Admitted.

Theorem Zle_abs : forall p : Z, (p <= Z_of_nat (Z.abs_nat p))%Z.
Admitted.

Theorem lt_Zlt_inv : forall n m : nat, (Z_of_nat n < Z_of_nat m)%Z -> n < m.
Admitted.

Theorem NconvertO : forall p : positive, nat_of_P p <> 0.
Admitted.

Theorem absolu_lt_nz : forall z : Z, z <> 0%Z -> 0 < Z.abs_nat z.
Admitted.

Theorem Rledouble : forall r : R, (0 <= r)%R -> (r <= 2 * r)%R.
Admitted.

Theorem Rltdouble : forall r : R, (0 < r)%R -> (r < 2 * r)%R.
Admitted.

Theorem Rle_Rinv : forall x y : R, (0 < x)%R -> (x <= y)%R -> (/ y <= / x)%R.
Admitted.

Theorem Zabs_eq_opp : forall x, (x <= 0)%Z -> Z.abs x = (- x)%Z.
Admitted.

Theorem Zabs_Zs : forall z : Z, (Z.abs (Z.succ z) <= Z.succ (Z.abs z))%Z.
Admitted.

Theorem Zle_Zpred : forall x y : Z, (x < y)%Z -> (x <= Z.pred y)%Z.
Admitted.

Theorem Zabs_Zopp : forall z : Z, Z.abs (- z) = Z.abs z.
Admitted.

Theorem Zle_Zabs : forall z : Z, (z <= Z.abs z)%Z.
Admitted.

Theorem Zlt_mult_simpl_l :
 forall a b c : Z, (0 < c)%Z -> (c * a < c * b)%Z -> (a < b)%Z.
Admitted.

Definition Z_eq_bool := Z.eqb.

Theorem Z_eq_bool_correct :
 forall p q : Z,
 match Z_eq_bool p q with
 | true => p = q
 | false => p <> q
 end.
Admitted.

Theorem Zle_Zpred_Zpred :
 forall z1 z2 : Z, (z1 <= z2)%Z -> (Z.pred z1 <= Z.pred z2)%Z.
Admitted.

Theorem Zlt_Zabs_inv1 :
 forall z1 z2 : Z, (Z.abs z1 < z2)%Z -> (- z2 < z1)%Z.
Admitted.

Theorem Zle_Zabs_inv1 :
 forall z1 z2 : Z, (Z.abs z1 <= z2)%Z -> (- z2 <= z1)%Z.
Admitted.

Theorem Zle_Zabs_inv2 :
 forall z1 z2 : Z, (Z.abs z1 <= z2)%Z -> (z1 <= z2)%Z.
Admitted.

Theorem Zlt_Zabs_Zpred :
 forall z1 z2 : Z,
 (Z.abs z1 < z2)%Z -> z1 <> Z.pred z2 -> (Z.abs (Z.succ z1) < z2)%Z.
Admitted.

Theorem Zle_n_Zpred :
 forall z1 z2 : Z, (Z.pred z1 <= Z.pred z2)%Z -> (z1 <= z2)%Z.
Admitted.

Theorem Zpred_Zopp_Zs : forall z : Z, Z.pred (- z) = (- Z.succ z)%Z.
Admitted.

Theorem Zlt_1_O : forall z : Z, (1 <= z)%Z -> (0 < z)%Z.
Admitted.

Theorem Zlt_not_eq_rev : forall p q : Z, (q < p)%Z -> p <> q.
Admitted.

Theorem Zle_Zpred_inv :
 forall z1 z2 : Z, (z1 <= Z.pred z2)%Z -> (z1 < z2)%Z.
Admitted.

Theorem Zabs_intro :
 forall (P : Z -> Prop) (z : Z), P (- z)%Z -> P z -> P (Z.abs z).
Admitted.

Theorem Zpred_Zle_Zabs_intro :
 forall z1 z2 : Z,
 (- Z.pred z2 <= z1)%Z -> (z1 <= Z.pred z2)%Z -> (Z.abs z1 < z2)%Z.
Admitted.

Theorem Zlt_Zabs_intro :
 forall z1 z2 : Z, (- z2 < z1)%Z -> (z1 < z2)%Z -> (Z.abs z1 < z2)%Z.
Admitted.

Section Pdigit.

Variable n : Z.

Hypothesis nMoreThan1 : (1 < n)%Z.

Let nMoreThanOne := Zlt_1_O _ (Zlt_le_weak _ _ nMoreThan1).

Theorem Zpower_nat_less : forall q : nat, (0 < Zpower_nat n q)%Z.
Proof using nMoreThanOne.
Admitted.

Theorem Zpower_nat_monotone_S :
 forall p : nat, (Zpower_nat n p < Zpower_nat n (S p))%Z.
Proof using nMoreThanOne.
Admitted.

Theorem Zpower_nat_monotone_lt :
 forall p q : nat, p < q -> (Zpower_nat n p < Zpower_nat n q)%Z.
Proof using nMoreThanOne.
Admitted.

Theorem Zpower_nat_anti_monotone_lt :
 forall p q : nat, (Zpower_nat n p < Zpower_nat n q)%Z -> p < q.
Proof using nMoreThanOne.
Admitted.

Theorem Zpower_nat_monotone_le :
 forall p q : nat, p <= q -> (Zpower_nat n p <= Zpower_nat n q)%Z.
Proof using nMoreThanOne.
Admitted.

Fixpoint digitAux (v r : Z) (q : positive) {struct q} : nat :=
  match q with
  | xH => 0
  | xI q' =>
      match (n * r)%Z with
      | r' =>
          match (r ?= v)%Z with
          | Datatypes.Gt => 0
          | _ => S (digitAux v r' q')
          end
      end
  | xO q' =>
      match (n * r)%Z with
      | r' =>
          match (r ?= v)%Z with
          | Datatypes.Gt => 0
          | _ => S (digitAux v r' q')
          end
      end
  end.

Definition digit (q : Z) :=
  match q with
  | Z0 => 0
  | Zpos q' => digitAux (Z.abs q) 1 (xO q')
  | Zneg q' => digitAux (Z.abs q) 1 (xO q')
  end.

Theorem digitAux1 :
 forall p r, (Zpower_nat n (S p) * r)%Z = (Zpower_nat n p * (n * r))%Z.
Proof using .
Admitted.

Theorem Zcompare_correct :
 forall p q : Z,
 match (p ?= q)%Z with
 | Datatypes.Gt => (q < p)%Z
 | Datatypes.Lt => (p < q)%Z
 | Datatypes.Eq => p = q
 end.
Proof using .
Admitted.

Theorem digitAuxLess :
 forall (v r : Z) (q : positive),
 match digitAux v r q with
 | S r' => (Zpower_nat n r' * r <= v)%Z
 | O => True
 end.
Proof using .
Admitted.

Theorem digitLess :
 forall q : Z, q <> 0%Z -> (Zpower_nat n (pred (digit q)) <= Z.abs q)%Z.
Proof using .
Admitted.

Fixpoint pos_length (p : positive) : nat :=
  match p with
  | xH => 0
  | xO p' => S (pos_length p')
  | xI p' => S (pos_length p')
  end.

Theorem digitAuxMore :
 forall (v r : Z) (q : positive),
 (0 < r)%Z ->
 (v < Zpower_nat n (pos_length q) * r)%Z ->
 (v < Zpower_nat n (digitAux v r q) * r)%Z.
Proof using nMoreThanOne.
Admitted.

Theorem pos_length_pow :
 forall p : positive, (Zpos p < Zpower_nat n (S (pos_length p)))%Z.
Proof using nMoreThan1.
Admitted.

Theorem digitMore : forall q : Z, (Z.abs q < Zpower_nat n (digit q))%Z.
Proof using nMoreThanOne.
Admitted.

Theorem digitInv :
 forall (q : Z) (r : nat),
 (Zpower_nat n (pred r) <= Z.abs q)%Z ->
 (Z.abs q < Zpower_nat n r)%Z -> digit q = r.
Proof using nMoreThanOne.
Admitted.

Theorem digit_monotone :
 forall p q : Z, (Z.abs p <= Z.abs q)%Z -> digit p <= digit q.
Proof using nMoreThanOne.
Admitted.

Theorem digitNotZero : forall q : Z, q <> 0%Z -> 0 < digit q.
Proof using nMoreThanOne.
Admitted.

Theorem digitAdd :
 forall (q : Z) (r : nat),
 q <> 0%Z -> digit (q * Zpower_nat n r) = digit q + r.
Proof using nMoreThanOne.
Admitted.

Theorem digit_abs : forall p : Z, digit (Z.abs p) = digit p.
Proof using .
Admitted.

Theorem digit_anti_monotone_lt :
 (1 < n)%Z -> forall p q : Z, digit p < digit q -> (Z.abs p < Z.abs q)%Z.
Proof using nMoreThanOne.
Admitted.
End Pdigit.

Theorem pow_NR0 : forall (e : R) (n : nat), e <> 0%R -> (e ^ n)%R <> 0%R.
Admitted.

Theorem pow_add :
 forall (e : R) (n m : nat), (e ^ (n + m))%R = (e ^ n * e ^ m)%R.
Admitted.

Theorem pow_RN_plus :
 forall (e : R) (n m : nat),
 e <> 0%R -> (e ^ n)%R = (e ^ (n + m) * / e ^ m)%R.
Admitted.

Theorem pow_lt : forall (e : R) (n : nat), (0 < e)%R -> (0 < e ^ n)%R.
Admitted.

Theorem Rlt_pow_R1 :
 forall (e : R) (n : nat), (1 < e)%R -> 0 < n -> (1 < e ^ n)%R.
Admitted.

Theorem Rlt_pow :
 forall (e : R) (n m : nat), (1 < e)%R -> n < m -> (e ^ n < e ^ m)%R.
Admitted.

Theorem pow_R1 :
 forall (r : R) (n : nat), (r ^ n)%R = 1%R -> Rabs r = 1%R \/ n = 0.
Admitted.

Theorem Zpower_NR0 :
 forall (e : Z) (n : nat), (0 <= e)%Z -> (0 <= Zpower_nat e n)%Z.
Admitted.

Theorem Zpower_NR1 :
 forall (e : Z) (n : nat), (1 <= e)%Z -> (1 <= Zpower_nat e n)%Z.
Admitted.

Theorem powerRZ_O : forall e : R, powerRZ e 0 = 1%R.
Admitted.

Theorem powerRZ_1 : forall e : R, powerRZ e (Z.succ 0) = e.
Admitted.

Theorem powerRZ_NOR : forall (e : R) (z : Z), e <> 0%R -> powerRZ e z <> 0%R.
Admitted.

Theorem powerRZ_add :
 forall (e : R) (n m : Z),
 e <> 0%R -> powerRZ e (n + m) = (powerRZ e n * powerRZ e m)%R.
Admitted.

Theorem powerRZ_Zopp :
 forall (e : R) (z : Z), e <> 0%R -> powerRZ e (- z) = (/ powerRZ e z)%R.
Admitted.

Theorem powerRZ_Zs :
 forall (e : R) (n : Z),
 e <> 0%R -> powerRZ e (Z.succ n) = (e * powerRZ e n)%R.
Admitted.

Theorem Zpower_nat_Z_powerRZ :
 forall (n : Z) (m : nat),
 IZR (Zpower_nat n m) = powerRZ (IZR n) (Z_of_nat m).
Admitted.

Theorem powerRZ_lt : forall (e : R) (z : Z), (0 < e)%R -> (0 < powerRZ e z)%R.
Admitted.

Theorem powerRZ_le :
 forall (e : R) (z : Z), (0 < e)%R -> (0 <= powerRZ e z)%R.
Admitted.

Theorem Rlt_powerRZ :
 forall (e : R) (n m : Z),
 (1 < e)%R -> (n < m)%Z -> (powerRZ e n < powerRZ e m)%R.
Admitted.

Theorem Zpower_nat_powerRZ_absolu :
 forall n m : Z,
 (0 <= m)%Z -> IZR (Zpower_nat n (Z.abs_nat m)) = powerRZ (IZR n) m.
Admitted.

Theorem powerRZ_R1 : forall n : Z, powerRZ 1 n = 1%R.
Admitted.

Theorem Rle_powerRZ :
 forall (e : R) (n m : Z),
 (1 <= e)%R -> (n <= m)%Z -> (powerRZ e n <= powerRZ e m)%R.
Admitted.

Theorem Zlt_powerRZ :
 forall (e : R) (n m : Z),
 (1 <= e)%R -> (powerRZ e n < powerRZ e m)%R -> (n < m)%Z.
Admitted.

Theorem Zle_powerRZ :
 forall (e : R) (n m : Z),
 (1 < e)%R -> (powerRZ e n <= powerRZ e m)%R -> (n <= m)%Z.
Admitted.

Theorem Rinv_powerRZ :
 forall (e : R) (n : Z), e <> 0%R -> (/ powerRZ e n)%R = powerRZ e (- n).
Admitted.

Section definitions.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Record float : Set := Float {Fnum : Z; Fexp : Z}.

Theorem floatEq :
 forall p q : float, Fnum p = Fnum q -> Fexp p = Fexp q -> p = q.
Proof using .
Admitted.

Theorem floatDec : forall x y : float, {x = y} + {x <> y}.
Proof using .
Admitted.

Definition Fzero (x : Z) := Float 0 x.

Definition is_Fzero (x : float) := Fnum x = 0%Z.

Coercion IZR : Z >-> R.
Coercion Z_of_nat : nat >-> Z.

Definition FtoR (x : float) := (Fnum x * powerRZ (IZR radix) (Fexp x))%R.

Local Coercion FtoR : float >-> R.

Theorem FzeroisReallyZero : forall z : Z, Fzero z = 0%R :>R.
Proof using .
Admitted.

Theorem is_Fzero_rep1 : forall x : float, is_Fzero x -> x = 0%R :>R.
Proof using .
Admitted.

Theorem LtFnumZERO : forall x : float, (0 < Fnum x)%Z -> (0 < x)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem is_Fzero_rep2 : forall x : float, x = 0%R :>R -> is_Fzero x.
Proof using radixMoreThanZERO.
Admitted.

Theorem NisFzeroComp :
 forall x y : float, ~ is_Fzero x -> x = y :>R -> ~ is_Fzero y.
Proof using radixMoreThanZERO.
Admitted.

Theorem Rlt_monotony_exp :
 forall (x y : R) (z : Z),
 (x < y)%R -> (x * powerRZ radix z < y * powerRZ radix z)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem Rle_monotone_exp :
 forall (x y : R) (z : Z),
 (x <= y)%R -> (x * powerRZ radix z <= y * powerRZ radix z)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem Rlt_monotony_contra_exp :
 forall (x y : R) (z : Z),
 (x * powerRZ radix z < y * powerRZ radix z)%R -> (x < y)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem Rle_monotony_contra_exp :
 forall (x y : R) (z : Z),
 (x * powerRZ radix z <= y * powerRZ radix z)%R -> (x <= y)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem FtoREqInv2 :
 forall p q : float, p = q :>R -> Fexp p = Fexp q -> p = q.
Proof using radixMoreThanZERO.
Admitted.

Theorem Rlt_Float_Zlt :
 forall p q r : Z, (Float p r < Float q r)%R -> (p < q)%Z.
Proof using radixMoreThanZERO.
Admitted.

Theorem oneExp_le :
 forall x y : Z, (x <= y)%Z -> (Float 1 x <= Float 1 y)%R.
Proof using radixMoreThanOne.
Admitted.

Theorem oneExp_Zlt :
 forall x y : Z, (Float 1 x < Float 1 y)%R -> (x < y)%Z.
Proof using radixMoreThanOne.
Admitted.

Definition Fdigit (p : float) := digit radix (Fnum p).

Definition Fshift (n : nat) (x : float) :=
  Float (Fnum x * Zpower_nat radix n) (Fexp x - n).

Theorem sameExpEq : forall p q : float, p = q :>R -> Fexp p = Fexp q -> p = q.
Proof using radixMoreThanZERO.
Admitted.

Theorem FshiftFdigit :
 forall (n : nat) (x : float),
 ~ is_Fzero x -> Fdigit (Fshift n x) = Fdigit x + n.
Proof using radixMoreThanOne.
Admitted.

Theorem FshiftCorrect : forall (n : nat) (x : float), Fshift n x = x :>R.
Proof using radixMoreThanZERO.
Admitted.

Theorem FshiftCorrectInv :
 forall x y : float,
 x = y :>R ->
 (Fexp x <= Fexp y)%Z -> Fshift (Z.abs_nat (Fexp y - Fexp x)) y = x.
Proof using radixMoreThanZERO.
Admitted.

Theorem FshiftO : forall x : float, Fshift 0 x = x.
Proof using .
Admitted.

Theorem FshiftCorrectSym :
 forall x y : float,
 x = y :>R -> exists n : nat, (exists m : nat, Fshift n x = Fshift m y).
Proof using radixMoreThanZERO.
Admitted.

Theorem FdigitEq :
 forall x y : float,
 ~ is_Fzero x -> x = y :>R -> Fdigit x = Fdigit y -> x = y.
Proof using radixMoreThanZERO.
Admitted.
End definitions.

Section comparisons.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Definition Fle (x y : float) := (x <= y)%R.

Lemma Fle_Zle :
 forall n1 n2 d : Z, (n1 <= n2)%Z -> Fle (Float n1 d) (Float n2 d).
Proof using radixMoreThanZERO.
Admitted.

Theorem Rlt_Fexp_eq_Zlt :
 forall x y : float, (x < y)%R -> Fexp x = Fexp y -> (Fnum x < Fnum y)%Z.
Proof using radixMoreThanOne.
Admitted.

Theorem Rle_Fexp_eq_Zle :
 forall x y : float, (x <= y)%R -> Fexp x = Fexp y -> (Fnum x <= Fnum y)%Z.
Proof using radixMoreThanOne.
Admitted.

Theorem LtR0Fnum : forall p : float, (0 < p)%R -> (0 < Fnum p)%Z.
Proof using radixMoreThanOne.
Admitted.

Theorem LeR0Fnum : forall p : float, (0 <= p)%R -> (0 <= Fnum p)%Z.
Proof using radixMoreThanOne.
Admitted.

Theorem LeFnumZERO : forall x : float, (0 <= Fnum x)%Z -> (0 <= x)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem R0LtFnum : forall p : float, (p < 0)%R -> (Fnum p < 0)%Z.
Proof using radixMoreThanOne.
Admitted.

Theorem R0LeFnum : forall p : float, (p <= 0)%R -> (Fnum p <= 0)%Z.
Proof using radixMoreThanOne.
Admitted.

Theorem LeZEROFnum : forall x : float, (Fnum x <= 0)%Z -> (x <= 0)%R.
Proof using radixMoreThanZERO.
Admitted.
End comparisons.

Section operations.
Variable radix : Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixNotZero : (0 < radix)%Z.

Definition Fplus (x y : float) :=
  Float
    (Fnum x * Zpower_nat radix (Z.abs_nat (Fexp x - Z.min (Fexp x) (Fexp y))) +
     Fnum y * Zpower_nat radix (Z.abs_nat (Fexp y - Z.min (Fexp x) (Fexp y))))
    (Z.min (Fexp x) (Fexp y)).

Theorem Fplus_correct : forall x y : float, Fplus x y = (x + y)%R :>R.
Proof using radixNotZero.
Admitted.

Definition Fopp (x : float) := Float (- Fnum x) (Fexp x).

Theorem Fopp_correct : forall x : float, Fopp x = (- x)%R :>R.
Proof using radix.
Admitted.

Theorem Fopp_Fopp : forall p : float, Fopp (Fopp p) = p.
Proof using .
Admitted.

Theorem Fdigit_opp : forall x : float, Fdigit radix (Fopp x) = Fdigit radix x.
Proof using .
Admitted.

Definition Fabs (x : float) := Float (Z.abs (Fnum x)) (Fexp x).

Theorem Fabs_correct1 :
 forall x : float, (0 <= FtoR radix x)%R -> Fabs x = x :>R.
Proof using radixNotZero.
Admitted.

Theorem Fabs_correct2 :
 forall x : float, (FtoR radix x <= 0)%R -> Fabs x = (- x)%R :>R.
Proof using radixNotZero.
Admitted.

Theorem Fabs_correct : forall x : float, Fabs x = Rabs x :>R.
Proof using radixNotZero.
Admitted.

Theorem RleFexpFabs :
 forall p : float, p <> 0%R :>R -> (Float 1 (Fexp p) <= Fabs p)%R.
Proof using radixNotZero.
Admitted.

Theorem Fabs_Fzero : forall x : float, ~ is_Fzero x -> ~ is_Fzero (Fabs x).
Proof using .
Admitted.

Theorem Fdigit_abs : forall x : float, Fdigit radix (Fabs x) = Fdigit radix x.
Proof using .
Admitted.

Definition Fminus (x y : float) := Fplus x (Fopp y).

Theorem Fminus_correct : forall x y : float, Fminus x y = (x - y)%R :>R.
Proof using radixNotZero.
Admitted.

Theorem Fopp_Fminus : forall p q : float, Fopp (Fminus p q) = Fminus q p.
Proof using .
Admitted.

Theorem Fopp_Fminus_dist :
 forall p q : float, Fopp (Fminus p q) = Fminus (Fopp p) (Fopp q).
Proof using .
Admitted.

Definition Fmult (x y : float) := Float (Fnum x * Fnum y) (Fexp x + Fexp y).

Definition Fmult_correct : forall x y : float, Fmult x y = (x * y)%R :>R.
Proof using radixNotZero.
Admitted.

End operations.

Section Fbounded_Def.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Coercion Z_of_N: N >-> Z.

Record Fbound : Set := Bound {vNum : positive; dExp : N}.

Definition Fbounded (b : Fbound) (d : float) :=
  (Z.abs (Fnum d) < Zpos (vNum b))%Z /\ (- dExp b <= Fexp d)%Z.

Theorem FzeroisZero : forall b : Fbound, Fzero (- dExp b) = 0%R :>R.
Proof using radix.
Admitted.

Theorem FboundedFzero : forall b : Fbound, Fbounded b (Fzero (- dExp b)).
Proof using .
Admitted.

Theorem FboundedZeroSameExp :
 forall (b : Fbound) (p : float), Fbounded b p -> Fbounded b (Fzero (Fexp p)).
Proof using .
Admitted.

Theorem FBoundedScale :
 forall (b : Fbound) (p : float) (n : nat),
 Fbounded b p -> Fbounded b (Float (Fnum p) (Fexp p + n)).
Proof using .
Admitted.

Theorem FvalScale :
 forall (b : Fbound) (p : float) (n : nat),
 Float (Fnum p) (Fexp p + n) = (powerRZ radix n * p)%R :>R.
Proof using radixMoreThanZERO.
Admitted.

Theorem oppBounded :
 forall (b : Fbound) (x : float), Fbounded b x -> Fbounded b (Fopp x).
Proof using .
Admitted.

Theorem oppBoundedInv :
 forall (b : Fbound) (x : float), Fbounded b (Fopp x) -> Fbounded b x.
Proof using .
Admitted.

Theorem absFBounded :
 forall (b : Fbound) (f : float), Fbounded b f -> Fbounded b (Fabs f).
Proof using .
Admitted.

Theorem FboundedEqExp :
 forall (b : Fbound) (p q : float),
 Fbounded b p -> p = q :>R -> (Fexp p <= Fexp q)%R -> Fbounded b q.
Proof using radixMoreThanZERO.
Admitted.

Theorem eqExpLess :
 forall (b : Fbound) (p q : float),
 Fbounded b p ->
 p = q :>R ->
 exists r : float, Fbounded b r /\ r = q :>R /\ (Fexp q <= Fexp r)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem FboundedShiftLess :
 forall (b : Fbound) (f : float) (n m : nat),
 m <= n -> Fbounded b (Fshift radix n f) -> Fbounded b (Fshift radix m f).
Proof using radixMoreThanOne.
Admitted.

Theorem eqExpMax :
 forall (b : Fbound) (p q : float),
 Fbounded b p ->
 Fbounded b q ->
 (Fabs p <= q)%R ->
 exists r : float, Fbounded b r /\ r = p :>R /\ (Fexp r <= Fexp q)%Z.
Proof using radixMoreThanZERO.
Admitted.

Theorem maxFbounded :
 forall (b : Fbound) (z : Z),
 (- dExp b <= z)%Z -> Fbounded b (Float (Z.pred (Zpos (vNum b))) z).
Proof using .
Admitted.

Theorem maxMax :
 forall (b : Fbound) (p : float) (z : Z),
 Fbounded b p ->
 (Fexp p <= z)%Z -> (Fabs p < Float (Zpos (vNum b)) z)%R.
Proof using radixMoreThanZERO.
Admitted.
End Fbounded_Def.

Section Fprop.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Variable b : Fbound.

Theorem SterbenzAux :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y ->
 (y <= x)%R -> (x <= 2 * y)%R -> Fbounded b (Fminus radix x y).
Proof using radixMoreThanOne.
Admitted.

Theorem Sterbenz :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y ->
 (/ 2 * y <= x)%R -> (x <= 2 * y)%R -> Fbounded b (Fminus radix x y).
Proof using radixMoreThanOne.
Admitted.

End Fprop.

Fixpoint mZlist_aux (p : Z) (n : nat) {struct n} :
 list Z :=
  match n with
  | O => p :: nil
  | S n1 => p :: mZlist_aux (Z.succ p) n1
  end.

Theorem mZlist_aux_correct :
 forall (n : nat) (p q : Z),
 (p <= q)%Z -> (q <= p + Z_of_nat n)%Z -> In q (mZlist_aux p n).
Admitted.

Theorem mZlist_aux_correct_rev1 :
 forall (n : nat) (p q : Z), In q (mZlist_aux p n) -> (p <= q)%Z.
Admitted.

Theorem mZlist_aux_correct_rev2 :
 forall (n : nat) (p q : Z),
 In q (mZlist_aux p n) -> (q <= p + Z_of_nat n)%Z.
Admitted.

Definition mZlist (p q : Z) : list Z :=
  match (q - p)%Z with
  | Z0 => p :: nil
  | Zpos d => mZlist_aux p (nat_of_P d)
  | Zneg _ => nil (A:=Z)
  end.

Theorem mZlist_correct :
 forall p q r : Z, (p <= r)%Z -> (r <= q)%Z -> In r (mZlist p q).
Admitted.

Theorem mZlist_correct_rev1 :
 forall p q r : Z, In r (mZlist p q) -> (p <= r)%Z.
Admitted.

Theorem mZlist_correct_rev2 :
 forall p q r : Z, In r (mZlist p q) -> (r <= q)%Z.
Admitted.

Fixpoint mProd (A B C : Set) (l1 : list A) (l2 : list B) {struct l2} :
 list (A * B) :=
  match l2 with
  | nil => nil
  | b :: l2' => map (fun a : A => (a, b)) l1 ++ mProd A B C l1 l2'
  end.

Theorem mProd_correct :
 forall (A B C : Set) (l1 : list A) (l2 : list B) (a : A) (b : B),
 In a l1 -> In b l2 -> In (a, b) (mProd A B C l1 l2).
Admitted.

Theorem mProd_correct_rev1 :
 forall (A B C : Set) (l1 : list A) (l2 : list B) (a : A) (b : B),
 In (a, b) (mProd A B C l1 l2) -> In a l1.
Admitted.

Theorem mProd_correct_rev2 :
 forall (A B C : Set) (l1 : list A) (l2 : list B) (a : A) (b : B),
 In (a, b) (mProd A B C l1 l2) -> In b l2.
Admitted.

Theorem in_map_inv :
 forall (A B : Set) (f : A -> B) (l : list A) (x : A),
 (forall a b : A, f a = f b -> a = b) -> In (f x) (map f l) -> In x l.
Admitted.

Section Fnormalized_Def.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Variable b : Fbound.

Definition Fnormal (p : float) :=
  Fbounded b p /\ (Zpos (vNum b) <= Z.abs (radix * Fnum p))%Z.

Theorem FnormalBounded : forall p : float, Fnormal p -> Fbounded b p.
Proof using .
Admitted.

Theorem FnormalNotZero : forall p : float, Fnormal p -> ~ is_Fzero p.
Proof using .
Admitted.

Theorem FnormalFop : forall p : float, Fnormal p -> Fnormal (Fopp p).
Proof using .
Admitted.

Theorem FnormalFabs : forall p : float, Fnormal p -> Fnormal (Fabs p).
Proof using radixMoreThanOne.
Admitted.

Definition pPred x := Z.pred (Zpos x).

Theorem maxMax1 :
 forall (p : float) (z : Z),
 Fbounded b p -> (Fexp p <= z)%Z -> (Fabs p <= Float (pPred (vNum b)) z)%R.
Proof using radixMoreThanOne.
Admitted.

Definition Fsubnormal (p : float) :=
  Fbounded b p /\
  Fexp p = (- dExp b)%Z /\ (Z.abs (radix * Fnum p) < Zpos (vNum b))%Z.

Theorem FsubnormalFbounded : forall p : float, Fsubnormal p -> Fbounded b p.
Proof using .
Admitted.

Theorem FsubnormalFexp :
 forall p : float, Fsubnormal p -> Fexp p = (- dExp b)%Z.
Proof using .
Admitted.

Theorem FsubnormFopp : forall p : float, Fsubnormal p -> Fsubnormal (Fopp p).
Proof using .
Admitted.

Theorem FsubnormFabs : forall p : float, Fsubnormal p -> Fsubnormal (Fabs p).
Proof using radixMoreThanOne.
Admitted.

Theorem FsubnormalUnique :
 forall p q : float, Fsubnormal p -> Fsubnormal q -> p = q :>R -> p = q.
Proof using radixMoreThanOne.
Admitted.

Theorem FsubnormalLt :
 forall p q : float,
 Fsubnormal p -> Fsubnormal q -> (p < q)%R -> (Fnum p < Fnum q)%Z.
Proof using radixMoreThanOne.
Admitted.

Definition Fcanonic (a : float) := Fnormal a \/ Fsubnormal a.

Theorem FcanonicBound : forall p : float, Fcanonic p -> Fbounded b p.
Proof using .
Admitted.

Theorem FcanonicFopp : forall p : float, Fcanonic p -> Fcanonic (Fopp p).
Proof using .
Admitted.

Theorem FcanonicFabs : forall p : float, Fcanonic p -> Fcanonic (Fabs p).
Proof using radixMoreThanOne.
Admitted.

Theorem MaxFloat :
 forall x : float,
 Fbounded b x -> (Rabs x < Float (Zpos (vNum b)) (Fexp x))%R.
Proof using radixMoreThanZERO.
Admitted.

Variable precision : nat.
Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem FboundNext :
 forall p : float,
 Fbounded b p ->
 exists q : float, Fbounded b q /\ q = Float (Z.succ (Fnum p)) (Fexp p) :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem digitPredVNumiSPrecision :
 digit radix (Z.pred (Zpos (vNum b))) = precision.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem digitVNumiSPrecision :
 digit radix (Zpos (vNum b)) = S precision.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem vNumPrecision :
 forall n : Z,
 digit radix n <= precision -> (Z.abs n < Zpos (vNum b))%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem pGivesDigit :
 forall p : float, Fbounded b p -> Fdigit radix p <= precision.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem digitGivesBoundedNum :
 forall p : float,
 Fdigit radix p <= precision -> (Z.abs (Fnum p) < Zpos (vNum b))%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FboundedMboundPos :
 forall z m : Z,
 (0 <= m)%Z ->
 (m <= Zpower_nat radix precision)%Z ->
 (- dExp b <= z)%Z ->
 exists c : float, Fbounded b c /\ c = (m * powerRZ radix z)%R :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FboundedMbound :
 forall z m : Z,
 (Z.abs m <= Zpower_nat radix precision)%Z ->
 (- dExp b <= z)%Z ->
 exists c : float, Fbounded b c /\ c = (m * powerRZ radix z)%R :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FnormalPrecision :
 forall p : float, Fnormal p -> Fdigit radix p = precision.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FnormalUnique :
 forall p q : float, Fnormal p -> Fnormal q -> p = q :>R -> p = q.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FnormalLtPos :
 forall p q : float,
 Fnormal p ->
 Fnormal q ->
 (0 <= p)%R ->
 (p < q)%R -> (Fexp p < Fexp q)%Z \/ Fexp p = Fexp q /\ (Fnum p < Fnum q)%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Definition nNormMin := Zpower_nat radix (pred precision).

Theorem nNormPos : (0 < nNormMin)%Z.
Proof using b precisionNotZero radixMoreThanOne.
Admitted.

Theorem digitnNormMin : digit radix nNormMin = precision.
Proof using b precisionNotZero radixMoreThanOne.
Admitted.

Theorem nNrMMimLevNum : (nNormMin <= Zpos (vNum b))%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Definition firstNormalPos := Float nNormMin (- dExp b).

Theorem firstNormalPosNormal : Fnormal firstNormalPos.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem pNormal_absolu_min :
 forall p : float, Fnormal p -> (nNormMin <= Z.abs (Fnum p))%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem maxMaxBis :
 forall (p : float) (z : Z),
 Fbounded b p -> (Fexp p < z)%Z -> (Fabs p < Float nNormMin z)%R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FnormalLtFirstNormalPos :
 forall p : float, Fnormal p -> (0 <= p)%R -> (firstNormalPos <= p)%R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FsubnormalDigit :
 forall p : float, Fsubnormal p -> Fdigit radix p < precision.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem pSubnormal_absolu_min :
 forall p : float, Fsubnormal p -> (Z.abs (Fnum p) < nNormMin)%Z.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FsubnormalLtFirstNormalPos :
 forall p : float, Fsubnormal p -> (0 <= p)%R -> (p < firstNormalPos)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FsubnormalnormalLtPos :
 forall p q : float,
 Fsubnormal p -> Fnormal q -> (0 <= p)%R -> (0 <= q)%R -> (p < q)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FsubnormalnormalLtNeg :
 forall p q : float,
 Fsubnormal p -> Fnormal q -> (p <= 0)%R -> (q <= 0)%R -> (q < p)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Definition Fnormalize (p : float) :=
  match Z_zerop (Fnum p) with
  | left _ => Float 0 (- dExp b)
  | right _ =>
      Fshift radix
        (min (precision - Fdigit radix p) (Z.abs_nat (dExp b + Fexp p))) p
  end.

Theorem FnormalizeCorrect : forall p : float, Fnormalize p = p :>R.
Proof using radixMoreThanOne.
Admitted.

Theorem Fnormalize_Fopp :
 forall p : float, Fnormalize (Fopp p) = Fopp (Fnormalize p).
Proof using precisionNotZero.
Admitted.

Theorem FnormalizeBounded :
 forall p : float, Fbounded b p -> Fbounded b (Fnormalize p).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FnormalizeCanonic :
 forall p : float, Fbounded b p -> Fcanonic (Fnormalize p).
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem NormalAndSubNormalNotEq :
 forall p q : float, Fnormal p -> Fsubnormal q -> p <> q :>R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FcanonicUnique :
 forall p q : float, Fcanonic p -> Fcanonic q -> p = q :>R -> p = q.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FcanonicLeastExp :
 forall x y : float,
 x = y :>R -> Fbounded b x -> Fcanonic y -> (Fexp y <= Fexp x)%Z.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FcanonicLtPos :
 forall p q : float,
 Fcanonic p ->
 Fcanonic q ->
 (0 <= p)%R ->
 (p < q)%R -> (Fexp p < Fexp q)%Z \/ Fexp p = Fexp q /\ (Fnum p < Fnum q)%Z.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem Fcanonic_Rle_Zle :
 forall x y : float,
 Fcanonic x -> Fcanonic y -> (Rabs x <= Rabs y)%R -> (Fexp x <= Fexp y)%Z.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FcanonicLtNeg :
 forall p q : float,
 Fcanonic p ->
 Fcanonic q ->
 (q <= 0)%R ->
 (p < q)%R -> (Fexp q < Fexp p)%Z \/ Fexp p = Fexp q /\ (Fnum p < Fnum q)%Z.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FcanonicFnormalizeEq :
 forall p : float, Fcanonic p -> Fnormalize p = p.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FcanonicPosFexpRlt :
 forall x y : float,
 (0 <= x)%R ->
 (0 <= y)%R -> Fcanonic x -> Fcanonic y -> (Fexp x < Fexp y)%Z -> (x < y)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FcanonicNegFexpRlt :
 forall x y : float,
 (x <= 0)%R ->
 (y <= 0)%R -> Fcanonic x -> Fcanonic y -> (Fexp x < Fexp y)%Z -> (y < x)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem vNumbMoreThanOne : (1 < Zpos (vNum b))%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem PosNormMin : Zpos (vNum b) = (radix * nNormMin)%Z.
Proof using pGivesBound precisionNotZero.
Admitted.

Theorem FnormalPpred :
 forall x : Z, (- dExp b <= x)%Z -> Fnormal (Float (pPred (vNum b)) x).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FcanonicPpred :
 forall x : Z,
 (- dExp b <= x)%Z -> Fcanonic (Float (pPred (vNum b)) x).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FnormalNnormMin :
 forall x : Z, (- dExp b <= x)%Z -> Fnormal (Float nNormMin x).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FcanonicNnormMin :
 forall x : Z, (- dExp b <= x)%Z -> Fcanonic (Float nNormMin x).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

End Fnormalized_Def.

Section suc.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition FSucc (x : float) :=
  match Z_eq_bool (Fnum x) (pPred (vNum b)) with
  | true => Float (nNormMin radix precision) (Z.succ (Fexp x))
  | false =>
      match Z_eq_bool (Fnum x) (- nNormMin radix precision) with
      | true =>
          match Z_eq_bool (Fexp x) (- dExp b) with
          | true => Float (Z.succ (Fnum x)) (Fexp x)
          | false => Float (- pPred (vNum b)) (Z.pred (Fexp x))
          end
      | false => Float (Z.succ (Fnum x)) (Fexp x)
      end
  end.

Theorem FSuccSimpl1 :
 forall x : float,
 Fnum x = pPred (vNum b) ->
 FSucc x = Float (nNormMin radix precision) (Z.succ (Fexp x)).
Proof using .
Admitted.

Theorem FSuccSimpl2 :
 forall x : float,
 Fnum x = (- nNormMin radix precision)%Z ->
 Fexp x <> (- dExp b)%Z ->
 FSucc x = Float (- pPred (vNum b)) (Z.pred (Fexp x)).
Proof using radixMoreThanOne.
Admitted.

Theorem FSuccSimpl3 :
 FSucc (Float (- nNormMin radix precision) (- dExp b)) =
 Float (Z.succ (- nNormMin radix precision)) (- dExp b).
Proof using radixMoreThanOne.
Admitted.

Theorem FSuccSimpl4 :
 forall x : float,
 Fnum x <> pPred (vNum b) ->
 Fnum x <> (- nNormMin radix precision)%Z ->
 FSucc x = Float (Z.succ (Fnum x)) (Fexp x).
Proof using .
Admitted.

Theorem FSuccDiff1 :
 forall x : float,
 Fnum x <> (- nNormMin radix precision)%Z ->
 Fminus radix (FSucc x) x = Float 1 (Fexp x) :>R.
Proof using pGivesBound precisionNotZero.
Admitted.

Theorem FSuccDiff2 :
 forall x : float,
 Fnum x = (- nNormMin radix precision)%Z ->
 Fexp x = (- dExp b)%Z -> Fminus radix (FSucc x) x = Float 1 (Fexp x) :>R.
Proof using radixMoreThanOne.
Admitted.

Theorem FSuccDiff3 :
 forall x : float,
 Fnum x = (- nNormMin radix precision)%Z ->
 Fexp x <> (- dExp b)%Z ->
 Fminus radix (FSucc x) x = Float 1 (Z.pred (Fexp x)) :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem ZltNormMinVnum : (nNormMin radix precision < Zpos (vNum b))%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FSuccNormPos :
 forall a : float,
 (0 <= a)%R -> Fnormal radix b a -> Fnormal radix b (FSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FSuccSubnormNotNearNormMin :
 forall a : float,
 Fsubnormal radix b a ->
 Fnum a <> Z.pred (nNormMin radix precision) -> Fsubnormal radix b (FSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FSuccSubnormNearNormMin :
 forall a : float,
 Fsubnormal radix b a ->
 Fnum a = Z.pred (nNormMin radix precision) -> Fnormal radix b (FSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FBoundedSuc : forall f : float, Fbounded b f -> Fbounded b (FSucc f).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FSuccSubnormal :
 forall a : float, Fsubnormal radix b a -> Fcanonic radix b (FSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FSuccPosNotMax :
 forall a : float,
 (0 <= a)%R -> Fcanonic radix b a -> Fcanonic radix b (FSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FSuccNormNegNotNormMin :
 forall a : float,
 (a <= 0)%R ->
 Fnormal radix b a ->
 a <> Float (- nNormMin radix precision) (- dExp b) ->
 Fnormal radix b (FSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FSuccNormNegNormMin :
 Fsubnormal radix b (FSucc (Float (- nNormMin radix precision) (- dExp b))).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FSuccNegCanonic :
 forall a : float,
 (a <= 0)%R -> Fcanonic radix b a -> Fcanonic radix b (FSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FSuccCanonic :
 forall a : float, Fcanonic radix b a -> Fcanonic radix b (FSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FSuccLt : forall a : float, (a < FSucc a)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FSuccPropPos :
 forall x y : float,
 (0 <= x)%R ->
 Fcanonic radix b x -> Fcanonic radix b y -> (x < y)%R -> (FSucc x <= y)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem R0RltRleSucc : forall x : float, (x < 0)%R -> (FSucc x <= 0)%R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FSuccPropNeg :
 forall x y : float,
 (x < 0)%R ->
 Fcanonic radix b x -> Fcanonic radix b y -> (x < y)%R -> (FSucc x <= y)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FSuccProp :
 forall x y : float,
 Fcanonic radix b x -> Fcanonic radix b y -> (x < y)%R -> (FSucc x <= y)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FSuccZleEq :
 forall p q : float,
 (p <= q)%R -> (q < FSucc p)%R -> (Fexp p <= Fexp q)%Z -> p = q :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Definition FNSucc x := FSucc (Fnormalize radix b precision x).

Theorem FNSuccCanonic :
 forall a : float, Fbounded b a -> Fcanonic radix b (FNSucc a).
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FNSuccLt : forall a : float, (a < FNSucc a)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

Theorem FNSuccProp :
 forall x y : float,
 Fbounded b x -> Fbounded b y -> (x < y)%R -> (FNSucc x <= y)%R.
Proof using pGivesBound precisionNotZero radixMoreThanZERO.
Admitted.

End suc.

Section suc1.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionNotZero : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem nNormMimLtvNum : (nNormMin radix precision < pPred (vNum b))%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

End suc1.

Section pred.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition FPred (x : float) :=
  match Z_eq_bool (Fnum x) (- pPred (vNum b)) with
  | true => Float (- nNormMin radix precision) (Z.succ (Fexp x))
  | false =>
      match Z_eq_bool (Fnum x) (nNormMin radix precision) with
      | true =>
          match Z_eq_bool (Fexp x) (- dExp b) with
          | true => Float (Z.pred (Fnum x)) (Fexp x)
          | false => Float (pPred (vNum b)) (Z.pred (Fexp x))
          end
      | false => Float (Z.pred (Fnum x)) (Fexp x)
      end
  end.

Theorem FPredSimpl1 :
 forall x : float,
 Fnum x = (- pPred (vNum b))%Z ->
 FPred x = Float (- nNormMin radix precision) (Z.succ (Fexp x)).
Proof using .
Admitted.

Theorem FPredSimpl2 :
 forall x : float,
 Fnum x = nNormMin radix precision ->
 Fexp x <> (- dExp b)%Z -> FPred x = Float (pPred (vNum b)) (Z.pred (Fexp x)).
Proof using precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredSimpl3 :
 FPred (Float (nNormMin radix precision) (- dExp b)) =
 Float (Z.pred (nNormMin radix precision)) (- dExp b).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredSimpl4 :
 forall x : float,
 Fnum x <> (- pPred (vNum b))%Z ->
 Fnum x <> nNormMin radix precision ->
 FPred x = Float (Z.pred (Fnum x)) (Fexp x).
Proof using .
Admitted.

Theorem FPredFopFSucc :
 forall x : float, FPred x = Fopp (FSucc b radix precision (Fopp x)).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredDiff1 :
 forall x : float,
 Fnum x <> nNormMin radix precision ->
 Fminus radix x (FPred x) = Float 1 (Fexp x) :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredDiff2 :
 forall x : float,
 Fnum x = nNormMin radix precision ->
 Fexp x = (- dExp b)%Z -> Fminus radix x (FPred x) = Float 1 (Fexp x) :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredDiff3 :
 forall x : float,
 Fnum x = nNormMin radix precision ->
 Fexp x <> (- dExp b)%Z ->
 Fminus radix x (FPred x) = Float 1 (Z.pred (Fexp x)) :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FBoundedPred : forall f : float, Fbounded b f -> Fbounded b (FPred f).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredCanonic :
 forall a : float, Fcanonic radix b a -> Fcanonic radix b (FPred a).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredLt : forall a : float, (FPred a < a)%R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem R0RltRlePred : forall x : float, (0 < x)%R -> (0 <= FPred x)%R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredProp :
 forall x y : float,
 Fcanonic radix b x -> Fcanonic radix b y -> (x < y)%R -> (x <= FPred y)%R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Definition FNPred (x : float) := FPred (Fnormalize radix b precision x).

Theorem FNPredFopFNSucc :
 forall x : float, FNPred x = Fopp (FNSucc b radix precision (Fopp x)).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FNPredCanonic :
 forall a : float, Fbounded b a -> Fcanonic radix b (FNPred a).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FNPredLt : forall a : float, (FNPred a < a)%R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FPredSuc :
 forall x : float,
 Fcanonic radix b x -> FPred (FSucc b radix precision x) = x.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FSucPred :
 forall x : float,
 Fcanonic radix b x -> FSucc b radix precision (FPred x) = x.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

End pred.

Section FMinMax.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition boundNat (n : nat) := Float 1 (digit radix n).

Theorem boundNatCorrect : forall n : nat, (n < boundNat n)%R.
Proof using radixMoreThanOne.
Admitted.

Definition boundR (r : R) := boundNat (Z.abs_nat (up (Rabs r))).

Theorem boundRCorrect1 : forall r : R, (r < boundR r)%R.
Proof using b precisionNotZero radixMoreThanOne.
Admitted.

Theorem boundRrOpp : forall r : R, boundR r = boundR (- r).
Proof using .
Admitted.

Theorem boundRCorrect2 : forall r : R, (Fopp (boundR r) < r)%R.
Proof using b precisionNotZero radixMoreThanOne.
Admitted.

Definition mBFloat (p : R) :=
  map (fun p : Z * Z => Float (fst p) (snd p))
    (mProd Z Z (Z * Z)
       (mZlist (- pPred (vNum b)) (pPred (vNum b)))
       (mZlist (- dExp b) (Fexp (boundR p)))).

Theorem mBFadic_correct1 :
 forall (r : R) (q : float),
 ~ is_Fzero q ->
 (Fopp (boundR r) < q)%R ->
 (q < boundR r)%R -> Fbounded b q -> In q (mBFloat r).
Proof using precisionNotZero radixMoreThanOne.
Admitted.

Theorem mBFadic_correct3 : forall r : R, In (Fopp (boundR r)) (mBFloat r).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem mBFadic_correct4 :
 forall r : R, In (Float 0 (- dExp b)) (mBFloat r).
Proof using precisionNotZero.
Admitted.

Theorem mBPadic_Fbounded :
 forall (p : float) (r : R), In p (mBFloat r) -> Fbounded b p.
Proof using .
Admitted.

Definition ProjectorP (P : R -> float -> Prop) :=
  forall p q : float, Fbounded b p -> P p q -> p = q :>R.

Definition MonotoneP (P : R -> float -> Prop) :=
  forall (p q : R) (p' q' : float),
  (p < q)%R -> P p p' -> P q q' -> (p' <= q')%R.

Definition isMin (r : R) (min : float) :=
  Fbounded b min /\
  (min <= r)%R /\
  (forall f : float, Fbounded b f -> (f <= r)%R -> (f <= min)%R).

Theorem isMin_inv1 : forall (p : float) (r : R), isMin r p -> (p <= r)%R.
Proof using .
Admitted.

Theorem ProjectMin : ProjectorP isMin.
Proof using .
Admitted.

Theorem MonotoneMin : MonotoneP isMin.
Proof using .
Admitted.

Definition isMax (r : R) (max : float) :=
  Fbounded b max /\
  (r <= max)%R /\
  (forall f : float, Fbounded b f -> (r <= f)%R -> (max <= f)%R).

Theorem isMax_inv1 : forall (p : float) (r : R), isMax r p -> (r <= p)%R.
Proof using .
Admitted.

Theorem ProjectMax : ProjectorP isMax.
Proof using .
Admitted.

Theorem MonotoneMax : MonotoneP isMax.
Proof using .
Admitted.

Theorem MinEq :
 forall (p q : float) (r : R), isMin r p -> isMin r q -> p = q :>R.
Proof using .
Admitted.

Theorem MaxEq :
 forall (p q : float) (r : R), isMax r p -> isMax r q -> p = q :>R.
Proof using .
Admitted.

Theorem MinOppMax :
 forall (p : float) (r : R), isMin r p -> isMax (- r) (Fopp p).
Proof using .
Admitted.

Theorem MaxOppMin :
 forall (p : float) (r : R), isMax r p -> isMin (- r) (Fopp p).
Proof using .
Admitted.

Theorem MinMax :
 forall (p : float) (r : R),
 isMin r p -> r <> p :>R -> isMax r (FNSucc b radix precision p).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem MinExList :
 forall (r : R) (L : list float),
 (forall f : float, In f L -> (r < f)%R) \/
 (exists min : float,
    In min L /\
    (min <= r)%R /\ (forall f : float, In f L -> (f <= r)%R -> (f <= min)%R)).
Proof using radix.
Admitted.

Theorem MinEx : forall r : R, exists min : float, isMin r min.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem MaxEx : forall r : R, exists max : float, isMax r max.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FminRep :
 forall p q : float,
 isMin p q -> exists m : Z, q = Float m (Fexp p) :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem MaxMin :
 forall (p : float) (r : R),
 isMax r p -> r <> p :>R -> isMin r (FNPred b radix precision p).
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FmaxRep :
 forall p q : float,
 isMax p q -> exists m : Z, q = Float m (Fexp p) :>R.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

End FMinMax.

Section FOdd.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition Even (z : Z) : Prop := exists z1 : _, z = (2 * z1)%Z.

Definition Odd (z : Z) : Prop := exists z1 : _, z = (2 * z1 + 1)%Z.

Theorem OddSEven : forall n : Z, Odd n -> Even (Z.succ n).
Proof using .
Admitted.

Theorem EvenSOdd : forall n : Z, Even n -> Odd (Z.succ n).
Proof using .
Admitted.

Theorem OddSEvenInv : forall n : Z, Odd (Z.succ n) -> Even n.
Proof using .
Admitted.

Theorem EvenSOddInv : forall n : Z, Even (Z.succ n) -> Odd n.
Proof using .
Admitted.

Theorem EvenO : Even 0.
Proof using .
Admitted.

Theorem Odd1 : Odd 1.
Proof using .
Admitted.

Theorem OddOpp : forall z : Z, Odd z -> Odd (- z).
Proof using .
Admitted.

Theorem EvenOpp : forall z : Z, Even z -> Even (- z).
Proof using .
Admitted.

Theorem OddEvenDec : forall n : Z, {Odd n} + {Even n}.
Proof using .
Admitted.

Theorem OddNEven : forall n : Z, Odd n -> ~ Even n.
Proof using .
Admitted.

Theorem EvenNOdd : forall n : Z, Even n -> ~ Odd n.
Proof using .
Admitted.

Theorem EvenPlus1 : forall n m : Z, Even n -> Even m -> Even (n + m).
Proof using .
Admitted.

Theorem OddPlus2 : forall n m : Z, Even n -> Odd m -> Odd (n + m).
Proof using .
Admitted.

Theorem EvenMult1 : forall n m : Z, Even n -> Even (n * m).
Proof using .
Admitted.

Theorem EvenMult2 : forall n m : Z, Even m -> Even (n * m).
Proof using .
Admitted.

Theorem OddMult : forall n m : Z, Odd n -> Odd m -> Odd (n * m).
Proof using .
Admitted.

Theorem EvenMultInv : forall n m : Z, Even (n * m) -> Odd n -> Even m.
Proof using .
Admitted.

Theorem EvenExp :
 forall (n : Z) (m : nat), Even n -> Even (Zpower_nat n (S m)).
Proof using .
Admitted.

Theorem OddExp :
 forall (n : Z) (m : nat), Odd n -> Odd (Zpower_nat n m).
Proof using .
Admitted.

Definition Feven (p : float) := Even (Fnum p).

Definition Fodd (p : float) := Odd (Fnum p).

Theorem FevenOrFodd : forall p : float, Feven p \/ Fodd p.
Proof using .
Admitted.

Theorem FevenSucProp :
 forall p : float,
 (Fodd p -> Feven (FSucc b radix precision p)) /\
 (Feven p -> Fodd (FSucc b radix precision p)).
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem FoddSuc :
 forall p : float, Fodd p -> Feven (FSucc b radix precision p).
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem FevenSuc :
 forall p : float, Feven p -> Fodd (FSucc b radix precision p).
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem FevenFop : forall p : float, Feven p -> Feven (Fopp p).
Proof using .
Admitted.

Definition FNodd (p : float) := Fodd (Fnormalize radix b precision p).

Definition FNeven (p : float) := Feven (Fnormalize radix b precision p).

Theorem FNoddEq :
 forall f1 f2 : float,
 Fbounded b f1 -> Fbounded b f2 -> f1 = f2 :>R -> FNodd f1 -> FNodd f2.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FNevenEq :
 forall f1 f2 : float,
 Fbounded b f1 -> Fbounded b f2 -> f1 = f2 :>R -> FNeven f1 -> FNeven f2.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FNevenFop : forall p : float, FNeven p -> FNeven (Fopp p).
Proof using precisionGreaterThanOne.
Admitted.

Theorem FNoddSuc :
 forall p : float,
 Fbounded b p -> FNodd p -> FNeven (FNSucc b radix precision p).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FNevenSuc :
 forall p : float,
 Fbounded b p -> FNeven p -> FNodd (FNSucc b radix precision p).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FNevenOrFNodd : forall p : float, FNeven p \/ FNodd p.
Proof using .
Admitted.

Theorem FnOddNEven : forall n : float, FNodd n -> ~ FNeven n.
Proof using .
Admitted.

End FOdd.

Section FRound.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition TotalP (P : R -> float -> Prop) :=
  forall r : R, exists p : float, P r p.

Definition UniqueP (P : R -> float -> Prop) :=
  forall (r : R) (p q : float), P r p -> P r q -> p = q :>R.

Definition CompatibleP (P : R -> float -> Prop) :=
  forall (r1 r2 : R) (p q : float),
  P r1 p -> r1 = r2 -> p = q :>R -> Fbounded b q -> P r2 q.

Definition MinOrMaxP (P : R -> float -> Prop) :=
  forall (r : R) (p : float), P r p -> isMin b radix r p \/ isMax b radix r p.

Definition RoundedModeP (P : R -> float -> Prop) :=
  TotalP P /\ CompatibleP P /\ MinOrMaxP P /\ MonotoneP radix P.

Theorem RoundedModeP_inv2 : forall P, RoundedModeP P -> CompatibleP P.
Proof using .
Admitted.

Theorem RoundedModeP_inv4 : forall P, RoundedModeP P -> MonotoneP radix P.
Proof using .
Admitted.

Theorem RoundedProjector : forall P, RoundedModeP P -> ProjectorP b radix P.
Proof using .
Admitted.

Theorem MinCompatible : CompatibleP (isMin b radix).
Proof using .
Admitted.

Theorem MinRoundedModeP : RoundedModeP (isMin b radix).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem MaxCompatible : CompatibleP (isMax b radix).
Proof using .
Admitted.

Theorem MaxRoundedModeP : RoundedModeP (isMax b radix).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem MinUniqueP : UniqueP (isMin b radix).
Proof using .
Admitted.

Theorem MaxUniqueP : UniqueP (isMax b radix).
Proof using .
Admitted.

Theorem MinOrMaxRep :
 forall P,
 MinOrMaxP P ->
 forall p q : float, P p q -> exists m : Z, q = Float m (Fexp p) :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RoundedModeRep :
 forall P,
 RoundedModeP P ->
 forall p q : float, P p q -> exists m : Z, q = Float m (Fexp p) :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Definition SymmetricP (P : R -> float -> Prop) :=
  forall (r : R) (p : float), P r p -> P (- r)%R (Fopp p).

End FRound.

Inductive Option (A : Set) : Set :=
  | Some : forall x : A, Option A
  | None : Option A.

Fixpoint Pdiv (p q : positive) {struct p} :
 Option positive * Option positive :=
  match p with
  | xH =>
      match q with
      | xH => (Some _ 1%positive, None _)
      | xO r => (None _, Some _ p)
      | xI r => (None _, Some _ p)
      end
  | xI p' =>
      match Pdiv p' q with
      | (None, None) =>
          match (1 - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ 1%positive)
          end
      | (None, Some r1) =>
          match (Zpos (xI r1) - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ (xI r1))
          end
      | (Some q1, None) =>
          match (1 - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ 1%positive)
          end
      | (Some q1, Some r1) =>
          match (Zpos (xI r1) - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ (xI r1))
          end
      end
  | xO p' =>
      match Pdiv p' q with
      | (None, None) => (None _, None _)
      | (None, Some r1) =>
          match (Zpos (xO r1) - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ (xO r1))
          end
      | (Some q1, None) => (Some _ (xO q1), None _)
      | (Some q1, Some r1) =>
          match (Zpos (xO r1) - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ (xO r1))
          end
      end
  end.

Definition oZ h := match h with
                   | None => 0
                   | Some p => nat_of_P p
                   end.

Theorem Pdiv_correct :
 forall p q,
 nat_of_P p =
 oZ (fst (Pdiv p q)) * nat_of_P q + oZ (snd (Pdiv p q)) /\
 oZ (snd (Pdiv p q)) < nat_of_P q.
Admitted.

Transparent Pdiv.

Definition oZ1 (x : Option positive) :=
  match x with
  | None => 0%Z
  | Some z => Zpos z
  end.

Definition Zquotient (n m : Z) :=
  match n, m with
  | Z0, _ => 0%Z
  | _, Z0 => 0%Z
  | Zpos x, Zpos y => match Pdiv x y with
                      | (x, _) => oZ1 x
                      end
  | Zneg x, Zneg y => match Pdiv x y with
                      | (x, _) => oZ1 x
                      end
  | Zpos x, Zneg y => match Pdiv x y with
                      | (x, _) => (- oZ1 x)%Z
                      end
  | Zneg x, Zpos y => match Pdiv x y with
                      | (x, _) => (- oZ1 x)%Z
                      end
  end.

Theorem inj_oZ1 : forall z, oZ1 z = Z_of_nat (oZ z).
Admitted.

Theorem ZquotientProp :
 forall m n : Z,
 n <> 0%Z ->
 ex
   (fun r : Z =>
    m = (Zquotient m n * n + r)%Z /\
    (Z.abs (Zquotient m n * n) <= Z.abs m)%Z /\ (Z.abs r < Z.abs n)%Z).
Admitted.

Theorem ZquotientPos :
 forall z1 z2 : Z, (0 <= z1)%Z -> (0 <= z2)%Z -> (0 <= Zquotient z1 z2)%Z.
Admitted.

Definition Zdivides (n m : Z) := exists q : Z, n = (m * q)%Z.

Theorem ZdividesZquotient :
 forall n m : Z, m <> 0%Z -> Zdivides n m -> n = (Zquotient n m * m)%Z.
Admitted.

Theorem ZdividesZquotientInv :
 forall n m : Z, n = (Zquotient n m * m)%Z -> Zdivides n m.
Admitted.

Theorem ZdividesMult :
 forall n m p : Z, Zdivides n m -> Zdivides (p * n) (p * m).
Admitted.

Theorem Zeq_mult_simpl :
 forall a b c : Z, c <> 0%Z -> (a * c)%Z = (b * c)%Z -> a = b.
Admitted.

Theorem ZdividesDiv :
 forall n m p : Z, p <> 0%Z -> Zdivides (p * n) (p * m) -> Zdivides n m.
Admitted.

Definition ZdividesP : forall n m : Z, {Zdivides n m} + {~ Zdivides n m}.
intros n m; case m.
case n.
left; red in |- *; exists 0%Z; auto with zarith.
intros p; right; red in |- *; intros H; case H; simpl in |- *; intros f H1;
 discriminate.
intros p; right; red in |- *; intros H; case H; simpl in |- *; intros f H1;
 discriminate.
intros p; generalize (Z_eq_bool_correct (Zquotient n (Zpos p) * Zpos p) n);
 case (Z_eq_bool (Zquotient n (Zpos p) * Zpos p) n);
 intros H1.
left; apply ZdividesZquotientInv; auto.
right; contradict H1; apply sym_equal; apply ZdividesZquotient; auto.
red in |- *; intros; discriminate.
intros p; generalize (Z_eq_bool_correct (Zquotient n (Zneg p) * Zneg p) n);
 case (Z_eq_bool (Zquotient n (Zneg p) * Zneg p) n);
 intros H1.
left; apply ZdividesZquotientInv; auto.
right; contradict H1; apply sym_equal; apply ZdividesZquotient; auto.
red in |- *; intros; discriminate.
Defined.

Theorem Zdivides1 : forall m : Z, Zdivides m 1.
Admitted.

Theorem NotDividesDigit :
 forall r v : Z,
 (1 < r)%Z -> v <> 0%Z -> ~ Zdivides v (Zpower_nat r (digit r v)).
Admitted.

Theorem ZDividesLe :
 forall n m : Z, n <> 0%Z -> Zdivides n m -> (Z.abs m <= Z.abs n)%Z.
Admitted.

Section mf.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Fixpoint maxDiv (v : Z) (p : nat) {struct p} : nat :=
  match p with
  | O => 0
  | S p' =>
      match ZdividesP v (Zpower_nat radix p) with
      | left _ => p
      | right _ => maxDiv v p'
      end
  end.

Theorem maxDivLess : forall (v : Z) (p : nat), maxDiv v p <= p.
Proof using .
Admitted.

Theorem maxDivLt :
 forall (v : Z) (p : nat),
 ~ Zdivides v (Zpower_nat radix p) -> maxDiv v p < p.
Proof using .
Admitted.

Theorem maxDivCorrect :
 forall (v : Z) (p : nat), Zdivides v (Zpower_nat radix (maxDiv v p)).
Proof using .
Admitted.

Theorem maxDivSimplAux :
 forall (v : Z) (p q : nat),
 p = maxDiv v (S (q + p)) -> p = maxDiv v (S p).
Proof using .
Admitted.

Theorem maxDivSimpl :
 forall (v : Z) (p q : nat),
 p < q -> p = maxDiv v q -> p = maxDiv v (S p).
Proof using .
Admitted.

Theorem maxDivSimplInvAux :
 forall (v : Z) (p q : nat),
 p = maxDiv v (S p) -> p = maxDiv v (S (q + p)).
Proof using .
Admitted.

Theorem maxDivSimplInv :
 forall (v : Z) (p q : nat),
 p < q -> p = maxDiv v (S p) -> p = maxDiv v q.
Proof using .
Admitted.

Theorem maxDivUnique :
 forall (v : Z) (p : nat),
 p = maxDiv v (S p) ->
 Zdivides v (Zpower_nat radix p) /\ ~ Zdivides v (Zpower_nat radix (S p)).
Proof using .
Admitted.

Theorem maxDivUniqueDigit :
 forall v : Z,
 v <> 0 ->
 Zdivides v (Zpower_nat radix (maxDiv v (digit radix v))) /\
 ~ Zdivides v (Zpower_nat radix (S (maxDiv v (digit radix v)))).
Proof using radixMoreThanOne.
Admitted.

Theorem maxDivUniqueInverse :
 forall (v : Z) (p : nat),
 Zdivides v (Zpower_nat radix p) ->
 ~ Zdivides v (Zpower_nat radix (S p)) -> p = maxDiv v (S p).
Proof using .
Admitted.

Theorem maxDivUniqueInverseDigit :
 forall (v : Z) (p : nat),
 v <> 0 ->
 Zdivides v (Zpower_nat radix p) ->
 ~ Zdivides v (Zpower_nat radix (S p)) -> p = maxDiv v (digit radix v).
Proof using radixMoreThanOne.
Admitted.

Theorem maxDivPlus :
 forall (v : Z) (n : nat),
 v <> 0 ->
 maxDiv (v * Zpower_nat radix n) (digit radix v + n) =
 maxDiv v (digit radix v) + n.
Proof using radixMoreThanOne.
Admitted.

Definition LSB (x : float) :=
  (Z_of_nat (maxDiv (Fnum x) (Fdigit radix x)) + Fexp x)%Z.

Theorem LSB_shift :
 forall (x : float) (n : nat), ~ is_Fzero x -> LSB x = LSB (Fshift radix n x).
Proof using radixMoreThanOne.
Admitted.

Theorem LSB_comp :
 forall (x y : float) (n : nat), ~ is_Fzero x -> x = y :>R -> LSB x = LSB y.
Proof using radixMoreThanOne.
Admitted.

Theorem maxDiv_opp :
 forall (v : Z) (p : nat), maxDiv v p = maxDiv (- v) p.
Proof using .
Admitted.

Theorem LSB_opp : forall x : float, LSB x = LSB (Fopp x).
Proof using .
Admitted.

Theorem maxDiv_abs :
 forall (v : Z) (p : nat), maxDiv v p = maxDiv (Z.abs v) p.
Proof using radixMoreThanOne.
Admitted.

Theorem LSB_abs : forall x : float, LSB x = LSB (Fabs x).
Proof using radixMoreThanOne.
Admitted.

Definition MSB (x : float) := Z.pred (Z_of_nat (Fdigit radix x) + Fexp x).

Theorem MSB_shift :
 forall (x : float) (n : nat), ~ is_Fzero x -> MSB x = MSB (Fshift radix n x).
Proof using radixMoreThanOne.
Admitted.

Theorem MSB_comp :
 forall (x y : float) (n : nat), ~ is_Fzero x -> x = y :>R -> MSB x = MSB y.
Proof using radixMoreThanOne.
Admitted.

Theorem MSB_opp : forall x : float, MSB x = MSB (Fopp x).
Proof using .
Admitted.

Theorem MSB_abs : forall x : float, MSB x = MSB (Fabs x).
Proof using .
Admitted.

Theorem LSB_le_MSB : forall x : float, ~ is_Fzero x -> (LSB x <= MSB x)%Z.
Proof using radixMoreThanOne.
Admitted.

Theorem Fexp_le_LSB : forall x : float, (Fexp x <= LSB x)%Z.
Proof using .
Admitted.

Theorem Ulp_Le_LSigB :
 forall x : float, (Float 1 (Fexp x) <= Float 1 (LSB x))%R.
Proof using radixMoreThanOne.
Admitted.

Theorem MSB_le_abs :
 forall x : float, ~ is_Fzero x -> (Float 1 (MSB x) <= Fabs x)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem abs_lt_MSB :
 forall x : float, (Fabs x < Float 1 (Z.succ (MSB x)))%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem LSB_le_abs :
 forall x : float, ~ is_Fzero x -> (Float 1 (LSB x) <= Fabs x)%R.
Proof using radixMoreThanZERO.
Admitted.

Theorem MSB_monotoneAux :
 forall x y : float,
 (Fabs x <= Fabs y)%R -> Fexp x = Fexp y -> (MSB x <= MSB y)%Z.
Proof using radixMoreThanOne.
Admitted.

Theorem MSB_monotone :
 forall x y : float,
 ~ is_Fzero x -> ~ is_Fzero y -> (Fabs x <= Fabs y)%R -> (MSB x <= MSB y)%Z.
Proof using radixMoreThanZERO.
Admitted.

Theorem LSB_rep_min :
 forall p : float, exists z : Z, p = Float z (LSB p) :>R.
Proof using radixMoreThanOne.
Admitted.
End mf.

Section FRoundP.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition Fulp (p : float) :=
  powerRZ radix (Fexp (Fnormalize radix b precision p)).

Theorem FulpComp :
 forall p q : float,
 Fbounded b p -> Fbounded b q -> p = q :>R -> Fulp p = Fulp q.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FulpLe :
 forall p : float, Fbounded b p -> (Fulp p <= Float 1 (Fexp p))%R.
Proof using precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem Fulp_zero :
 forall x : float, is_Fzero x -> Fulp x = powerRZ radix (- dExp b).
Proof using .
Admitted.

Theorem FulpLe2 :
 forall p : float,
 Fbounded b p ->
 Fnormal radix b (Fnormalize radix b precision p) ->
 (Fulp p <= Rabs p * powerRZ radix (Z.succ (- precision)))%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem FulpGe :
 forall p : float,
 Fbounded b p -> (Rabs p <= (powerRZ radix precision - 1) * Fulp p)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem LeFulpPos :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y -> (0 <= x)%R -> (x <= y)%R -> (Fulp x <= Fulp y)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FulpSucCan :
 forall p : float,
 Fcanonic radix b p -> (FSucc b radix precision p - p <= Fulp p)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem FulpSuc :
 forall p : float,
 Fbounded b p -> (FNSucc b radix precision p - p <= Fulp p)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem FulpPredCan :
 forall p : float,
 Fcanonic radix b p -> (p - FPred b radix precision p <= Fulp p)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem FulpPred :
 forall p : float,
 Fbounded b p -> (p - FNPred b radix precision p <= Fulp p)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem FSuccDiffPos :
 forall x : float,
 (0 <= x)%R ->
 Fminus radix (FSucc b radix precision x) x = Float 1 (Fexp x) :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FulpFPredGePos :
 forall f : float,
 Fbounded b f ->
 Fcanonic radix b f ->
 (0 < f)%R -> (Fulp (FPred b radix precision f) <= Fulp f)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem CanonicFulp :
 forall p : float, Fcanonic radix b p -> Fulp p = Float 1 (Fexp p).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FSuccUlpPos :
 forall x : float,
 Fcanonic radix b x ->
 (0 <= x)%R -> Fminus radix (FSucc b radix precision x) x = Fulp x :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FulpFabs : forall f : float, Fulp f = Fulp (Fabs f) :>R.
Proof using precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RoundedModeUlp :
 forall P,
 RoundedModeP b radix P ->
 forall (p : R) (q : float), P p q -> (Rabs (p - q) < Fulp q)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem RoundedModeErrorExpStrict :
 forall P,
 RoundedModeP b radix P ->
 forall (p q : float) (x : R),
 Fbounded b p ->
 Fbounded b q ->
 P x p -> q = (x - p)%R :>R -> q <> 0%R :>R -> (Fexp q < Fexp p)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem RoundedModeProjectorIdem :
 forall P (p : float), RoundedModeP b radix P -> Fbounded b p -> P p p.
Proof using .
Admitted.

Theorem RoundedModeBounded :
 forall P (r : R) (q : float),
 RoundedModeP b radix P -> P r q -> Fbounded b q.
Proof using .
Admitted.

Theorem RoundedModeProjectorIdemEq :
 forall (P : R -> float -> Prop) (p q : float),
 RoundedModeP b radix P -> Fbounded b p -> P (FtoR radix p) q -> p = q :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RoundedModeMult :
 forall P,
 RoundedModeP b radix P ->
 forall (r : R) (q q' : float),
 P r q -> Fbounded b q' -> (r <= radix * q')%R -> (q <= radix * q')%R.
Proof using radixMoreThanOne.
Admitted.

Theorem RoundedModeMultLess :
 forall P,
 RoundedModeP b radix P ->
 forall (r : R) (q q' : float),
 P r q -> Fbounded b q' -> (radix * q' <= r)%R -> (radix * q' <= q)%R.
Proof using radixMoreThanOne.
Admitted.

Theorem RleMinR0 :
 forall (r : R) (min : float),
 (0 <= r)%R -> isMin b radix r min -> (0 <= min)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RleRoundedR0 :
 forall (P : R -> float -> Prop) (p : float) (r : R),
 RoundedModeP b radix P -> P r p -> (0 <= r)%R -> (0 <= p)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RleMaxR0 :
 forall (r : R) (max : float),
 (r <= 0)%R -> isMax b radix r max -> (max <= 0)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RleRoundedLessR0 :
 forall (P : R -> float -> Prop) (p : float) (r : R),
 RoundedModeP b radix P -> P r p -> (r <= 0)%R -> (p <= 0)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem PminPos :
 forall p min : float,
 (0 <= p)%R ->
 Fbounded b p ->
 isMin b radix (/ 2 * p) min ->
 exists c : float, Fbounded b c /\ c = (p - min)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem div2IsBetweenPos :
 forall p min max : float,
 (0 <= p)%R ->
 Fbounded b p ->
 isMin b radix (/ 2 * p) min ->
 isMax b radix (/ 2 * p) max -> p = (min + max)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem div2IsBetween :
 forall p min max : float,
 Fbounded b p ->
 isMin b radix (/ 2 * p) min ->
 isMax b radix (/ 2 * p) max -> p = (min + max)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem RoundedModeMultAbs :
 forall P,
 RoundedModeP b radix P ->
 forall (r : R) (q q' : float),
 P r q ->
 Fbounded b q' -> (Rabs r <= radix * q')%R -> (Rabs q <= radix * q')%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem isMinComp :
 forall (r1 r2 : R) (min max : float),
 isMin b radix r1 min ->
 isMax b radix r1 max -> (min < r2)%R -> (r2 < max)%R -> isMin b radix r2 min.
Proof using .
Admitted.

Theorem isMaxComp :
 forall (r1 r2 : R) (min max : float),
 isMin b radix r1 min ->
 isMax b radix r1 max -> (min < r2)%R -> (r2 < max)%R -> isMax b radix r2 max.
Proof using .
Admitted.

Theorem RleBoundRoundl :
 forall P,
 RoundedModeP b radix P ->
 forall (p q : float) (r : R),
 Fbounded b p -> (p <= r)%R -> P r q -> (p <= q)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RleBoundRoundr :
 forall P,
 RoundedModeP b radix P ->
 forall (p q : float) (r : R),
 Fbounded b p -> (r <= p)%R -> P r q -> (q <= p)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RoundAbsMonotoner :
 forall (P : R -> float -> Prop) (p : R) (q r : float),
 RoundedModeP b radix P ->
 Fbounded b r -> P p q -> (Rabs p <= r)%R -> (Rabs q <= r)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RoundAbsMonotonel :
 forall (P : R -> float -> Prop) (p : R) (q r : float),
 RoundedModeP b radix P ->
 Fbounded b r -> P p q -> (r <= Rabs p)%R -> (r <= Rabs q)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem FUlp_Le_LSigB :
 forall x : float, Fbounded b x -> (Fulp x <= Float 1 (LSB radix x))%R.
Proof using precisionGreaterThanOne radixMoreThanOne.
Admitted.

End FRoundP.

Section FRoundPP.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem errorBoundedMultMin :
 forall p q fmin : float,
 Fbounded b p ->
 Fbounded b q ->
 (0 <= p)%R ->
 (0 <= q)%R ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 isMin b radix (p * q) fmin ->
 exists r : float,
   r = (p * q - fmin)%R :>R /\ Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedMultMax :
 forall p q fmax : float,
 Fbounded b p ->
 Fbounded b q ->
 (0 <= p)%R ->
 (0 <= q)%R ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 isMax b radix (p * q) fmax ->
 exists r : float,
   FtoRradix r = (p * q - fmax)%R /\
   Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem multExpUpperBound :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p * q)%R pq ->
 Fbounded b p ->
 Fbounded b q ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 exists r : float,
   Fbounded b r /\ r = pq :>R /\ (Fexp r <= precision + (Fexp p + Fexp q))%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedMultPos :
 forall P,
 RoundedModeP b radix P ->
 forall p q f : float,
 Fbounded b p ->
 Fbounded b q ->
 (0 <= p)%R ->
 (0 <= q)%R ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 P (p * q)%R f ->
 exists r : float,
   r = (p * q - f)%R :>R /\ Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedMultNeg :
 forall P,
 RoundedModeP b radix P ->
 forall p q f : float,
 Fbounded b p ->
 Fbounded b q ->
 (p <= 0)%R ->
 (0 <= q)%R ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 P (p * q)%R f ->
 exists r : float,
   r = (p * q - f)%R :>R /\ Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedMult :
 forall P,
 RoundedModeP b radix P ->
 forall p q f : float,
 Fbounded b p ->
 Fbounded b q ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 P (p * q)%R f ->
 exists r : float,
   r = (p * q - f)%R :>R /\ Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedMultExp_aux :
 forall n1 n2 : Z,
 (Z.abs n1 < Zpos (vNum b))%Z ->
 (Z.abs n2 < Zpos (vNum b))%Z ->
 (exists ny : Z,
    (exists ey : Z,
       (n1 * n2)%R = (ny * powerRZ radix ey)%R :>R /\
       (Z.abs ny < Zpos (vNum b))%Z)) ->
 exists nx : Z,
   (exists ex : Z,
      (n1 * n2)%R = (nx * powerRZ radix ex)%R :>R /\
      (Z.abs nx < Zpos (vNum b))%Z /\
      (0 <= ex)%Z /\ (ex <= precision)%Z).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedMultExpPos :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 (0 <= p)%R ->
 (0 <= q)%R ->
 P (p * q)%R pq ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fbounded b r /\
       Fbounded b s /\
       r = pq :>R /\
       s = (p * q - r)%R :>R /\
       Fexp s = (Fexp p + Fexp q)%Z :>Z /\
       (Fexp s <= Fexp r)%Z /\ (Fexp r <= precision + (Fexp p + Fexp q))%Z)).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedMultExp :
 forall P, (RoundedModeP b radix P) ->
 forall p q pq : float,
  (Fbounded b p) -> (Fbounded b q) ->
  (P (p * q)%R pq) ->
   (-(dExp b) <= Fexp p + Fexp q)%Z ->
   exists r : float,
   exists s : float,
      (Fbounded b r) /\ (Fbounded b s) /\
       r = pq :>R /\ s = (p * q - r)%R :>R /\
       (Fexp s =  Fexp p + Fexp q)%Z /\
       (Fexp s <= Fexp r)%Z /\
       (Fexp r <= precision + (Fexp p + Fexp q))%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

End FRoundPP.

Section Fclosest.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition Closest (r : R) (p : float) :=
  Fbounded b p /\
  (forall f : float, Fbounded b f -> (Rabs (p - r) <= Rabs (f - r))%R).

Theorem ClosestTotal : TotalP Closest.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ClosestCompatible : CompatibleP b radix Closest.
Proof using .
Admitted.

Theorem ClosestMin :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max -> (2 * r <= min + max)%R -> Closest r min.
Proof using .
Admitted.

Theorem ClosestMax :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max -> (min + max <= 2 * r)%R -> Closest r max.
Proof using .
Admitted.

Theorem ClosestMinOrMax : MinOrMaxP b radix Closest.
Proof using .
Admitted.

Theorem ClosestMinEq :
 forall (r : R) (min max p : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (2 * r < min + max)%R -> Closest r p -> p = min :>R.
Proof using .
Admitted.

Theorem ClosestMaxEq :
 forall (r : R) (min max p : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (min + max < 2 * r)%R -> Closest r p -> p = max :>R.
Proof using .
Admitted.

Theorem ClosestMonotone : MonotoneP radix Closest.
Proof using .
Admitted.

Theorem ClosestRoundedModeP : RoundedModeP b radix Closest.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Definition EvenClosest (r : R) (p : float) :=
  Closest r p /\
  (FNeven b radix precision p \/ (forall q : float, Closest r q -> q = p :>R)).

Theorem EvenClosestTotal : TotalP EvenClosest.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem EvenClosestCompatible : CompatibleP b radix EvenClosest.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem EvenClosestMinOrMax : MinOrMaxP b radix EvenClosest.
Proof using .
Admitted.

Theorem EvenClosestMonotone : MonotoneP radix EvenClosest.
Proof using .
Admitted.

Theorem EvenClosestRoundedModeP : RoundedModeP b radix EvenClosest.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem EvenClosestUniqueP : UniqueP radix EvenClosest.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ClosestSymmetric : SymmetricP Closest.
Proof using .
Admitted.

Theorem EvenClosestSymmetric : SymmetricP EvenClosest.
Proof using precisionGreaterThanOne.
Admitted.
End Fclosest.

Section Fclosestp2.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem ClosestOpp :
 forall (p : float) (r : R),
 Closest b radix r p -> Closest b radix (- r) (Fopp p).
Proof using .
Admitted.

Theorem ClosestFabs :
 forall (p : float) (r : R),
 Closest b radix r p -> Closest b radix (Rabs r) (Fabs p).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ClosestUlp :
 forall (p : R) (q : float),
 Closest b radix p q -> (2 * Rabs (p - q) <= Fulp b radix precision q)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ClosestExp :
 forall (p : R) (q : float),
 Closest b radix p q -> (2 * Rabs (p - q) <= powerRZ radix (Fexp q))%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ClosestErrorExpStrict :
 forall (p q : float) (x : R),
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix x p ->
 q = (x - p)%R :>R -> q <> 0%R :>R -> (Fexp q < Fexp p)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem ClosestIdem :
 forall p q : float, Fbounded b p -> Closest b radix p q -> p = q :>R.
Proof using .
Admitted.

Theorem FmultRadixInv :
 forall (x z : float) (y : R),
 Fbounded b x ->
 Closest b radix y z -> (/ 2 * x < y)%R -> (/ 2 * x <= z)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ClosestErrorBound :
 forall (p q : float) (x : R),
 Fbounded b p ->
 Closest b radix x p ->
 q = (x - p)%R :>R -> (Rabs q <= Float 1 (Fexp p) * / 2)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ClosestErrorBoundNormal_aux :
 forall (x : R) (p : float),
 Closest b radix x p ->
 Fnormal radix b (Fnormalize radix b precision p) ->
 (Rabs (x - p) <= Rabs p * (/ 2 * (radix * / Zpos (vNum b))))%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem ClosestErrorBoundNormal :
 forall (x : R) (p : float),
 Closest b radix x p ->
 Fnormal radix b (Fnormalize radix b precision p) ->
 (Rabs (x - p) <= Rabs p * (/ 2 * powerRZ radix (Z.succ (- precision))))%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem FpredUlpPos :
 forall x : float,
 Fcanonic radix b x ->
 (0 < x)%R ->
 (FPred b radix precision x +
  Fulp b radix precision (FPred b radix precision x))%R = x.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem FulpFPredLe :
 forall f : float,
 Fbounded b f ->
 Fcanonic radix b f ->
 (Fulp b radix precision f <=
  radix * Fulp b radix precision (FPred b radix precision f))%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

End Fclosestp2.

Section FRoundPM.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem errorBoundedMultClosest_aux :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p * q) pq ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 (p * q - pq)%R <> 0%R :>R ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fcanonic radix b r /\
       Fbounded b r /\
       Fbounded b s /\
       r = pq :>R /\
       s = (p * q - r)%R :>R /\
       Fexp s = (Fexp p + Fexp q)%Z :>Z /\
       (Fexp s <= Fexp r)%Z /\ (Fexp r <= precision + (Fexp p + Fexp q))%Z)).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem errorBoundedMultClosest :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p * q) pq ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 (- dExp b <= Fexp (Fnormalize radix b precision pq) - precision)%Z ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fcanonic radix b r /\
       Fbounded b r /\
       Fbounded b s /\
       r = pq :>R /\
       s = (p * q - r)%R :>R /\ Fexp s = (Fexp r - precision)%Z :>Z)).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.
End FRoundPM.

Section finduct.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition Fweight (p : float) :=
  (Fnum p + Fexp p * Zpower_nat radix precision)%Z.

Theorem FweightLt :
 forall p q : float,
 Fcanonic radix b p ->
 Fcanonic radix b q -> (0 <= p)%R -> (p < q)%R -> (Fweight p < Fweight q)%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FweightEq :
 forall p q : float,
 Fcanonic radix b p ->
 Fcanonic radix b q -> p = q :>R -> Fweight p = Fweight q.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FweightZle :
 forall p q : float,
 Fcanonic radix b p ->
 Fcanonic radix b q -> (0 <= p)%R -> (p <= q)%R -> (Fweight p <= Fweight q)%Z.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FinductNegAux :
 forall (P : float -> Prop) (p : float),
 (0 <= p)%R ->
 Fcanonic radix b p ->
 P p ->
 (forall q : float,
  Fcanonic radix b q ->
  (0 < q)%R -> (q <= p)%R -> P q -> P (FPred b radix precision q)) ->
 forall x : Z,
 (0 <= x)%Z ->
 forall q : float,
 x = (Fweight p - Fweight q)%Z ->
 Fcanonic radix b q -> (0 <= q)%R -> (q <= p)%R -> P q.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem FinductNeg :
 forall (P : float -> Prop) (p : float),
 (0 <= p)%R ->
 Fcanonic radix b p ->
 P p ->
 (forall q : float,
  Fcanonic radix b q ->
  (0 < q)%R -> (q <= p)%R -> P q -> P (FPred b radix precision q)) ->
 forall q : float, Fcanonic radix b q -> (0 <= q)%R -> (q <= p)%R -> P q.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.

Theorem radixRangeBoundExp :
 forall p q : float,
 Fcanonic radix b p ->
 Fcanonic radix b q ->
 (0 <= p)%R ->
 (p < q)%R -> (q < radix * p)%R -> Fexp p = Fexp q \/ Z.succ (Fexp p) = Fexp q.
Proof using pGivesBound precisionNotZero radixMoreThanOne.
Admitted.
End finduct.

Section FRoundPN.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem plusExpMin :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p + q)%R pq ->
 exists s : float,
   Fbounded b s /\ s = pq :>R /\ (Z.min (Fexp p) (Fexp q) <= Fexp s)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem plusExpUpperBound :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p + q)%R pq ->
 Fbounded b p ->
 Fbounded b q ->
 exists r : float,
   Fbounded b r /\ r = pq :>R /\ (Fexp r <= Z.succ (Zmax (Fexp p) (Fexp q)))%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem plusExpBound :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p + q)%R pq ->
 Fbounded b p ->
 Fbounded b q ->
 exists r : float,
   Fbounded b r /\
   r = pq :>R /\
   (Z.min (Fexp p) (Fexp q) <= Fexp r)%Z /\
   (Fexp r <= Z.succ (Zmax (Fexp p) (Fexp q)))%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem minusRoundRep :
 forall P,
 RoundedModeP b radix P ->
 forall p q qmp qmmp : float,
 (0 <= p)%R ->
 (p <= q)%R ->
 P (q - p)%R qmp ->
 Fbounded b p ->
 Fbounded b q -> exists r : float, Fbounded b r /\ r = (q - qmp)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem ExactMinusIntervalAux :
 forall P,
 RoundedModeP b radix P ->
 forall p q : float,
 (0 < p)%R ->
 (2 * p < q)%R ->
 Fcanonic radix b p ->
 Fcanonic radix b q ->
 (exists r : float, Fbounded b r /\ r = (q - p)%R :>R) ->
 forall r : float,
 Fcanonic radix b r ->
 (2 * p < r)%R ->
 (r <= q)%R -> exists r' : float, Fbounded b r' /\ r' = (r - p)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem ExactMinusIntervalAux1 :
 forall P,
 RoundedModeP b radix P ->
 forall p q : float,
 (0 <= p)%R ->
 (p <= q)%R ->
 Fcanonic radix b p ->
 Fcanonic radix b q ->
 (exists r : float, Fbounded b r /\ r = (q - p)%R :>R) ->
 forall r : float,
 Fcanonic radix b r ->
 (p <= r)%R ->
 (r <= q)%R -> exists r' : float, Fbounded b r' /\ r' = (r - p)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem ExactMinusInterval :
 forall P,
 RoundedModeP b radix P ->
 forall p q : float,
 (0 <= p)%R ->
 (p <= q)%R ->
 Fbounded b p ->
 Fbounded b q ->
 (exists r : float, Fbounded b r /\ r = (q - p)%R :>R) ->
 forall r : float,
 Fbounded b r ->
 (p <= r)%R ->
 (r <= q)%R -> exists r' : float, Fbounded b r' /\ r' = (r - p)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem MSBroundLSB :
 forall P : R -> float -> Prop,
 RoundedModeP b radix P ->
 forall f1 f2 : float,
 P f1 f2 ->
 ~ is_Fzero (Fminus radix f1 f2) ->
 (MSB radix (Fminus radix f1 f2) < LSB radix f2)%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem LSBMinus :
 forall p q : float,
 ~ is_Fzero (Fminus radix p q) ->
 (Z.min (LSB radix p) (LSB radix q) <= LSB radix (Fminus radix p q))%Z.
Proof using precision radixMoreThanZERO.
Admitted.

Theorem LSBPlus :
 forall p q : float,
 ~ is_Fzero (Fplus radix p q) ->
 (Z.min (LSB radix p) (LSB radix q) <= LSB radix (Fplus radix p q))%Z.
Proof using precision radixMoreThanZERO.
Admitted.

End FRoundPN.

Section ClosestP.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem errorBoundedPlusLe :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 (Fexp p <= Fexp q)%Z ->
 Closest b radix (p + q) pq ->
 exists error : float,
   error = Rabs (p + q - pq) :>R /\
   Fbounded b error /\ Fexp error = Z.min (Fexp p) (Fexp q).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedPlusAbs :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) pq ->
 exists error : float,
   error = Rabs (p + q - pq) :>R /\
   Fbounded b error /\ Fexp error = Z.min (Fexp p) (Fexp q).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem errorBoundedPlus :
 forall p q pq : float,
 (Fbounded b p) ->
 (Fbounded b q) ->
 (Closest b radix (p + q) pq) ->
 exists error : float,
   error = (p + q - pq)%R :>R /\
   (Fbounded b error) /\ (Fexp error) = (Z.min (Fexp p) (Fexp q)).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem plusExact1 :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 (Fexp r <= Z.min (Fexp p) (Fexp q))%Z -> r = (p + q)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem plusExact2Aux :
 forall p q r : float,
 (0 <= p)%R ->
 Fcanonic radix b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 (Fexp r < Z.pred (Fexp p))%Z -> r = (p + q)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem plusExact2 :
 forall p q r : float,
 Fcanonic radix b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 (Fexp r < Z.pred (Fexp p))%Z -> r = (p + q)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem plusExactR0 :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r -> r = 0%R :>R -> r = (p + q)%R :>R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem pPredMoreThanOne : (0 < pPred (vNum b))%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem pPredMoreThanRadix : (radix < pPred (vNum b))%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem plusExactExp :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) pq ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fbounded b r /\
       Fbounded b s /\
       s = pq :>R /\
       r = (p + q - s)%R :>R /\
       Fexp r = Z.min (Fexp p) (Fexp q) :>Z /\
       (Fexp r <= Fexp s)%Z /\ (Fexp s <= Z.succ (Zmax (Fexp p) (Fexp q)))%Z)).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

End ClosestP.

Section MinOrMax_def.
Variable radix : Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Variable b : Fbound.
Variable precision : nat.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Definition MinOrMax (z : R) (f : float) :=
  isMin b radix z f \/ isMax b radix z f.

Theorem MinOrMax_Fopp :
 forall (x : R) (f : float), MinOrMax (- x) (Fopp f) -> MinOrMax x f.
Proof using .
Admitted.

Theorem MinOrMax1 :
 forall (z : R) (p : float),
 Fbounded b p ->
 Fcanonic radix b p ->
 (0 < p)%R ->
 (Rabs (z - p) < Fulp b radix precision (FPred b radix precision p))%R ->
 MinOrMax z p.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem MinOrMax2 :
 forall (z : R) (p : float),
 Fbounded b p ->
 Fcanonic radix b p ->
 (0 < p)%R ->
 (Rabs (z - p) < Fulp b radix precision p)%R -> (p <= z)%R -> MinOrMax z p.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem MinOrMax3_aux :
 forall (z : R) (p : float),
 Fbounded b p ->
 Fcanonic radix b p ->
 0%R = p ->
 (z <= 0)%R ->
 (- z < Fulp b radix precision (FPred b radix precision p))%R -> MinOrMax z p.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem MinOrMax3 :
 forall (z : R) (p : float),
 Fbounded b p ->
 Fcanonic radix b p ->
 0%R = p ->
 (Rabs (z - p) < Fulp b radix precision (FPred b radix precision p))%R ->
 MinOrMax z p.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.
End MinOrMax_def.

Section AxpyMisc.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Variable b : Fbound.
Variable precision : nat.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem FulpLeGeneral :
 forall p : float,
 Fbounded b p ->
 (Fulp b radix precision p <=
  Rabs (FtoRradix p) * powerRZ radix (Z.succ (- precision)) +
  powerRZ radix (- dExp b))%R.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem RoundLeGeneral :
 forall (p : float) (z : R),
 Fbounded b p ->
 Closest b radix z p ->
 (Rabs p <=
  Rabs z * / (1 - powerRZ radix (- precision)) +
  powerRZ radix (Z.pred (- dExp b)) * / (1 - powerRZ radix (- precision)))%R.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem ExactSum_Near :
 forall p q f : float,
 Fbounded b p ->
 Fbounded b q ->
 Fbounded b f ->
 Closest b radix (p + q) f ->
 Fexp p = (- dExp b)%Z ->
 (Rabs (p + q - f) < powerRZ radix (- dExp b))%R -> (p + q)%R = f.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

End AxpyMisc.

Section AxpyAux.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Variable b : Fbound.
Variable precision : nat.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
Variables a1 x1 y1 : R.
Variables a x y t u r : float.
Hypothesis Fa : Fbounded b a.
Hypothesis Fx : Fbounded b x.
Hypothesis Fy : Fbounded b y.
Hypothesis Ft : Fbounded b t.
Hypothesis Fu : Fbounded b u.
Hypothesis tDef : Closest b radix (a * x) t.
Hypothesis uDef : Closest b radix (t + y) u.
Hypothesis rDef : isMin b radix (a1 * x1 + y1) r.

Theorem Axpy_aux1 :
 Fcanonic radix b u ->
 (Rabs (FtoRradix a * FtoRradix x - FtoRradix t) <=
  / 4 * Fulp b radix precision (FPred b radix precision u))%R ->
 (0 < u)%R ->
 (4 * Rabs t <= Rabs u)%R ->
 (Rabs (y1 - y) + Rabs (a1 * x1 - a * x) <
  / 4 * Fulp b radix precision (FPred b radix precision u))%R ->
 MinOrMax radix b (a1 * x1 + y1) u.
Proof using Fu pGivesBound precisionGreaterThanOne uDef.
Admitted.

Theorem Axpy_aux1_aux1 :
 Fnormal radix b t ->
 Fcanonic radix b u ->
 (0 < u)%R ->
 (4 * Rabs t <= Rabs u)%R ->
 (Rabs (FtoRradix a * FtoRradix x - FtoRradix t) <=
  / 4 * Fulp b radix precision (FPred b radix precision u))%R.
Proof using Ft Fu pGivesBound precisionGreaterThanOne tDef.
Admitted.

Theorem Axpy_aux2 :
 Fcanonic radix b u ->
 Fsubnormal radix b t ->
 (0 < u)%R ->
 FtoRradix u = (t + y)%R ->
 (Rabs (y1 - y) + Rabs (a1 * x1 - a * x) <
  / 4 * Fulp b radix precision (FPred b radix precision u))%R ->
 MinOrMax radix b (a1 * x1 + y1) u.
Proof using Ft Fu pGivesBound precisionGreaterThanOne tDef.
Admitted.

Theorem Axpy_aux1_aux3 :
 Fsubnormal radix b t ->
 Fcanonic radix b u ->
 (0 < u)%R ->
 (Z.succ (- dExp b) <= Fexp (FPred b radix precision u))%Z ->
 (Rabs (FtoRradix a * FtoRradix x - FtoRradix t) <=
  / 4 * Fulp b radix precision (FPred b radix precision u))%R.
Proof using Ft Fu pGivesBound precisionGreaterThanOne tDef.
Admitted.

Theorem Axpy_aux3 :
 Fcanonic radix b u ->
 Fsubnormal radix b t ->
 (0 < u)%R ->
 Fexp (FPred b radix precision u) = (- dExp b)%Z ->
 (Z.succ (- dExp b) <= Fexp u)%Z ->
 (Rabs (y1 - y) + Rabs (a1 * x1 - a * x) <
  / 4 * Fulp b radix precision (FPred b radix precision u))%R ->
 MinOrMax radix b (a1 * x1 + y1) u.
Proof using Ft Fu Fy pGivesBound precisionGreaterThanOne tDef uDef.
Admitted.

Theorem AxpyPos :
 Fcanonic radix b u ->
 Fcanonic radix b t ->
 (0 < u)%R ->
 (4 * Rabs t <= Rabs u)%R ->
 (Rabs (y1 - y) + Rabs (a1 * x1 - a * x) <
  / 4 * Fulp b radix precision (FPred b radix precision u))%R ->
 MinOrMax radix b (a1 * x1 + y1) u.
Proof using Ft Fu Fy pGivesBound precisionGreaterThanOne tDef uDef.
Admitted.

Definition FLess (p : float) :=
  match Rcase_abs p with
  | left _ => FSucc b radix precision p
  | right _ => FPred b radix precision p
  end.

Theorem UlpFlessuGe_aux :
 forall p : float,
 Fbounded b p ->
 Fcanonic radix b p ->
 (Rabs p - Fulp b radix precision p <= Rabs (FLess p))%R.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem UlpFlessuGe :
 Fcanonic radix b u ->
 (/
  (4 * (powerRZ radix precision - 1) * (1 + powerRZ radix (- precision))) *
  ((1 - powerRZ radix (Z.succ (- precision))) * Rabs y) +
  -
  (/
   (4 * (powerRZ radix precision - 1) * (1 + powerRZ radix (- precision)) *
    (1 - powerRZ radix (- precision))) *
   ((1 - powerRZ radix (Z.succ (- precision))) * Rabs (a * x))) +
  -
  (powerRZ radix (Z.pred (- dExp b)) *
   (/ (2 * (powerRZ radix precision - 1)) +
    /
    (4 * (powerRZ radix precision - 1) *
     (1 + powerRZ radix (- precision)) * (1 - powerRZ radix (- precision))) *
    (1 - powerRZ radix (Z.succ (- precision))))) <=
  / 4 * Fulp b radix precision (FLess u))%R.
Proof using Ft Fu Fy pGivesBound precisionGreaterThanOne tDef uDef.
Admitted.

Theorem UlpFlessuGe2 :
 Fcanonic radix b u ->
 (powerRZ radix (Z.pred (Z.pred (- precision))) *
  (1 - powerRZ radix (Z.succ (- precision))) * Rabs y +
  - (powerRZ radix (Z.pred (Z.pred (- precision))) * Rabs (a * x)) +
  - powerRZ radix (Z.pred (Z.pred (- dExp b))) <
  / 4 * Fulp b radix precision (FLess u))%R.
Proof using Ft Fu Fy pGivesBound precisionGreaterThanOne tDef uDef.
Admitted.

End AxpyAux.

Section Axpy.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Variable b : Fbound.
Variable precision : nat.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.

Theorem Axpy_tFlessu :
 forall (a1 x1 y1 : R) (a x y t u : float),
 Fbounded b a ->
 Fbounded b x ->
 Fbounded b y ->
 Fbounded b t ->
 Fbounded b u ->
 Closest b radix (a * x) t ->
 Closest b radix (t + y) u ->
 Fcanonic radix b u ->
 Fcanonic radix b t ->
 (4 * Rabs t <= Rabs u)%R ->
 (Rabs (y1 - y) + Rabs (a1 * x1 - a * x) <
  / 4 * Fulp b radix precision (FLess b precision u))%R ->
 MinOrMax radix b (a1 * x1 + y1) u.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Axpy_opt :
 forall (a1 x1 y1 : R) (a x y t u : float),
 (Fbounded b a) -> (Fbounded b x) -> (Fbounded b y) ->
 (Fbounded b t) -> (Fbounded b u) ->
 (Closest b radix (a * x) t) ->
 (Closest b radix (t + y) u) ->
 (Fcanonic radix b u) -> (Fcanonic radix b t) ->
 ((5 + 4 * (powerRZ radix (- precision))) *
    / (1 - powerRZ radix (- precision)) *
    (Rabs (a * x) + (powerRZ radix (Z.pred (- dExp b))))
    <= Rabs y)%R ->
 (Rabs (y1 - y) + Rabs (a1 * x1 - a * x) <=
    (powerRZ radix (Z.pred (Z.pred (- precision)))) *
    (1 - powerRZ radix (Z.succ (- precision))) * Rabs y +
    - (powerRZ radix (Z.pred (Z.pred (- precision))) * Rabs (a * x)) +
    - powerRZ radix (Z.pred (Z.pred (- dExp b))))%R ->
         (MinOrMax radix b (a1 * x1 + y1) u).
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

End Axpy.

Section Generic.
Variable b : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix p.

Theorem FboundedMbound2Pos :
 (0 < p) ->
 forall z m : Z,
 (0 <= m)%Z ->
 (m <= Zpower_nat radix p)%Z ->
 (- dExp b <= z)%Z ->
 exists c : float, Fbounded b c /\ c = (m * powerRZ radix z)%R :>R /\ (z <= Fexp c)%Z.
Proof using pGivesBound radixMoreThanOne.
Admitted.

Theorem FboundedMbound2 :
 (0 < p) ->
 forall z m : Z,
 (Z.abs m <= Zpower_nat radix p)%Z ->
 (- dExp b <= z)%Z ->
 exists c : float, Fbounded b c /\ c = (m * powerRZ radix z)%R :>R /\ (z <= Fexp c)%Z.
Proof using pGivesBound radixMoreThanOne.
Admitted.

Hypothesis precisionGreaterThanOne : 1 < p.

Variable z:R.
Variable f:float.
Variable e:Z.

Hypothesis Bf: Fbounded b f.
Hypothesis Cf: Fcanonic radix b f.
Hypothesis zGe: (powerRZ radix (e+p-1) <= z)%R.
Hypothesis zLe: (z <= powerRZ radix (e+p))%R.
Hypothesis fGe: (powerRZ radix (e+p-1) <= f)%R.
Hypothesis eGe: (- dExp b <= e)%Z.

Theorem ClosestSuccPred: (Fcanonic radix b f)
 -> (Rabs(z-f) <= Rabs(z-(FSucc b radix p f)))%R
 -> (Rabs(z-f) <= Rabs(z-(FPred b radix p f)))%R
 -> Closest b radix z f.
Proof using Bf pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ImplyClosest: (Rabs(z-f) <= (powerRZ radix e)/2)%R
  -> Closest b radix z f.
Proof using Bf Cf eGe fGe pGivesBound precisionGreaterThanOne radixMoreThanZERO zGe.
Admitted.

Theorem ImplyClosestStrict: (Rabs(z-f) < (powerRZ radix e)/2)%R
  -> (forall g: float, Closest b radix z g -> (FtoRradix f=g)%R ).
Proof using Bf Cf eGe fGe pGivesBound precisionGreaterThanOne radixMoreThanZERO zGe.
Admitted.

Theorem ImplyClosestStrict2: (Rabs(z-f) < (powerRZ radix e)/2)%R
  -> (Closest b radix z f) /\ (forall g: float, Closest b radix z g -> (FtoRradix f=g)%R ).
Proof using Bf Cf eGe fGe pGivesBound precisionGreaterThanOne radixMoreThanZERO zGe.
Admitted.

End Generic.

Section Generic2.
Variable b : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hypothesis precisionGreaterThanOne : 1 < p.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix p.

Variable z m:R.
Variable f h:float.

Theorem ClosestImplyEven: (EvenClosest b radix p z f) ->
   (exists g: float, (z=g+(powerRZ radix (Fexp g))/2)%R /\ (Fcanonic radix b g) /\ (0 <= Fnum g)%Z)
       -> (FNeven b radix p f).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem ClosestImplyEven_int: (Even radix)%Z
   ->  (EvenClosest b radix p z f) -> (Fcanonic radix b f) -> (0 <= f)%R
   ->  (z=(powerRZ radix (Fexp f))*(m+1/2))%R -> (exists n:Z, IZR n=m)
   ->  (FNeven b radix p f).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

End Generic2.
Section Velt.

Variable radix : Z.
Variable b : Fbound.
Variables s t:nat.
Variables p x q hx: float.

Let b' := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix (minus t s)))))
    (dExp b).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypothesis SLe: (2 <= s).
Hypothesis SGe: (s <= t-2).
Hypothesis Fx:  Fbounded b x.
Hypothesis pDef: (Closest b radix (x*((powerRZ radix s)+1))%R p).
Hypothesis qDef: (Closest b radix (x-p)%R  q).
Hypothesis hxDef:(Closest b radix (q+p)%R hx).
Hypothesis xPos: (0 < x)%R.
Hypothesis Np:  Fnormal radix b p.
Hypothesis Nq:  Fnormal radix b q.
Hypothesis Nx:  Fnormal radix b x.

Lemma p'GivesBound: Zpos (vNum b')=(Zpower_nat radix (minus t s)).
Proof using b radixMoreThanOne.
Admitted.

Lemma pPos: (0 <= p)%R.
Proof using SGe SLe pDef pGivesBound radixMoreThanOne xPos.
Admitted.

Lemma qNeg: (q <= 0)%R.
Proof using Fx SGe SLe pDef pGivesBound qDef radixMoreThanOne xPos.
Admitted.

Lemma RleRRounded:  forall (f : float) (z : R),
   Fnormal radix b f -> Closest b radix z f -> (Rabs z <= (Rabs f)*(1+(powerRZ radix (1-t))/2))%R.
Proof using SGe SLe pGivesBound radixMoreThanOne.
Admitted.

Lemma hxExact: (FtoRradix hx=p+q)%R.
Proof using Fx Np Nq SGe SLe hxDef pDef pGivesBound qDef radixMoreThanZERO xPos.
Admitted.

Lemma eqLeep: (Fexp q <= Fexp p)%Z.
Proof using Fx Np Nq SGe SLe pDef pGivesBound qDef radixMoreThanOne xPos.
Admitted.

Lemma epLe: (Fexp p <=s+1+Fexp x)%Z.
Proof using Fx Np Nx SGe SLe pDef pGivesBound radixMoreThanOne xPos.
Admitted.

Lemma eqLe: (Fexp q <= s+ Fexp x)%Z \/
  ((FtoRradix q= - powerRZ radix (t+s+Fexp x))%R /\(Rabs (x - hx) <= (powerRZ radix (s + Fexp x))/2)%R).
Proof using Fx Np Nq Nx SGe SLe hxDef pDef pGivesBound qDef radixMoreThanZERO xPos.
Admitted.

Lemma eqGe: (s+ Fexp x <= Fexp q)%Z.
Proof using Fx Np Nq Nx SGe SLe pDef pGivesBound qDef radixMoreThanOne xPos.
Admitted.

Lemma eqEqual: (Fexp q=s+Fexp x)%Z \/
  ((FtoRradix q= - powerRZ radix (t+s+Fexp x))%R /\
     (Rabs (x - hx) <= (powerRZ radix (s + Fexp x))/2)%R).
Proof using Fx Np Nq Nx SGe SLe hxDef pDef pGivesBound qDef radixMoreThanZERO xPos.
Admitted.

Lemma Veltkamp_aux_aux: forall v:float,  (FtoRradix v=hx) -> Fcanonic radix b' v ->
  (Rabs (x-v) <= (powerRZ radix (s+Fexp x)) /2)%R
  -> (powerRZ radix (t-1+Fexp x) <= v)%R.
Proof using Fx Np Nq Nx SGe SLe hxDef pDef pGivesBound qDef radixMoreThanZERO xPos.
Admitted.

Lemma Veltkamp_aux:
   (Rabs (x-hx) <= (powerRZ radix (s+Fexp x)) /2)%R /\
   (exists hx':float, (FtoRradix hx'=hx) /\ (Closest b' radix x hx')
    /\ (s+Fexp x <= Fexp hx')%Z).
Proof using Fx Np Nq Nx SGe SLe hxDef pDef pGivesBound qDef radixMoreThanZERO xPos.
Admitted.

Hypothesis pDefEven: (EvenClosest b radix t (x*((powerRZ radix s)+1))%R p).
Hypothesis qDefEven: (EvenClosest b radix t (x-p)%R  q).
Hypothesis hxDefEven:(EvenClosest b radix t (q+p)%R hx).

Lemma VeltkampEven1: (Even radix)
   ->(exists hx':float, (FtoRradix hx'=hx)
    /\ (EvenClosest b' radix (t-s) x hx')).
Proof using Fx Np Nq Nx SGe SLe hxDef hxDefEven pDef pDefEven pGivesBound qDef qDefEven radixMoreThanZERO xPos.
Admitted.

Lemma VeltkampEven2: (Odd radix)
   -> (exists hx':float, (FtoRradix hx'=hx) /\ (EvenClosest b' radix (t-s) x hx')).
Proof using Fx Np Nq Nx SGe SLe hxDef pDef pGivesBound qDef radixMoreThanZERO xPos.
Admitted.

End Velt.
Section VeltN.

Variable radix : Z.
Variable b : Fbound.
Variables s t:nat.

Let b' := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix (minus t s)))))
    (dExp b).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypothesis SLe: (2 <= s).
Hypothesis SGe: (s <= t-2).

Lemma Veltkamp_pos: forall x p q hx:float,
     Fnormal radix b x -> Fcanonic radix b p ->  Fcanonic radix b q
  -> (0 < x)%R
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Rabs (x-hx) <= (powerRZ radix (s+Fexp x)) /2)%R /\
     (exists hx':float, (FtoRradix hx'=hx) /\ (Closest b' radix x hx')
       /\ (s+Fexp x <= Fexp hx')%Z).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

Lemma VeltkampN_aux: forall x p q hx:float,
      Fnormal radix b x -> Fcanonic radix b p ->  Fcanonic radix b q
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Rabs (x-hx) <= (powerRZ radix (s+Fexp x)) /2)%R /\
     (exists hx':float, (FtoRradix hx'=hx) /\ (Closest b' radix x hx')
       /\ (s+Fexp x <= Fexp hx')%Z).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

Lemma VeltkampN: forall x p q hx:float,
      Fnormal radix b x
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Rabs (x-hx) <= (powerRZ radix (s+Fexp x)) /2)%R /\
     (exists hx':float, (FtoRradix hx'=hx) /\ (Closest b' radix x hx')
       /\ (s+Fexp x <= Fexp hx')%Z).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

Lemma VeltkampEven_pos: forall x p q hx:float,
      Fnormal radix b x -> Fcanonic radix b p ->  Fcanonic radix b q
  -> (0 < x)%R
  -> (EvenClosest b radix t (x*((powerRZ radix s)+1))%R p)
  -> (EvenClosest b radix t (x-p)%R  q)
  -> (EvenClosest b radix t (q+p)%R hx)
  -> (exists hx':float, (FtoRradix hx'=hx) /\ (EvenClosest b' radix (t-s) x hx')).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

Lemma VeltkampEvenN_aux: forall x p q hx:float,
      Fnormal radix b x -> Fcanonic radix b p ->  Fcanonic radix b q
  -> (EvenClosest b radix t (x*((powerRZ radix s)+1))%R p)
  -> (EvenClosest b radix t (x-p)%R  q)
  -> (EvenClosest b radix t (q+p)%R hx)
  -> (exists hx':float, (FtoRradix hx'=hx) /\ (EvenClosest b' radix (t-s) x hx')).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

Lemma VeltkampEvenN: forall x p q hx:float,
      Fnormal radix b x
  -> (EvenClosest b radix t (x*((powerRZ radix s)+1))%R p)
  -> (EvenClosest b radix t (x-p)%R  q)
  -> (EvenClosest b radix t (q+p)%R hx)
  -> (exists hx':float, (FtoRradix hx'=hx) /\ (EvenClosest b' radix (t-s) x hx')).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

End VeltN.
Section VeltS.

Variable radix : Z.
Variable b : Fbound.
Variables s t:nat.

Let b' := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix (minus t s)))))
    (dExp b).

Definition plusExp (b:Fbound):=
   Bound
     (vNum b)
     (Nplus (dExp b) (Npos (P_of_succ_nat (pred (pred t))))).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypothesis SLe: (2 <= s).
Hypothesis SGe: (s <= t-2).

Lemma bimplybplusNorm: forall f:float,
   Fbounded b f -> (FtoRradix f <> 0)%R ->
    (exists g:float, (FtoRradix g=f)%R /\
      Fnormal radix (plusExp b) g).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

Lemma Closestbplusb: forall b0:Fbound, forall z:R, forall f:float,
   (Closest (plusExp b0) radix z f) -> (Fbounded b0 f) -> (Closest b0 radix z f).
Proof using SGe SLe b.
Admitted.

Lemma Closestbbplus: forall b0:Fbound, forall n:nat, forall fext f:float,
    Zpos (vNum b0)=(Zpower_nat radix n) -> (1 < n) ->
   (-dExp b0 <= Fexp fext)%Z ->
    (Closest b0 radix fext f) -> (Closest (plusExp b0) radix fext f).
Proof using SGe SLe b radixMoreThanZERO.
Admitted.

Lemma EvenClosestbplusb: forall b0:Fbound, forall n:nat, forall fext f:float,
    Zpos (vNum b0)=(Zpower_nat radix n) -> (1 < n) ->
   (-dExp b0 <= Fexp fext)%Z ->
   (EvenClosest (plusExp b0) radix n fext f) -> (Fbounded b0 f)
      -> (EvenClosest b0 radix n fext f).
Proof using SGe SLe b radixMoreThanZERO.
Admitted.

Lemma ClosestClosest: forall b0:Fbound, forall n:nat, forall z:R, forall f1 f2:float,
    Zpos (vNum b0)=(Zpower_nat radix n) -> (1 < n) ->
    (Closest b0 radix z f1) -> (Closest b0 radix z f2)
    -> Fnormal radix b0 f2 -> (Fexp f1 <= Fexp f2 -2)%Z
    -> False.
Proof using SGe SLe b radixMoreThanZERO.
Admitted.

Lemma EvenClosestbbplus: forall b0:Fbound, forall n:nat, forall fext f:float,
    Zpos (vNum b0)=(Zpower_nat radix n) -> (1 < n) ->
   (-dExp b0 <= Fexp fext)%Z ->
    (EvenClosest b0 radix n fext f) -> (EvenClosest (plusExp b0) radix n fext f).
Proof using SGe SLe b radixMoreThanZERO.
Admitted.

Lemma VeltkampS: forall x p q hx:float,
     Fsubnormal radix b x
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Rabs (x-hx) <= (powerRZ radix (s+Fexp x)) /2)%R /\
     (exists hx':float, (FtoRradix hx'=hx) /\ (Closest b' radix x hx')).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

Lemma VeltkampEvenS: forall x p q hx:float,
      Fsubnormal radix b x
  -> (EvenClosest b radix t (x*((powerRZ radix s)+1))%R p)
  -> (EvenClosest b radix t (x-p)%R  q)
  -> (EvenClosest b radix t (q+p)%R hx)
  -> (exists hx':float, (FtoRradix hx'=hx) /\ (EvenClosest b' radix (t-s) x hx')).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

End VeltS.
Section VeltUlt.

Variable radix : Z.
Variable b : Fbound.
Variables s t:nat.

Let b' := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix (minus t s)))))
    (dExp b).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypothesis SLe: (2 <= s).
Hypothesis SGe: (s <= t-2).

Theorem Veltkamp: forall x p q hx:float,
     (Fbounded b x)
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Rabs (x-hx) <= (powerRZ radix (s+Fexp x)) /2)%R /\
      (exists hx':float, (FtoRradix hx'=hx) /\ (Closest b' radix x hx')
         /\ ((Fnormal radix b x) -> (s+Fexp x <= Fexp hx')%Z)).
Proof using SGe SLe pGivesBound radixMoreThanOne.
Admitted.

Theorem VeltkampEven: forall x p q hx:float,
     (Fbounded b x)
  -> (EvenClosest b radix t (x*((powerRZ radix s)+1))%R p)
  -> (EvenClosest b radix t (x-p)%R  q)
  -> (EvenClosest b radix t (q+p)%R hx)
  -> (exists hx':float, (FtoRradix hx'=hx) /\ (EvenClosest b' radix (t-s) x hx')).
Proof using SGe SLe pGivesBound radixMoreThanOne.
Admitted.

End VeltUlt.
Section VeltTail.

Variable radix : Z.
Variable b : Fbound.
Variables s t:nat.

Let b' := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix (minus t s)))))
    (dExp b).

Let bt := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix s))))
    (dExp b).

Let bt2 := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix (minus s 1)))))
    (dExp b).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypothesis SLe: (2 <= s).
Hypothesis SGe: (s <= t-2).

Theorem Veltkamp_tail_aux: forall x p q hx tx:float,
     (Fcanonic radix b x)
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Closest b radix (x-hx)%R tx)
  -> (exists v:float, (FtoRradix v=hx) /\
     (Fexp (Fminus radix x v) = Fexp x) /\
      (Z.abs (Fnum (Fminus radix x v)) <= (powerRZ radix s)/2)%R).
Proof using SGe SLe b' pGivesBound radixMoreThanZERO.
Admitted.

Theorem Veltkamp_tail: forall x p q hx tx:float,
     (Fbounded b x)
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Closest b radix (x-hx)%R tx)
  -> (exists tx':float, (FtoRradix tx'=tx) /\
         (hx+tx'=x)%R /\ (Fbounded bt tx') /\
         (Fexp (Fnormalize radix b t x) <= Fexp tx')%Z).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

Theorem Veltkamp_tail2: forall x p q hx tx:float,
     (radix=2)%Z
  -> (Fbounded b x)
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Closest b radix (x-hx)%R tx)
  -> (exists tx':float, (FtoRradix tx'=tx)  /\
         (hx+tx'=x)%R /\ (Fbounded bt2 tx') /\
         (Fexp (Fnormalize radix b t x) <= Fexp tx')%Z).
Proof using SGe SLe pGivesBound radixMoreThanZERO.
Admitted.

End VeltTail.

Section VeltUtile.
Variable radix : Z.
Variable b : Fbound.
Variables s t:nat.

Let b' := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix (minus t s)))))
    (dExp b).

Let bt := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix s))))
    (dExp b).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypothesis SLe: (2 <= s).
Hypothesis SGe: (s <= t-2).

Theorem VeltkampU: forall x p q hx tx:float,
     (Fcanonic radix b x)
  -> (Closest b radix (x*((powerRZ radix s)+1))%R p)
  -> (Closest b radix (x-p)%R  q)
  -> (Closest b radix (q+p)%R hx)
  -> (Closest b radix (x-hx)%R tx)
  -> (Rabs (x-hx) <= (powerRZ radix (s+Fexp x)) /2)%R /\
     (FtoRradix x=hx+tx)%R /\

     (exists hx':float, (FtoRradix hx'=hx)%R
                     /\ (Fbounded b' hx')
                     /\ ((Fnormal radix b x) -> (s+Fexp x <= Fexp hx')%Z)) /\

     (exists tx':float, (FtoRradix tx'=tx)%R
                     /\ (Fbounded bt tx')
                     /\ (Fexp x <= Fexp tx')%Z).
Proof using SGe SLe pGivesBound radixMoreThanOne.
Admitted.

End VeltUtile.

Section GenericDek.
Variable b : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 1 < p.

Theorem BoundedL: forall (r:R) (x:float) (e:Z),
   (e <=Fexp x)%Z -> (-dExp b <= e)%Z -> (FtoRradix x=r)%R ->
   (Rabs r < powerRZ radix (e+p))%R ->
       (exists x':float, (FtoRradix x'=r) /\ (Fbounded b x') /\ Fexp x'=e).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem ClosestZero: forall (r:R) (x:float),
  (Closest b radix r x) -> (r=0)%R -> (FtoRradix x=0)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Theorem Closestbbext: forall bext:Fbound, forall fext f:float,
    (vNum bext=vNum b) -> (dExp b < dExp bext)%Z ->
    (-dExp b <= Fexp fext)%Z ->
    (Closest b radix fext f) -> (Closest bext radix fext f).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Variable b' : Fbound.

Definition Underf_Err (a a' : float) (ra n:R) :=
   (Closest b radix ra a) /\ (Fbounded b' a') /\
   (Rabs (a-a') <= n*powerRZ radix (-(dExp b)))%R /\
   ( ((-dExp b) <= Fexp a')%Z -> (FtoRradix a =a')%R).

Theorem Underf_Err1: forall (a' a:float),
    vNum b=vNum b' -> (dExp b <= dExp b')%Z ->
   (Fbounded b' a') -> (Closest b radix a' a) ->
   (Underf_Err a a' (FtoRradix a') (/2)%R).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem Underf_Err2_aux: forall (r:R) (x1:float),
    vNum b=vNum b' -> (dExp b <= dExp b')%Z ->
    (Fcanonic radix b x1) ->
    (Closest b radix r x1) ->
    (exists x2:float, (Underf_Err x1 x2 r (3/4)%R) /\ (Closest b' radix r x2)).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem Underf_Err2: forall (r:R) (x1:float),
    vNum b=vNum b' -> (dExp b <= dExp b')%Z ->
    (Closest b radix r x1) ->
    (exists x2:float, (Underf_Err x1 x2 r (3/4)%R) /\ (Closest b' radix r x2)).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem Underf_Err3: forall (x x' y y' z' z:float) (rx ry epsx epsy:R),
    vNum b=vNum b' -> (dExp b <= dExp b')%Z ->
   (Underf_Err x x' rx epsx) -> (Underf_Err y y' ry epsy) ->
   (epsx+epsy <= (powerRZ radix (p-1) -1))%R ->
   (Fbounded b' z') -> (FtoRradix z'=x'-y')%R ->
   (Fexp z' <= Fexp x')%Z -> (Fexp z' <= Fexp y')%Z ->
   (Closest b radix (x-y) z) ->
   (Underf_Err z z' (x-y) (epsx+epsy)%R).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Theorem Underf_Err3_bis: forall (x x' y y' z' z:float) (rx ry epsx epsy:R),
   (4 <= p) ->
    vNum b=vNum b' -> (dExp b <= dExp b')%Z ->
   (Underf_Err x x' rx epsx) -> (Underf_Err y y' ry epsy) ->
   (epsx+epsy <= 7)%R ->
   (Fbounded b' z') -> (FtoRradix z'=x'-y')%R ->
   (Fexp z' <= Fexp x')%Z -> (Fexp z' <= Fexp y')%Z ->
   (Closest b radix (x-y) z) ->
   (Underf_Err z z' (x-y) (epsx+epsy)%R).
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

End GenericDek.

Section Sec1.

Variable radix : Z.
Variable b : Fbound.
Variables s t:nat.

Let b' := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix (minus t s)))))
    (dExp b).

Let bt := Bound
    (P_of_succ_nat (pred (Z.abs_nat (Zpower_nat radix s))))
    (dExp b).

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).

Hypothesis SLe: (2 <= s).
Hypothesis SGe: (s <= t-2).

Hypothesis Hst1: (t-1 <= s+s)%Z.
Hypothesis Hst2: (s+s <= t+1)%Z.

Variables x x1 x2 y y1 y2 r e: float.

Hypotheses Nx: Fnormal radix b x.
Hypotheses Ny: Fnormal radix b y.

Hypothesis K: (-dExp b <= Fexp x +Fexp y)%Z.

Hypotheses rDef: Closest b radix (x*y) r.

Hypotheses eeq: (x*y=r+e)%R.
Hypotheses Xeq: (FtoRradix x=x1+x2)%R.
Hypotheses Yeq: (FtoRradix y=y1+y2)%R.

Hypotheses x2Le: (Rabs x2 <= (powerRZ radix (s+Fexp x)) /2)%R.
Hypotheses y2Le: (Rabs y2 <= (powerRZ radix (s+Fexp y)) /2)%R.
Hypotheses x1Exp: (s+Fexp x <= Fexp x1)%Z.
Hypotheses y1Exp: (s+Fexp y <= Fexp y1)%Z.
Hypotheses x2Exp: (Fexp x <= Fexp x2)%Z.
Hypotheses y2Exp: (Fexp y <= Fexp y2)%Z.

Lemma x2y2Le: (Rabs (x2*y2) <= (powerRZ radix (2*s+Fexp x+Fexp y)) /4)%R.
Proof using SGe SLe b radixMoreThanOne x2Le y2Le.
Admitted.

Lemma x2y1Le: (Rabs (x2*y1) < (powerRZ radix (t+s+Fexp x+Fexp y)) /2
          + (powerRZ radix (2*s+Fexp x+Fexp y)) /4)%R.
Proof using Ny SGe SLe Yeq pGivesBound radixMoreThanZERO x2Le y2Le.
Admitted.

Lemma x1y2Le: (Rabs (x1*y2) < (powerRZ radix (t+s+Fexp x+Fexp y)) /2
          + (powerRZ radix (2*s+Fexp x+Fexp y)) /4)%R.
Proof using Nx SGe SLe Xeq pGivesBound radixMoreThanZERO x2Le y2Le.
Admitted.

Lemma eLe: (Rabs e <= (powerRZ radix (t+Fexp x+Fexp y)) /2)%R.
Proof using Hst2 K Nx Ny SGe SLe eeq pGivesBound rDef radixMoreThanZERO.
Admitted.

Lemma rExp: (t - 1 + Fexp x + Fexp y <= Fexp r)%Z.
Proof using Hst2 K Nx Ny SGe SLe pGivesBound rDef radixMoreThanZERO.
Admitted.

Lemma powerRZSumRle: forall (e1 e2:Z),
  (e2<= e1)%Z ->
  (powerRZ radix e1 + powerRZ radix e2 <= powerRZ radix (e1+1))%R.
Proof using radixMoreThanOne.
Admitted.

Lemma Boundedt1: (exists x':float, (FtoRradix x'=r-x1*y1)%R /\ (Fbounded b x')
                   /\ (Fexp x'=t-1+Fexp x+Fexp y)%Z).
Proof using Hst1 Hst2 K Nx Ny SGe SLe Xeq Yeq eeq pGivesBound rDef radixMoreThanZERO x1Exp x2Le y1Exp y2Le.
Admitted.

Lemma Boundedt2: (exists x':float, (FtoRradix x'=r-x1*y1-x1*y2)%R /\ (Fbounded b x')
                   /\ (Fexp x'=s+Fexp x+Fexp y)%Z).
Proof using Hst1 Hst2 K Nx Ny SGe SLe Xeq Yeq eeq pGivesBound rDef radixMoreThanZERO x1Exp x2Le y1Exp y2Exp y2Le.
Admitted.

Lemma Boundedt3: (exists x':float, (FtoRradix x'=r-x1*y1-x1*y2-x2*y1)%R /\ (Fbounded b x')
                   /\ (Fexp x'=s+Fexp x+Fexp y)%Z).
Proof using Hst1 Hst2 K Nx Ny SGe SLe Xeq Yeq eeq pGivesBound rDef radixMoreThanZERO x1Exp x2Exp x2Le y1Exp y2Exp y2Le.
Admitted.

Lemma Boundedt4: (exists x':float, (FtoRradix x'=r-x1*y1-x1*y2-x2*y1-x2*y2)%R /\ (Fbounded b x')).
Proof using Hst2 K Nx Ny SGe SLe Xeq Yeq pGivesBound rDef radixMoreThanOne.
Admitted.

Lemma Boundedt4_aux: (exists x':float, (FtoRradix x'=r-x1*y1-x1*y2-x2*y1-x2*y2)%R /\ (Fbounded b x')
  /\ (Fexp x'=Fexp x+Fexp y)%Z).
Proof using Hst2 K Nx Ny SGe SLe Xeq Yeq pGivesBound rDef radixMoreThanOne.
Admitted.

Hypotheses Fx1: Fbounded b' x1.
Hypotheses Fx2: Fbounded bt x2.
Hypotheses Fy1: Fbounded b' y1.
Hypotheses Fy2: Fbounded bt y2.
Hypothesis Hst3: (t <= s+s)%Z.

Lemma p''GivesBound: Zpos (vNum bt)=(Zpower_nat radix s).
Proof using b radixMoreThanOne.
Admitted.

Lemma Boundedx1y1_aux: (exists x':float, (FtoRradix x'=x1*y1)%R /\ (Fbounded b x')
  /\ (Fexp x'=Fexp x1+Fexp y1)%Z ).
Proof using Fx1 Fy1 Hst2 Hst3 K SGe SLe pGivesBound radixMoreThanZERO x1Exp y1Exp.
Admitted.

Lemma Boundedx1y1: (exists x':float, (FtoRradix x'=x1*y1)%R /\ (Fbounded b x')).
Proof using Fx1 Fy1 Hst2 Hst3 K SGe SLe pGivesBound radixMoreThanZERO x1Exp y1Exp.
Admitted.

Lemma Boundedx1y2_aux: (exists x':float, (FtoRradix x'=x1*y2)%R /\ (Fbounded b x')
   /\ (Fexp x'=Fexp x1+Fexp y2)%Z ).
Proof using Fx1 Fy2 Hst2 Hst3 K SGe SLe pGivesBound radixMoreThanZERO x1Exp y2Exp.
Admitted.

Lemma Boundedx1y2: (exists x':float, (FtoRradix x'=x1*y2)%R /\ (Fbounded b x')).
Proof using Fx1 Fy2 Hst2 Hst3 K SGe SLe pGivesBound radixMoreThanZERO x1Exp y2Exp.
Admitted.

Lemma Boundedx2y1_aux: (exists x':float, (FtoRradix x'=x2*y1)%R /\ (Fbounded b x')
   /\ (Fexp x'=Fexp x2+Fexp y1)%Z ).
Proof using Fx2 Fy1 Hst2 Hst3 K SGe SLe pGivesBound radixMoreThanZERO x2Exp y1Exp.
Admitted.

Lemma Boundedx2y1: (exists x':float, (FtoRradix x'=x2*y1)%R /\ (Fbounded b x')).
Proof using Fx2 Fy1 Hst2 Hst3 K SGe SLe pGivesBound radixMoreThanZERO x2Exp y1Exp.
Admitted.

End Sec1.

Section Algo.

Variable radix : Z.
Variable b : Fbound.
Variables t:nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypotheses pGe: (4 <= t).

Variables x y p q hx tx p' q' hy ty x1y1 x1y2 x2y1 x2y2 r t1 t2 t3 t4:float.

Hypothesis Cx: (Fnormal radix b x).
Hypothesis Cy: (Fnormal radix b y).

Hypothesis Expoxy: (-dExp b <= Fexp x+Fexp y)%Z.

Let s:= t- Nat.div2 t.

Hypothesis A1: (Closest b radix (x*((powerRZ radix s)+1))%R p).
Hypothesis A2: (Closest b radix (x-p)%R  q).
Hypothesis A3: (Closest b radix (q+p)%R hx).
Hypothesis A4: (Closest b radix (x-hx)%R tx).

Hypothesis B1: (Closest b radix (y*((powerRZ radix s)+1))%R p').
Hypothesis B2: (Closest b radix (y-p')%R  q').
Hypothesis B3: (Closest b radix (q'+p')%R hy).
Hypothesis B4: (Closest b radix (y-hy)%R ty).

Hypothesis C1: (Closest b radix (hx*hy)%R  x1y1).
Hypothesis C2: (Closest b radix (hx*ty)%R  x1y2).
Hypothesis C3: (Closest b radix (tx*hy)%R  x2y1).
Hypothesis C4: (Closest b radix (tx*ty)%R  x2y2).

Hypothesis D1: (Closest b radix (x*y)%R  r).
Hypothesis D2: (Closest b radix (r-x1y1)%R  t1).
Hypothesis D3: (Closest b radix (t1-x1y2)%R  t2).
Hypothesis D4: (Closest b radix (t2-x2y1)%R  t3).
Hypothesis D5: (Closest b radix (t3-x2y2)%R  t4).

Lemma SLe: (2 <= s).
Proof using b pGe.
Admitted.

Lemma SGe: (s <= t-2).
Proof using b pGe.
Admitted.

Lemma s2Ge: (t <= s + s)%Z.
Proof using b pGe.
Admitted.

Lemma s2Le: (s + s <= t + 1)%Z.
Proof using b pGe.
Admitted.

Theorem Dekker_aux: (exists x':float, (FtoRradix x'=tx*ty)%R /\ (Fbounded b x'))
    -> (x*y=r-t4)%R.
Proof using A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 Cx Cy D1 D2 D3 D4 D5 Expoxy pGe pGivesBound radixMoreThanZERO.
Admitted.

Theorem Boundedx2y2: (radix=2)%Z \/ (Nat.Even t) ->
    (exists x':float, (FtoRradix x'=tx*ty)%R /\ (Fbounded b x') /\ (Fexp x+Fexp y <= Fexp x')%Z).
Proof using A1 A2 A3 A4 B1 B2 B3 B4 Cx Cy Expoxy pGe pGivesBound radixMoreThanZERO.
Admitted.

Theorem DekkerN: (radix=2)%Z \/ (Nat.Even t) ->  (x*y=r-t4)%R.
Proof using A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 Cx Cy D1 D2 D3 D4 D5 Expoxy pGe pGivesBound radixMoreThanZERO.
Admitted.

End Algo.

Section AlgoS1.

Variable radix : Z.
Variable b : Fbound.
Variables t:nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypotheses pGe: (4 <= t).

Variables x y p q hx tx p' q' hy ty x1y1 x1y2 x2y1 x2y2 r t1 t2 t3 t4:float.

Hypothesis Cx: (Fnormal radix b x).
Hypothesis Cy: (Fsubnormal radix b y).

Hypothesis Expoxy: (-dExp b <= Fexp x+Fexp y)%Z.

Let s:= t- Nat.div2 t.

Hypothesis A1: (Closest b radix (x*((powerRZ radix s)+1))%R p).
Hypothesis A2: (Closest b radix (x-p)%R  q).
Hypothesis A3: (Closest b radix (q+p)%R hx).
Hypothesis A4: (Closest b radix (x-hx)%R tx).

Hypothesis B1: (Closest b radix (y*((powerRZ radix s)+1))%R p').
Hypothesis B2: (Closest b radix (y-p')%R  q').
Hypothesis B3: (Closest b radix (q'+p')%R hy).
Hypothesis B4: (Closest b radix (y-hy)%R ty).

Hypothesis C1: (Closest b radix (hx*hy)%R  x1y1).
Hypothesis C2: (Closest b radix (hx*ty)%R  x1y2).
Hypothesis C3: (Closest b radix (tx*hy)%R  x2y1).
Hypothesis C4: (Closest b radix (tx*ty)%R  x2y2).

Hypothesis D1: (Closest b radix (x*y)%R  r).
Hypothesis D2: (Closest b radix (r-x1y1)%R  t1).
Hypothesis D3: (Closest b radix (t1-x1y2)%R  t2).
Hypothesis D4: (Closest b radix (t2-x2y1)%R  t3).
Hypothesis D5: (Closest b radix (t3-x2y2)%R  t4).

Theorem DekkerS1: (radix=2)%Z \/ (Nat.Even t) ->  (x*y=r-t4)%R.
Proof using A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 Cx Cy D1 D2 D3 D4 D5 Expoxy pGe pGivesBound radixMoreThanZERO.
Admitted.

End AlgoS1.

Section AlgoS2.

Variable radix : Z.
Variable b : Fbound.
Variables t:nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypotheses pGe: (4 <= t).

Variables x y p q hx tx p' q' hy ty x1y1 x1y2 x2y1 x2y2 r t1 t2 t3 t4:float.

Hypothesis Cx: (Fsubnormal radix b x).
Hypothesis Cy: (Fnormal radix b y).

Hypothesis Expoxy: (-dExp b <= Fexp x+Fexp y)%Z.

Let s:= t- Nat.div2 t.

Hypothesis A1: (Closest b radix (x*((powerRZ radix s)+1))%R p).
Hypothesis A2: (Closest b radix (x-p)%R  q).
Hypothesis A3: (Closest b radix (q+p)%R hx).
Hypothesis A4: (Closest b radix (x-hx)%R tx).

Hypothesis B1: (Closest b radix (y*((powerRZ radix s)+1))%R p').
Hypothesis B2: (Closest b radix (y-p')%R  q').
Hypothesis B3: (Closest b radix (q'+p')%R hy).
Hypothesis B4: (Closest b radix (y-hy)%R ty).

Hypothesis C1: (Closest b radix (hx*hy)%R  x1y1).
Hypothesis C2: (Closest b radix (hx*ty)%R  x1y2).
Hypothesis C3: (Closest b radix (tx*hy)%R  x2y1).
Hypothesis C4: (Closest b radix (tx*ty)%R  x2y2).

Hypothesis D1: (Closest b radix (x*y)%R  r).
Hypothesis D2: (Closest b radix (r-x1y1)%R  t1).
Hypothesis D3: (Closest b radix (t1-x1y2)%R  t2).
Hypothesis D4: (Closest b radix (t2-x2y1)%R  t3).
Hypothesis D5: (Closest b radix (t3-x2y2)%R  t4).

Theorem DekkerS2: (radix=2)%Z \/ (Nat.Even t) ->  (x*y=r-t4)%R.
Proof using A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 Cx Cy D1 D2 D3 D4 D5 Expoxy pGe pGivesBound radixMoreThanZERO.
Admitted.

End AlgoS2.

Section Algo1.

Variable radix : Z.
Variable b : Fbound.
Variables t:nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypotheses pGe: (4 <= t).

Variables x y p q hx tx p' q' hy ty x1y1 x1y2 x2y1 x2y2 r t1 t2 t3 t4:float.

Hypothesis Cx: (Fcanonic radix b x).
Hypothesis Cy: (Fcanonic radix b y).

Hypothesis Expoxy: (-dExp b <= Fexp x+Fexp y)%Z.

Let s:= t- Nat.div2 t.

Hypothesis A1: (Closest b radix (x*((powerRZ radix s)+1))%R p).
Hypothesis A2: (Closest b radix (x-p)%R  q).
Hypothesis A3: (Closest b radix (q+p)%R hx).
Hypothesis A4: (Closest b radix (x-hx)%R tx).

Hypothesis B1: (Closest b radix (y*((powerRZ radix s)+1))%R p').
Hypothesis B2: (Closest b radix (y-p')%R  q').
Hypothesis B3: (Closest b radix (q'+p')%R hy).
Hypothesis B4: (Closest b radix (y-hy)%R ty).

Hypothesis C1: (Closest b radix (hx*hy)%R  x1y1).
Hypothesis C2: (Closest b radix (hx*ty)%R  x1y2).
Hypothesis C3: (Closest b radix (tx*hy)%R  x2y1).
Hypothesis C4: (Closest b radix (tx*ty)%R  x2y2).

Hypothesis D1: (Closest b radix (x*y)%R  r).
Hypothesis D2: (Closest b radix (r-x1y1)%R  t1).
Hypothesis D3: (Closest b radix (t1-x1y2)%R  t2).
Hypothesis D4: (Closest b radix (t2-x2y1)%R  t3).
Hypothesis D5: (Closest b radix (t3-x2y2)%R  t4).

Hypothesis dExpPos: ~(Z_of_N(dExp b)=0)%Z.

Theorem Dekker1: (radix=2)%Z \/ (Nat.Even t) ->  (x*y=r-t4)%R.
Proof using A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 Cx Cy D1 D2 D3 D4 D5 Expoxy dExpPos pGe pGivesBound radixMoreThanOne.
Admitted.

End Algo1.
Section Algo2.

Variable radix : Z.
Variable b : Fbound.
Variables t:nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypotheses pGe: (4 <= t).
Let s:= t- Nat.div2 t.

Variables x y:float.

Let b' := Bound (vNum b) (Nplus (N.double (dExp b)) (N.double  (Npos (P_of_succ_nat t)))).

Theorem Veltkampb': forall (f pf qf hf tf:float),
  (dExp b < dExp b')%Z ->
  (Fbounded b f) ->
  Closest b radix (f * (powerRZ radix s + 1)) pf -> Closest b radix (f - pf) qf ->
  Closest b radix (qf + pf) hf -> Closest b radix (f - hf) tf ->
  Closest b' radix (f * (powerRZ radix s + 1)) pf /\
  Closest b' radix (f - pf) qf /\ Closest b' radix (qf + pf) hf /\
  Closest b' radix (f - hf) tf.
Proof using pGe pGivesBound radixMoreThanZERO.
Admitted.

Variables p q hx tx p' q' hy ty x1y1 x1y2 x2y1 x2y2 r t1 t2 t3 t4:float.

Hypothesis Cx: (Fcanonic radix b x).
Hypothesis Cy: (Fcanonic radix b y).

Hypothesis Expoxy: (Fexp x+Fexp y < -dExp b)%Z.

Hypothesis A1: (Closest b radix (x*((powerRZ radix s)+1))%R p).
Hypothesis A2: (Closest b radix (x-p)%R  q).
Hypothesis A3: (Closest b radix (q+p)%R hx).
Hypothesis A4: (Closest b radix (x-hx)%R tx).

Hypothesis B1: (Closest b radix (y*((powerRZ radix s)+1))%R p').
Hypothesis B2: (Closest b radix (y-p')%R  q').
Hypothesis B3: (Closest b radix (q'+p')%R hy).
Hypothesis B4: (Closest b radix (y-hy)%R ty).

Hypothesis C1: (Closest b radix (hx*hy)%R  x1y1).
Hypothesis C2: (Closest b radix (hx*ty)%R  x1y2).
Hypothesis C3: (Closest b radix (tx*hy)%R  x2y1).
Hypothesis C4: (Closest b radix (tx*ty)%R  x2y2).

Hypothesis D1: (Closest b radix (x*y)%R  r).
Hypothesis D2: (Closest b radix (r-x1y1)%R  t1).
Hypothesis D3: (Closest b radix (t1-x1y2)%R  t2).
Hypothesis D4: (Closest b radix (t2-x2y1)%R  t3).
Hypothesis D5: (Closest b radix (t3-x2y2)%R  t4).

Theorem dExpPrim: (dExp b < dExp b')%Z.
Proof using pGe s.
Admitted.

Theorem dExpPrimEq: (Z_of_N (N.double (dExp b) + Npos (xO (P_of_succ_nat t)))
   =2*(dExp b)+2*t+2)%Z.
Proof using pGe.
Admitted.

Theorem NormalbPrim: forall (f:float), Fcanonic radix b f -> (FtoRradix f <>0) ->
   (exists f':float, (Fnormal radix b' f') /\ FtoRradix f'=f /\ (-t-dExp b <= Fexp f')%Z).
Proof using pGe pGivesBound radixMoreThanZERO.
Admitted.

Theorem Dekker2_aux:
  (FtoRradix x <>0) -> (FtoRradix y <>0) ->
  (radix=2)%Z \/ (Nat.Even t) ->  (Rabs (x*y-(r-t4)) <= (7/2)*powerRZ radix (-(dExp b)))%R.
Proof using A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 Cx Cy D1 D2 D3 D4 D5 pGe pGivesBound radixMoreThanZERO.
Admitted.

Theorem Dekker2:
  (radix=2)%Z \/ (Nat.Even t) ->  (Rabs (x*y-(r-t4)) <= (7/2)*powerRZ radix (-(dExp b)))%R.
Proof using A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 Cx Cy D1 D2 D3 D4 D5 pGe pGivesBound radixMoreThanZERO.
Admitted.

End Algo2.

Section AlgoT.

Variable radix : Z.
Variable b : Fbound.
Variables t:nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound: Zpos (vNum b)=(Zpower_nat radix t).
Hypotheses pGe: (4 <= t).

Variables x y p q hx tx p' q' hy ty x1y1 x1y2 x2y1 x2y2 r t1 t2 t3 t4:float.

Hypothesis Cx: (Fcanonic radix b x).
Hypothesis Cy: (Fcanonic radix b y).

Let s:= t- Nat.div2 t.

Hypothesis A1: (Closest b radix (x*((powerRZ radix s)+1))%R p).
Hypothesis A2: (Closest b radix (x-p)%R  q).
Hypothesis A3: (Closest b radix (q+p)%R hx).
Hypothesis A4: (Closest b radix (x-hx)%R tx).

Hypothesis B1: (Closest b radix (y*((powerRZ radix s)+1))%R p').
Hypothesis B2: (Closest b radix (y-p')%R  q').
Hypothesis B3: (Closest b radix (q'+p')%R hy).
Hypothesis B4: (Closest b radix (y-hy)%R ty).

Hypothesis C1: (Closest b radix (hx*hy)%R  x1y1).
Hypothesis C2: (Closest b radix (hx*ty)%R  x1y2).
Hypothesis C3: (Closest b radix (tx*hy)%R  x2y1).
Hypothesis C4: (Closest b radix (tx*ty)%R  x2y2).

Hypothesis D1: (Closest b radix (x*y)%R  r).
Hypothesis D2: (Closest b radix (-r+x1y1)%R  t1).
Hypothesis D3: (Closest b radix (t1+x1y2)%R  t2).
Hypothesis D4: (Closest b radix (t2+x2y1)%R  t3).
Hypothesis D5: (Closest b radix (t3+x2y2)%R  t4).

Hypothesis dExpPos: ~(Z_of_N (dExp b)=0)%Z.

Theorem Dekker: (radix=2)%Z \/ (Nat.Even t) ->
  ((-dExp b <= Fexp x+Fexp y)%Z ->  (x*y=r+t4)%R) /\
    (Rabs (x*y-(r+t4)) <= (7/2)*powerRZ radix (-(dExp b)))%R.
Proof using A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 Cx Cy D1 D2 D3 D4 D5 dExpPos pGe pGivesBound radixMoreThanOne.
Admitted.

End AlgoT.

Section Discriminant1.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.

Variables a b b' c p q d:float.

Let delta := (Rabs (d-(b*b'-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fb': (Fbounded bo b').
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).

Hypothesis U1:(- dExp bo <= Fexp d - 1)%Z.
Hypothesis Nd:(Fnormal radix bo d).
Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Np:(Fnormal radix bo p).

Hypothesis Square:(0 <=b*b')%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b')%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).

Hypothesis Firstcase : (p+q <= 3*(Rabs (p-q)))%R.
Hypothesis Roundd : (EvenClosest bo radix precision (p-q)%R d).

Theorem delta_inf: (delta <= (/2)*(Fulp bo radix precision d)+
   ((/2)*(Fulp bo radix precision p)+(/2)*(Fulp bo radix precision q)))%R.
Proof using Roundd Roundp Roundq pGivesBound precisionGreaterThanOne.
Admitted.

Theorem P_positive: (Rle 0 p)%R.
Proof using Roundp Square pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Fulp_le_twice_l: forall x y:float, (0 <= x)%R ->
   (Fnormal radix bo x) -> (Fbounded bo y) -> (2*x<=y)%R ->
   (2*(Fulp bo radix precision x) <= (Fulp bo radix precision y))%R.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Fulp_le_twice_r: forall x y:float, (0 <= x)%R ->
   (Fnormal radix bo y) -> (Fbounded bo x) -> (x<=2*y)%R ->
   ((Fulp bo radix precision x) <= 2*(Fulp bo radix precision y))%R.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Half_Closest_Round: forall (x:float) (r:R),
   (- dExp bo <= Z.pred (Fexp x))%Z -> (Closest bo radix r x)
  -> (Closest bo radix (r/2)%R (Float (Fnum x) (Z.pred (Fexp x)))).
Proof using .
Admitted.

Theorem Twice_EvenClosest_Round: forall (x:float) (r:R),
   (-(dExp bo) <= (Fexp x)-1)%Z -> (Fnormal radix bo x)
  -> (EvenClosest bo radix precision r x)
  -> (EvenClosest bo radix precision (2*r)%R (Float (Fnum x) (Z.succ (Fexp x)))).
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem EvenClosestMonotone2: forall (p q : R) (p' q' : float),
  (p <= q)%R -> (EvenClosest bo radix precision p p') ->
  (EvenClosest bo radix precision q q') -> (p' <= q')%R.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Fulp_le_twice_r_round: forall (x y:float) (r:R), (0 <= x)%R ->
   (Fbounded bo x) -> (Fnormal radix bo y) -> (- dExp bo <= Fexp y - 1)%Z
     -> (x<=2*r)%R ->
   (EvenClosest bo radix precision r y) ->
   ((Fulp bo radix precision x) <= 2*(Fulp bo radix precision y))%R.
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem discri1: (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Fd Firstcase Fp Fq Nd Np Nq Roundd Roundp Roundq Square U1 pGivesBound precisionGreaterThanOne.
Admitted.

End Discriminant1.

Section Discriminant2.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.

Variables a b b' c p q t dp dq s d:float.

Let delta := (Rabs (d-(b*b'-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fb': (Fbounded bo b').
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Ft : (Fbounded bo t).
Hypothesis Fs : (Fbounded bo s).
Hypothesis Fdp: (Fbounded bo dp).
Hypothesis Fdq: (Fbounded bo dq).
Hypothesis Cs:(Fcanonic radix bo s).

Hypothesis U1: (- dExp bo <= (Fexp t)-1)%Z.
Hypothesis U2: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b'))%R.
Hypothesis U3: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R.

Hypothesis Np:(Fnormal radix bo p).
Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Nd:(Fnormal radix bo d).

Hypothesis Square:(0 <=b*b')%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b')%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).

Hypothesis Secondcase : (3*(Rabs (p-q)) < p+q)%R.

Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis dpEq   : (FtoRradix dp=b*b'-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.
Hypothesis Rounds : (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis Roundd : (EvenClosest bo radix precision (t+s)%R d).

Hypothesis p_differ_q:~(p=q)%R.

Theorem Q_positive: (0 < q)%R.
Proof using Roundp Secondcase Square pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Q_le_two_P: (q <= 2*p)%R.
Proof using Roundp Secondcase Square pGivesBound precisionGreaterThanOne.
Admitted.

Theorem P_le_two_Q: (p <= 2*q)%R.
Proof using Roundp Secondcase Square pGivesBound precisionGreaterThanOne.
Admitted.

Theorem t_exact: (FtoRradix t=p-q)%R.
Proof using Fp Fq Roundp Roundt Secondcase Square pGivesBound precisionGreaterThanOne.
Admitted.

Theorem dp_dq_le: (Rabs (dp-dq) <= (3/2)*(Rmin
    (Fulp bo radix precision p) (Fulp bo radix precision q)))%R.
Proof using Fp Fq Np Nq Roundp Roundq Secondcase Square dpEq dqEq pGivesBound precisionGreaterThanOne.
Admitted.

Theorem EvenClosestFabs :
 forall (f : float) (r : R), (Fcanonic radix bo f)
    -> EvenClosest bo radix precision r f ->
    EvenClosest bo radix precision (Rabs r) (Fabs f).
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem discri2: (3*(Rmin (Fulp bo radix precision p) (Fulp bo radix precision q))
  <= (Rabs (p-q)))%R -> (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Cs Fd Fp Fq Fs Nd Np Nq Roundd Roundp Roundq Rounds Roundt Secondcase Square U1 dpEq dqEq pGivesBound precisionGreaterThanOne.
Admitted.

Theorem discri3: (exists f:float, (Fbounded bo f) /\ (FtoRradix f)=(dp-dq)%R)
    -> (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Fp Fq Roundd Roundp Rounds Roundt Secondcase Square dpEq dqEq pGivesBound precisionGreaterThanOne.
Admitted.

Theorem errorBoundedMultClosest_Can:
       forall f1 f2 g : float,
       Fbounded bo f1 ->
       Fbounded bo f2 ->
       Closest bo radix (f1* f2) g ->
       (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (f1*f2))%R ->
       Fcanonic radix bo g ->
         (exists s : float,
            Fbounded bo s /\
           (FtoRradix s = f1*f2 - g)%R /\
            Fexp s = (Fexp g - precision)%Z /\
            (Rabs (Fnum s) <= powerRZ radix (Z.pred precision))%R).
Proof using pGivesBound precisionGreaterThanOne.
Admitted.

Theorem discri4: (Fexp p)=(Fexp q) -> (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Fa Fb Fb' Fc Fp Fq Np Nq Roundd Roundp Roundq Rounds Roundt Secondcase Square U2 U3 dpEq dqEq pGivesBound precisionGreaterThanOne.
Admitted.

End Discriminant2.

Section Discriminant3.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.

Variables a b b' c p q t dp dq s d:float.

Let delta := (Rabs (d-(b*b'-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fb': (Fbounded bo b').
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Ft : (Fbounded bo t).
Hypothesis Fs : (Fbounded bo s).
Hypothesis Fdp: (Fbounded bo dp).
Hypothesis Fdq: (Fbounded bo dq).
Hypothesis Cs:(Fcanonic radix bo s).

Hypothesis U1: (- dExp bo <= (Fexp d)-1)%Z.
Hypothesis U2: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b'))%R.
Hypothesis U3: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R.

Hypothesis Np:(Fnormal radix bo p).
Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Nd:(Fnormal radix bo d).

Hypothesis Square:(0 <=b*b')%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b')%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).

Hypothesis p_pos:(0 <= p)%R.
Hypothesis q_pos:(0 <= q)%R.

Hypothesis Secondcase : (3*(Rabs (p-q)) < p+q)%R.

Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis dpEq   : (FtoRradix dp=b*b'-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.
Hypothesis Rounds : (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis Roundd : (EvenClosest bo radix precision (t+s)%R d).

Hypothesis p_differ_q:~(p=q)%R.

Variable e:Z.
Hypothesis p_eqF : p=(Float (Zpower_nat radix (pred precision)) (Z.succ e)).
Hypothesis p_eqR : (FtoRradix p)=(powerRZ radix (precision+e)%Z).
Hypothesis q_eqExp : (Fexp q)=e.

Theorem discri5: (0 < dp*dq)%R -> (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Fa Fb Fb' Fc Fp Fq Np Nq Roundd Roundp Roundq Rounds Roundt Secondcase Square U2 U3 dpEq dqEq pGivesBound p_eqF precisionGreaterThanOne q_eqExp.
Admitted.

Theorem discri6: (0< dp)%R -> (dq < 0)%R
    -> (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Cs Fp Fq Fs Nd Np Nq Roundd Roundp Roundq Rounds Roundt Secondcase Square U1 dpEq dqEq pGivesBound p_eqF p_eqR precisionGreaterThanOne q_eqExp.
Admitted.

Theorem discri7: (dp < 0)%R -> (0 < dq)%R
    -> (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Fa Fb Fb' Fc Fp Fq Np Nq Roundd Roundp Roundq Rounds Roundt Secondcase Square U2 U3 dpEq dqEq pGivesBound p_eqF p_eqR precisionGreaterThanOne q_eqExp.
Admitted.

Theorem discri8: (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Cs Fa Fb Fb' Fc Fdp Fdq Fp Fq Fs Nd Np Nq Roundd Roundp Roundq Rounds Roundt Secondcase Square U1 U2 U3 dpEq dqEq pGivesBound p_eqF p_eqR precisionGreaterThanOne q_eqExp.
Admitted.

End Discriminant3.

Section Discriminant4.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.

Variables a b c p q t dp dq s d:float.

Let delta := (Rabs (d-(b*b-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Ft : (Fbounded bo t).
Hypothesis Fs : (3*(Rabs (p-q)) < p+q)%R -> (Fbounded bo s).
Hypothesis Fdp: (3*(Rabs (p-q)) < p+q)%R -> (Fbounded bo dp).
Hypothesis Fdq: (3*(Rabs (p-q)) < p+q)%R -> (Fbounded bo dq).
Hypothesis Cs:(3*(Rabs (p-q)) < p+q)%R -> (Fcanonic radix bo s).

Hypothesis U0: (- dExp bo <= (Fexp d)-1)%Z.
Hypothesis U1: (- dExp bo <= (Fexp t)-1)%Z.
Hypothesis U2: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b))%R.
Hypothesis U3: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R.

Hypothesis Np:(Fnormal radix bo p).
Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Nd:(Fnormal radix bo d).

Hypothesis Roundp : (EvenClosest bo radix precision (b*b)%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).

Hypothesis Firstcase : (p+q <= 3*(Rabs (p-q)))%R ->
   (EvenClosest bo radix precision (p-q)%R d).

Hypothesis SRoundt : (3*(Rabs (p-q)) < p+q)%R -> (EvenClosest bo radix precision (p-q)%R t).
Hypothesis SdpEq   : (3*(Rabs (p-q)) < p+q)%R -> (FtoRradix dp=b*b-p)%R.
Hypothesis SdqEq   : (3*(Rabs (p-q)) < p+q)%R -> (FtoRradix dq=a*c-q)%R.
Hypothesis SRounds : (3*(Rabs (p-q)) < p+q)%R -> (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis SRoundd : (3*(Rabs (p-q)) < p+q)%R -> (EvenClosest bo radix precision (t+s)%R d).

Theorem discri9: (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Cs Fa Fb Fc Fd Fdp Fdq Firstcase Fp Fq Fs Nd Np Nq Roundp Roundq SRoundd SRounds SRoundt SdpEq SdqEq U0 U1 U2 U3 pGivesBound precisionGreaterThanOne.
Admitted.

End Discriminant4.

Section Discriminant1A.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.
Hypothesis precisionGreaterThanThree : 3 <= precision.

Theorem RoundLeNormal: forall f:float, forall r:R,
  Closest bo radix r f -> (Fnormal radix bo f) ->
  (Rabs f <= Rabs r / (1 - powerRZ radix (- precision)))%R.
Proof using pGivesBound precisionGreaterThanOne precisionGreaterThanThree.
Admitted.

Variables a b b' c p q t d u v dp dq:float.

Let delta := (Rabs (d-(b*b'-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fb': (Fbounded bo b').
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Fu : (Fbounded bo u).
Hypothesis Fv : (Fbounded bo v).
Hypothesis Cand : (Fcanonic radix bo d).

Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Np:(Fnormal radix bo p).
Hypothesis Nv:(Fnormal radix bo v).
Hypothesis Nu:(Fnormal radix bo u).
Hypothesis U0: (- dExp bo <= Fexp p - 2)%Z.

Hypothesis Square:(0 <=b*b')%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b')%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).
Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis dDef   : d=t.
Hypothesis Roundu : (EvenClosest bo radix precision (3*Rabs t)%R u).
Hypothesis Roundv : (EvenClosest bo radix precision (p+q)%R v).
Hypothesis dpEq   : (FtoRradix dp=b*b'-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.

Hypothesis Case1 : (3*(Rabs (p-q)) < p+q )%R.
Hypothesis Case2 : (v <= u )%R.

Theorem IneqEq: (FtoRradix v=u)%R.
Proof using Case1 Case2 Fp Fq Fu Roundp Roundt Roundu Roundv Square pGivesBound precisionGreaterThanOne.
Admitted.

Theorem dexact: (FtoRradix d=p-q)%R.
Proof using Case1 Fp Fq Roundp Roundt Square dDef pGivesBound precisionGreaterThanOne.
Admitted.

Theorem discri10: (q <= p)%R -> (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Cand Case1 Case2 Fp Fq Fu Fv Np Nq Nu Nv Roundp Roundq Roundt Roundu Roundv Square U0 dDef dpEq dqEq pGivesBound precisionGreaterThanOne precisionGreaterThanThree.
Admitted.
End Discriminant1A.

Section Discriminant2A.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.
Hypothesis precisionGreaterThanThree : 3 <= precision.

Variables a b b' c p q t d u v dp dq:float.

Let delta := (Rabs (d-(b*b'-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fb': (Fbounded bo b').
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Fu : (Fbounded bo u).
Hypothesis Fv : (Fbounded bo v).
Hypothesis Cand : (Fcanonic radix bo d).

Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Np:(Fnormal radix bo p).
Hypothesis Nv:(Fnormal radix bo v).
Hypothesis Nu:(Fnormal radix bo u).
Hypothesis U0: (- dExp bo <= Fexp p - 2)%Z.
Hypothesis U1: (- dExp bo <= Fexp q - 2)%Z.

Hypothesis Square:(0 <=b*b')%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b')%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).
Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis dDef   : d=t.
Hypothesis Roundu : (EvenClosest bo radix precision (3*Rabs t)%R u).
Hypothesis Roundv : (EvenClosest bo radix precision (p+q)%R v).
Hypothesis dpEq   : (FtoRradix dp=b*b'-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.

Hypothesis Case1 : (3*(Rabs (p-q)) < p+q )%R.
Hypothesis Case2 : (v <= u )%R.

Theorem discri11: (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Cand Case1 Case2 Fp Fq Fu Fv Np Nq Nu Nv Roundp Roundq Roundt Roundu Roundv Square U0 U1 dDef dpEq dqEq pGivesBound precisionGreaterThanOne precisionGreaterThanThree.
Admitted.

End Discriminant2A.

Section Discriminant3A.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.
Hypothesis precisionGreaterThanFour : 4 <= precision.

Variables a b b' c p q t dp dq s d u v:float.

Let delta := (Rabs (d-(b*b'-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fb': (Fbounded bo b').
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Ft : (Fbounded bo t).
Hypothesis Fs : (Fbounded bo s).
Hypothesis Fdp: (u<v)%R -> (Fbounded bo dp).
Hypothesis Fdq: (u<v)%R -> (Fbounded bo dq).

Hypotheses Cv: Fcanonic radix bo v.
Hypothesis Cs:(Fcanonic radix bo s).

Hypothesis U1: (- dExp bo <= (Fexp t)-1)%Z.
Hypothesis U2: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b'))%R.
Hypothesis U3: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R.

Hypothesis Np:(Fnormal radix bo p).
Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Nd:(Fnormal radix bo d).
Hypothesis Nt:(Fnormal radix bo t).
Hypothesis Nu:(Fnormal radix bo u).
Hypothesis Nv:(Fnormal radix bo v).

Hypothesis Square:(0 <=b*b')%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b')%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).
Hypothesis Roundu : (EvenClosest bo radix precision (3*Rabs t)%R u).
Hypothesis Roundv : (EvenClosest bo radix precision (p+q)%R v).

Hypothesis Case1 : (p+q <= 3*(Rabs (p-q)))%R.
Hypothesis Case2 : (u < v )%R.

Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis dpEq   : (FtoRradix dp=b*b'-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.
Hypothesis Rounds : (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis Roundd : (EvenClosest bo radix precision (t+s)%R d).

Theorem RoundGeNormal: forall f:float, forall r:R,
  Closest bo radix r f -> (Fnormal radix bo f) ->
  (Rabs r <= Rabs f * (1 + powerRZ radix (- precision)))%R.
Proof using pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Theorem discri12:  (q <= p)%R -> (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Case1 Case2 Fd Fp Fq Fs Ft Nd Nq Nt Nu Nv Roundd Roundp Roundq Rounds Roundt Roundu Roundv Square U1 dpEq dqEq pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.
End Discriminant3A.

Section Discriminant4A.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.
Hypothesis precisionGreaterThanFour : 4 <= precision.

Variables a b b' c p q t dp dq s d u v:float.

Let delta := (Rabs (d-(b*b'-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fb': (Fbounded bo b').
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Ft : (Fbounded bo t).
Hypothesis Fs : (Fbounded bo s).
Hypothesis Fdp: (u<v)%R -> (Fbounded bo dp).
Hypothesis Fdq: (u<v)%R -> (Fbounded bo dq).

Hypotheses Cv: Fcanonic radix bo v.
Hypotheses Cs: Fcanonic radix bo s.

Hypothesis U1: (- dExp bo <= (Fexp t)-1)%Z.
Hypothesis U2: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b'))%R.
Hypothesis U3: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R.

Hypothesis Np:(Fnormal radix bo p).
Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Nd:(Fnormal radix bo d).
Hypothesis Nt:(Fnormal radix bo t).
Hypothesis Nu:(Fnormal radix bo u).
Hypothesis Nv:(Fnormal radix bo v).

Hypothesis Square:(0 <=b*b')%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b')%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).
Hypothesis Roundu : (EvenClosest bo radix precision (3*Rabs t)%R u).
Hypothesis Roundv : (EvenClosest bo radix precision (p+q)%R v).

Hypothesis Case1 : (p+q <= 3*(Rabs (p-q)))%R.
Hypothesis Case2 : (u < v )%R.

Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis dpEq   : (FtoRradix dp=b*b'-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.
Hypothesis Rounds : (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis Roundd : (EvenClosest bo radix precision (t+s)%R d).

Theorem discri13: (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Case1 Case2 Fd Fp Fq Fs Ft Nd Np Nq Nt Nu Nv Roundd Roundp Roundq Rounds Roundt Roundu Roundv Square U1 dpEq dqEq pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

End Discriminant4A.

Section Discriminant5.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.
Hypothesis precisionGreaterThanFour : 4 <= precision.

Variables a b c p q t dp dq s d u v:float.

Let delta := (Rabs (d-(b*b-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Ft : (Fbounded bo t).
Hypothesis Fs : (u<v)%R -> (Fbounded bo s).
Hypothesis Fdp: (u<v)%R -> (Fbounded bo dp).
Hypothesis Fdq: (u<v)%R -> (Fbounded bo dq).
Hypothesis Fu: (Fbounded bo u).
Hypothesis Fv: (Fbounded bo v).
Hypothesis Cs: (u < v)%R -> (Fcanonic radix bo s).

Hypothesis U0: (- dExp bo <= Fexp d - 1)%Z.
Hypothesis U1: (- dExp bo <= (Fexp t)-1)%Z.
Hypothesis U2: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b))%R.
Hypothesis U3: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R.

Hypothesis Np:(Fnormal radix bo p).
Hypothesis Nq:(Fnormal radix bo q).
Hypothesis Nd:(Fnormal radix bo d).
Hypothesis Nu:(Fnormal radix bo u).
Hypothesis Nv:(Fnormal radix bo v).
Hypothesis Nt:(Fnormal radix bo t).

Hypothesis Roundp : (EvenClosest bo radix precision (b*b)%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).
Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis Roundu : (EvenClosest bo radix precision (3*Rabs t)%R u).
Hypothesis Roundv : (EvenClosest bo radix precision (p+q)%R v).

Hypothesis FRoundd : (v <= u)%R ->
   (EvenClosest bo radix precision (p-q)%R d).

Hypothesis dpEq   : (FtoRradix dp=b*b-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.
Hypothesis SRounds : (u < v)%R -> (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis SRoundd : (u < v)%R -> (EvenClosest bo radix precision (t+s)%R d).

Theorem discri14: (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Cs FRoundd Fa Fb Fc Fd Fdp Fdq Fp Fq Fs Ft Fu Fv Nd Np Nq Nt Nu Nv Roundp Roundq Roundt Roundu Roundv SRoundd SRounds U0 U1 U2 U3 dpEq dqEq pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

End Discriminant5.

Section Discriminant6.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.
Hypothesis precisionGreaterThanFour : 4 <= precision.

Variables a b c p q t dp dq s d u v:float.

Let delta := (Rabs (d-(b*b-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fdp: (u<v)%R -> (Fbounded bo dp).
Hypothesis Fdq: (u<v)%R -> (Fbounded bo dq).

Hypothesis U1: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b))%R.
Hypothesis U2: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R.
Hypothesis U4: (powerRZ radix (-dExp bo+precision) <= Rabs d)%R.
Hypothesis U5: (powerRZ radix (-dExp bo+precision-1) <= Rabs u)%R.
Hypothesis U6: (powerRZ radix (-dExp bo+precision-1) <= Rabs v)%R.
Hypothesis U7: (powerRZ radix (-dExp bo+precision) <= Rabs t)%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b)%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).
Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis Roundu : (EvenClosest bo radix precision (3*Rabs t)%R u).
Hypothesis Roundv : (EvenClosest bo radix precision (p+q)%R v).

Hypothesis FRoundd : (v <= u)%R ->
   (EvenClosest bo radix precision (p-q)%R d).

Hypothesis dpEq   : (FtoRradix dp=b*b-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.
Hypothesis SRounds : (u < v)%R -> (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis SRoundd : (u < v)%R -> (EvenClosest bo radix precision (t+s)%R d).

Theorem discri15: (delta <= 2*(Fulp bo radix precision d))%R.
Proof using FRoundd Fa Fb Fc Fdp Fdq Roundp Roundq Roundt Roundu Roundv SRoundd SRounds U1 U2 U4 U5 U6 U7 dpEq dqEq pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

End Discriminant6.

Section Discriminant7.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.
Hypothesis precisionGreaterThanFour : 4 <= precision.

Theorem FexpGeUnderf: forall e:Z, forall f:float,
  (Fbounded bo f) ->
  ((powerRZ radix e) <= Rabs f)%R -> (e-precision+1 <= Fexp f)%Z.
Proof using pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Theorem AddExpGeUnderf: forall f1:float ,forall f2:float, forall g:float, forall e:Z,
    Closest bo radix (f1+f2) g -> (Fbounded bo f1) -> (Fbounded bo f2)
      ->  (powerRZ radix e <= Rabs f1)%R
      ->  (powerRZ radix e <= Rabs f2)%R
      ->  ((FtoRradix g=0)%R \/ (powerRZ radix (e-precision+1) <= Rabs g)%R).
Proof using pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Theorem AddExpGeUnderf2: forall f1:float ,forall f2:float, forall g:float, forall e:Z,
    Closest bo radix (f1+f2) g -> (Fbounded bo f1) -> (Fbounded bo f2)
      ->  (powerRZ radix e <= Rabs f1)%R
      ->  (powerRZ radix e <= Rabs f2)%R
      ->  (FtoRradix g <>0)%R
      -> (powerRZ radix (e-precision+1) <= Rabs g)%R.
Proof using pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Theorem AddExpGe1Underf: forall f1:float ,forall f2:float, forall g:float, forall e:Z,
    Closest bo radix (f1+f2) g -> (Fcanonic radix bo f1) -> (Fcanonic radix bo f2)
      ->  (powerRZ radix e <= Rabs f1)%R
      ->  (-dExp bo <= e-1)%Z
      ->  ((FtoRradix g=0)%R \/ (powerRZ radix (e-precision) <= Rabs g)%R).
Proof using pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Theorem AddExpGe1Underf2: forall f1:float ,forall f2:float, forall g:float, forall e:Z,
    Closest bo radix (f1+f2) g -> (Fbounded bo f1) -> (Fbounded bo f2)
      ->  (powerRZ radix e <= Rabs f1)%R
      ->  (-dExp bo <= e-1)%Z
      ->  (FtoRradix g <>0)%R
      -> (powerRZ radix (e-precision) <= Rabs g)%R.
Proof using pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Variables a b c p q t dp dq s d u v:float.

Let delta := (Rabs (d-(b*b-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fdp: (u < v)%R -> (Fbounded bo dp).
Hypothesis Fdq: (u < v)%R -> (Fbounded bo dq).

Hypothesis U1: (FtoRradix b=0)%R \/
    (powerRZ radix (-dExp bo+3*precision-1) <= Rabs (b*b))%R.
Hypothesis U2: (a*c=0)%R  \/
  (powerRZ radix (-dExp bo+3*precision-1) <= Rabs (a*c))%R.

Hypothesis Roundp : (EvenClosest bo radix precision (b*b)%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).
Hypothesis Roundt : (EvenClosest bo radix precision (p-q)%R t).
Hypothesis Roundu : (EvenClosest bo radix precision (3*Rabs t)%R u).
Hypothesis Roundv : (EvenClosest bo radix precision (p+q)%R v).

Hypothesis FRoundd : (v <= u)%R ->
   (EvenClosest bo radix precision (p-q)%R d).

Hypothesis dpEq   : (FtoRradix dp=b*b-p)%R.
Hypothesis dqEq   : (FtoRradix dq=a*c-q)%R.
Hypothesis SRounds : (u < v)%R -> (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis SRoundd : (u < v)%R -> (EvenClosest bo radix precision (t+s)%R d).

Theorem pGeUnderf: (FtoRradix b <> 0)%R ->
   (powerRZ radix (-dExp bo+3*precision-1) <= Rabs (p))%R.
Proof using Roundp U1 pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Theorem qGeUnderf: (a*c <> 0)%R ->
(powerRZ radix (-dExp bo+3*precision-1) <= Rabs (q))%R.
Proof using Roundq U2 pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Theorem cases: (FtoRradix b=0)%R \/ (a*c=0)%R
   \/ (FtoRradix d=0)%R \/  (FtoRradix v=0)%R \/ (FtoRradix t=0)%R \/
    ((powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b))%R
     /\ (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R
     /\ (powerRZ radix (-dExp bo+precision) <= Rabs d)%R
     /\ (powerRZ radix (-dExp bo+precision-1) <= Rabs u)%R
     /\ (powerRZ radix (-dExp bo+precision-1) <= Rabs v)%R
     /\ (powerRZ radix (-dExp bo+precision) <= Rabs t)%R).
Proof using FRoundd Roundp Roundq Roundt Roundu Roundv SRoundd SRounds U1 U2 pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.

Theorem discri16: (FtoRradix d=0)%R \/ (delta <= 2*(Fulp bo radix precision d))%R.
Proof using FRoundd Fa Fb Fc Fdp Fdq Roundp Roundq Roundt Roundu Roundv SRoundd SRounds U1 U2 dpEq dqEq pGivesBound precisionGreaterThanFour precisionGreaterThanOne.
Admitted.
End Discriminant7.

Section Discriminant5B.
Variable bo : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix precision.

Variables a b c p q t dp dq s d:float.

Let delta := (Rabs (d-(b*b-a*c)))%R.

Hypothesis Fa : (Fbounded bo a).
Hypothesis Fb : (Fbounded bo b).
Hypothesis Fc : (Fbounded bo c).
Hypothesis Fp : (Fbounded bo p).
Hypothesis Fq : (Fbounded bo q).
Hypothesis Fd : (Fbounded bo d).
Hypothesis Ft : (Fbounded bo t).
Hypothesis Fs : (Fbounded bo s).
Hypothesis Fdp: (Fbounded bo dp).
Hypothesis Fdq: (Fbounded bo dq).

Hypothesis U0: (- dExp bo <= Fexp d - 1)%Z.
Hypothesis U1: (- dExp bo <= (Fexp t)-1)%Z.
Hypothesis U2: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (b*b))%R.
Hypothesis U3: (powerRZ radix (-dExp bo+2*precision-1) <= Rabs (a*c))%R.

Hypothesis Np:(FtoRradix p=0)%R \/ (Fnormal radix bo p).
Hypothesis Nq:(FtoRradix q=0)%R \/ (Fnormal radix bo q).
Hypothesis Ns: (3*(Rabs (p-q)) < p+q)%R -> (FtoRradix s=0)%R \/ (Fnormal radix bo s).
Hypothesis Nd: (Fnormal radix bo d).

Hypothesis Roundp : (EvenClosest bo radix precision (b*b)%R p).
Hypothesis Roundq : (EvenClosest bo radix precision (a*c)%R q).

Hypothesis Firstcase : (p+q <= 3*(Rabs (p-q)))%R ->
   (EvenClosest bo radix precision (p-q)%R d).

Hypothesis SRoundt : (3*(Rabs (p-q)) < p+q)%R -> (EvenClosest bo radix precision (p-q)%R t).
Hypothesis SdpEq   : (3*(Rabs (p-q)) < p+q)%R -> (FtoRradix dp=b*b-p)%R.
Hypothesis SdqEq   : (3*(Rabs (p-q)) < p+q)%R -> (FtoRradix dq=a*c-q)%R.
Hypothesis SRounds : (3*(Rabs (p-q)) < p+q)%R -> (EvenClosest bo radix precision (dp-dq)%R s).
Hypothesis SRoundd : (3*(Rabs (p-q)) < p+q)%R -> (EvenClosest bo radix precision (t+s)%R d).

Theorem discri: (delta <= 2*(Fulp bo radix precision d))%R.
Proof using Fa Fb Fc Fd Fdp Fdq Firstcase Fp Fq Fs Nd Np Nq Ns Roundp Roundq SRoundd SRounds SRoundt SdpEq SdqEq U0 U1 U2 U3 pGivesBound precisionGreaterThanOne.
Admitted.
End Discriminant5B.

Section Fast.
Variable b : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Local Coercion FtoRradix := FtoR radix.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
Variable Iplus : float -> float -> float.
Hypothesis
  IplusCorrect :
    forall p q : float,
    Fbounded b p -> Fbounded b q -> Closest b radix (p + q) (Iplus p q).
Hypothesis IplusSym : forall p q : float, Iplus p q = Iplus q p.
Hypothesis
  IplusOp : forall p q : float, Fopp (Iplus p q) = Iplus (Fopp p) (Fopp q).
Variable Iminus : float -> float -> float.
Hypothesis IminusPlus : forall p q : float, Iminus p q = Iplus p (Fopp q).

Let radixMoreThanOne : (1 < radix)%Z := eq_refl.
Let radixMoreThanZERO : (0 < radix)%Z := eq_refl.

Theorem IminusCorrect :
 forall p q : float,
 Fbounded b p -> Fbounded b q -> Closest b radix (p - q) (Iminus p q).
Proof using IminusPlus IplusCorrect.
Admitted.

Theorem ErrorBoundedIplus :
 forall p q : float,
 Fbounded b p ->
 Fbounded b q ->
 exists error : float, error = (p + q - Iplus p q)%R :>R /\ Fbounded b error.
Proof using IplusCorrect pGivesBound precisionGreaterThanOne.
Admitted.

Theorem IplusOr :
 forall p q : float,
 Fbounded b p -> Fbounded b q -> q = 0%R :>R -> Iplus p q = p :>R.
Proof using IplusCorrect.
Admitted.

Theorem IminusId :
 forall p q : float,
 Fbounded b p -> Fbounded b q -> p = q :>R -> Iminus p q = 0%R :>R.
Proof using IminusPlus IplusCorrect.
Admitted.

Theorem IplusBounded :
 forall p q : float, Fbounded b p -> Fbounded b q -> Fbounded b (Iplus p q).
Proof using IplusCorrect.
Admitted.

Theorem IminusBounded :
 forall p q : float, Fbounded b p -> Fbounded b q -> Fbounded b (Iminus p q).
Proof using IminusPlus IplusCorrect.
Admitted.

Theorem MDekkerAux1 :
 forall p q : float,
 Iminus (Iplus p q) p = (Iplus p q - p)%R :>R ->
 Fbounded b p ->
 Fbounded b q -> Iminus q (Iminus (Iplus p q) p) = (p + q - Iplus p q)%R :>R.
Proof using IminusPlus IplusCorrect pGivesBound precisionGreaterThanOne.
Admitted.

Theorem MDekkerAux2 :
 forall p q : float,
 Iplus p q = (p + q)%R :>R ->
 Fbounded b p -> Fbounded b q -> Iminus (Iplus p q) p = (Iplus p q - p)%R :>R.
Proof using IminusPlus IplusCorrect.
Admitted.

Theorem MDekkerAux3 :
 forall p q : float,
 Fbounded b (Fplus radix p q) ->
 Fbounded b p -> Fbounded b q -> Iminus (Iplus p q) p = (Iplus p q - p)%R :>R.
Proof using IminusPlus IplusCorrect.
Admitted.

Theorem MDekkerAux4 :
 forall p q : float,
 Fbounded b (Fminus radix (Iplus p q) p) ->
 Fbounded b p -> Fbounded b q -> Iminus (Iplus p q) p = (Iplus p q - p)%R :>R.
Proof using IminusPlus IplusCorrect.
Admitted.

Theorem Dekker1_FTS :
 forall p q : float,
 (0 <= q)%R ->
 (q <= p)%R ->
 Fbounded b p -> Fbounded b q -> Iminus (Iplus p q) p = (Iplus p q - p)%R :>R.
Proof using IminusPlus IplusCorrect pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Dekker2_FTS :
 forall p q : float,
 (0 <= p)%R ->
 (- q <= p)%R ->
 (p <= radix * - q)%R ->
 Fbounded b p -> Fbounded b q -> Iminus (Iplus p q) p = (Iplus p q - p)%R :>R.
Proof using IminusPlus IplusCorrect.
Admitted.

Theorem Dekker3 :
 forall p q : float,
 (q <= 0)%R ->
 (radix * - q < p)%R ->
 Fbounded b p -> Fbounded b q -> Iminus (Iplus p q) p = (Iplus p q - p)%R :>R.
Proof using IminusPlus IplusCorrect pGivesBound precisionGreaterThanOne.
Admitted.

Theorem MDekkerAux5 :
 forall p q : float,
 Fbounded b p ->
 Fbounded b q ->
 Iminus (Iplus (Fopp p) (Fopp q)) (Fopp p) =
 (Iplus (Fopp p) (Fopp q) - Fopp p)%R :>R ->
 Iminus (Iplus p q) p = (Iplus p q - p)%R :>R.
Proof using IminusPlus IplusOp.
Admitted.

Theorem MDekker :
 forall p q : float,
 Fbounded b p ->
 Fbounded b q ->
 (Rabs q <= Rabs p)%R -> Iminus (Iplus p q) p = (Iplus p q - p)%R :>R.
Proof using IminusPlus IplusCorrect IplusOp pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Dekker_FTS :
 forall p q : float,
 Fbounded b p ->
 Fbounded b q ->
 (Rabs q <= Rabs p)%R ->
 Iminus q (Iminus (Iplus p q) p) = (p + q - Iplus p q)%R :>R.
Proof using IminusPlus IplusCorrect IplusOp pGivesBound precisionGreaterThanOne.
Admitted.
End Fast.

Section GenericA.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.

Hypothesis Evenradix: (Even radix).

Variable a b e x y:float.

Hypothesis eLea: (Rabs e <= /2*Fulp bo radix p a)%R.
Hypothesis eLeb: (Rabs e <= /2*Fulp bo radix p b)%R.
Hypothesis xDef: Closest bo radix (a+b)%R x.
Hypothesis yDef: Closest bo radix (a+b+e)%R y.
Hypothesis Nx: Fnormal radix bo x.
Hypothesis Ny: Fnormal radix bo y.
Hypothesis Cb: Fcanonic radix bo b.
Hypothesis Ca: Fcanonic radix bo a.

Hypothesis Fexpb: (- dExp bo < Fexp b)%Z.

Let Unmoins := (1 - (powerRZ radix (Z.succ (-p)))/2)%R.
Let Unplus  := (1 + (powerRZ radix (Z.succ (-p)))/2)%R.

Lemma UnMoinsPos: (0 < Unmoins)%R.
Proof using bo precisionGreaterThanOne radixMoreThanOne.
Admitted.

Lemma ClosestRoundeLeNormal: forall (z : R) (f : float),
       Closest bo radix z f ->
       Fnormal radix bo f ->
       (Rabs f <= (Rabs z) / Unmoins)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Lemma ClosestRoundeGeNormal: forall (z : R) (f : float),
       Closest bo radix z f ->
       Fnormal radix bo f ->
       (Rabs z <= (Rabs f) * Unplus)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Lemma abeLeab: (Rabs b <= Rabs a)%R -> (2*powerRZ radix (Fexp b) <= Rabs (a+b))%R
               -> (Rabs (a+b) <= Rabs (a+b+e) *4/3)%R.
Proof using Cb eLeb pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Lemma xLe2y_aux1: (Rabs b <= Rabs a)%R -> (powerRZ radix (Fexp b) = Rabs (a+b))%R
              ->  (Rabs x <= 2*Rabs y)%R.
Proof using Cb Evenradix Fexpb eLeb pGivesBound precisionGreaterThanOne radixMoreThanZERO xDef yDef.
Admitted.

Lemma xLe2y_aux2 :  (Rabs b <= Rabs a)%R -> (Rabs x <= 2*Rabs y)%R.
Proof using Ca Cb Evenradix Fexpb Nx Ny Unmoins Unplus eLeb pGivesBound precisionGreaterThanOne radixMoreThanZERO xDef yDef.
Admitted.

Lemma yLe2x_aux : (Rabs b <= Rabs a)%R -> ~(FtoRradix x=0)%R
              -> (Rabs y <= 2*Rabs x)%R.
Proof using Ca Cb Nx Ny Unmoins Unplus eLeb pGivesBound precisionGreaterThanOne radixMoreThanZERO xDef yDef.
Admitted.

End GenericA.

Section GenericB.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.

Hypothesis Evenradix: (Even radix).

Variable a b e x y:float.

Hypothesis eLea: (Rabs e <= /2*Fulp bo radix p a)%R.
Hypothesis eLeb: (Rabs e <= /2*Fulp bo radix p b)%R.
Hypothesis xDef: Closest bo radix (a+b)%R x.
Hypothesis yDef: Closest bo radix (a+b+e)%R y.
Hypothesis Nx: Fnormal radix bo x.
Hypothesis Ny: Fnormal radix bo y.
Hypothesis Cb: Fcanonic radix bo b.
Hypothesis Ca: Fcanonic radix bo a.

Hypothesis Fexpb: (- dExp bo < Fexp b)%Z.
Hypothesis Fexpa: (- dExp bo < Fexp a)%Z.

Hypothesis dsd: ((0<= y)%R -> (0<= x)%R) /\ ((y <= 0)%R -> (x <= 0)%R).

Lemma xLe2y : (Rabs x <= 2*Rabs y)%R.
Proof using Ca Cb Evenradix Fexpa Fexpb Nx Ny eLea eLeb pGivesBound precisionGreaterThanOne radixMoreThanOne xDef yDef.
Admitted.

Lemma yLe2x: ~(FtoRradix x=0)%R -> (Rabs y <= 2*Rabs x)%R.
Proof using Ca Cb Nx Ny eLea eLeb pGivesBound precisionGreaterThanOne radixMoreThanOne xDef yDef.
Admitted.

Lemma Subexact: exists v:float, (FtoRradix v=x-y)%R /\ (Fbounded bo v) /\
        (Fexp v=Z.min (Fexp x) (Fexp y))%Z.
Proof using Ca Cb Evenradix Fexpa Fexpb Nx Ny dsd eLea eLeb pGivesBound precisionGreaterThanOne radixMoreThanZERO xDef yDef.
Admitted.

End GenericB.

Section GenericC.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 1 < p.
Hypothesis Evenradix: (Even radix).

Lemma LSB_Pred: forall x y:float,
    (Rabs x < Rabs y)%R -> (LSB radix x <= LSB radix y)%Z
       -> (Rabs x <= Rabs y - powerRZ radix (LSB radix x))%R.
Proof using bo precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Variables x1 x2 y f:float.
Hypothesis x1Def: Closest bo radix (x1+x2)%R x1.
Hypothesis fDef : Closest bo radix (x1+x2+y)%R f.
Hypothesis yLe:  (MSB radix y < LSB radix x2)%Z.
Hypothesis Nx1: Fnormal radix bo x1.
Hypothesis x1Pos: (0 < x1)%R.
Hypothesis x2NonZero: ~(FtoRradix x2 =0)%R.
Hypothesis x1Exp: (-dExp bo < Fexp x1)%Z.

Lemma Midpoint_aux_aux:
    (FtoRradix x1= f) \/ (exists v:float, (FtoRradix v=x2)%R /\ (Fexp x1 -2 <= Fexp v)%Z).
Proof using Evenradix Nx1 fDef pGivesBound precisionGreaterThanOne radixMoreThanZERO x1Def x1Exp x1Pos x2NonZero yLe.
Admitted.

End GenericC.

Section GenericD.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 1 < p.
Hypothesis Evenradix: (Even radix).

Variables x1 x2 y f:float.
Hypothesis x1Def: Closest bo radix (x1+x2)%R x1.
Hypothesis fDef : Closest bo radix (x1+x2+y)%R f.
Hypothesis yLe:  (MSB radix y < LSB radix x2)%Z.
Hypothesis Nx1: Fnormal radix bo x1.
Hypothesis x2NonZero: ~(FtoRradix x2 =0)%R.
Hypothesis x1Exp: (-dExp bo < Fexp x1)%Z.

Lemma Midpoint_aux:
    (FtoRradix x1= f) \/ (exists v:float, (FtoRradix v=x2)%R /\ (Fexp x1 -2 <= Fexp v)%Z).
Proof using Evenradix Nx1 fDef pGivesBound precisionGreaterThanOne radixMoreThanOne x1Def x1Exp x2NonZero yLe.
Admitted.

End GenericD.

Section Be2Zero.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.
Hypothesis Evenradix: (Even radix).

Theorem TwoSumProp: forall (a b x y:float),
  (Fbounded bo a) ->
  (Closest bo radix (a+b)%R x) -> (FtoRradix y=a+b-x)%R
  -> (Rabs y <= Rabs b)%R.
Proof using .
Admitted.

Variable a x y r1 u1 u2 al1 al2 be1 be2 gat ga :float.

Hypothesis Fa : Fbounded bo a.
Hypothesis Fx : Fbounded bo x.
Hypothesis Fy : Fbounded bo y.

Hypothesis Nbe1:  Fnormal radix bo be1.
Hypothesis Nr1 :  Fnormal radix bo r1.
Hypothesis Cal1:  Fcanonic radix bo al1.
Hypothesis Cu1 :  Fcanonic radix bo u1.
Hypothesis Exp1:  (- dExp bo < Fexp al1)%Z.
Hypothesis Exp2:  (- dExp bo < Fexp u1)%Z.

Hypothesis r1Def: (Closest bo radix (a*x+y)%R r1).
Hypothesis u1Def: (Closest bo radix (a*x)%R u1).
Hypothesis u2Def: (FtoRradix u2=a*x-u1)%R.
Hypothesis al1Def:(Closest bo radix (y+u2)%R al1).
Hypothesis al2Def:(FtoRradix al2=y+u2-al1)%R.
Hypothesis be1Def:(Closest bo radix (u1+al1)%R be1).
Hypothesis be2Def:(FtoRradix be2=u1+al1-be1)%R.
Hypothesis gatDef:(Closest bo radix (be1-r1)%R gat).
Hypothesis gaDef: (Closest bo radix (gat+be2)%R ga).

Lemma gatCorrect: exists v:float, (FtoRradix v=be1-r1)%R /\ (Fbounded bo v)
                     /\ (Fexp v=Z.min (Fexp be1) (Fexp r1))%Z.
Proof using Cal1 Cu1 Evenradix Exp1 Exp2 Fy Nbe1 Nr1 al1Def al2Def be1Def pGivesBound precisionGreaterThanOne r1Def radixMoreThanOne u1Def u2Def.
Admitted.

Hypothesis Be2Zero: (FtoRradix be2=0)%R.

Theorem FmaErr_aux1: (a*x+y=r1+ga+al2)%R.
Proof using Be2Zero Cal1 Cu1 Evenradix Exp1 Exp2 Fy Nbe1 Nr1 al1Def al2Def be1Def be2Def gaDef gatDef pGivesBound precisionGreaterThanOne r1Def radixMoreThanOne u1Def u2Def.
Admitted.

End Be2Zero.

Section Be2NonZero.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.
Hypothesis Evenradix: (Even radix).

Variable P: R -> float -> Prop.
Hypothesis P1: forall (r:R) (f:float), (P r f) -> (Closest bo radix r f).
Hypothesis P2: forall (r1 r2:R) (f1 f2:float),
     (P r1 f1) -> (P r2 f2) -> (r1=r2)%R -> (FtoRradix f1=f2)%R.

Variable a x y r1 u1 u2 al1 al2 be1 be2 gat ga :float.

Hypothesis Fa : Fbounded bo a.
Hypothesis Fx : Fbounded bo x.
Hypothesis Fy : Fbounded bo y.

Hypothesis Nbe1:  Fnormal radix bo be1.
Hypothesis Nr1 :  Fnormal radix bo r1.
Hypothesis Cal1:  Fcanonic radix bo al1.
Hypothesis Cu1 :  Fcanonic radix bo u1.
Hypothesis Exp1:  (- dExp bo < Fexp al1)%Z.
Hypothesis Exp2:  (- dExp bo < Fexp u1)%Z.
Hypothesis Exp3:  (- dExp bo+1 < Fexp be1)%Z.

Hypothesis r1Def: (Closest bo radix (a*x+y)%R r1).
Hypothesis u1Def: (Closest bo radix (a*x)%R u1).
Hypothesis u2Def: (FtoRradix u2=a*x-u1)%R.
Hypothesis al1Def:(Closest bo radix (y+u2)%R al1).
Hypothesis al2Def:(FtoRradix al2=y+u2-al1)%R.
Hypothesis be1Def:(Closest bo radix (u1+al1)%R be1).
Hypothesis be2Def:(FtoRradix be2=u1+al1-be1)%R.
Hypothesis gatDef:(Closest bo radix (be1-r1)%R gat).
Hypothesis gaDef: (Closest bo radix (gat+be2)%R ga).
Hypothesis be2Bounded: Fbounded bo be2.

Hypothesis r1DefE: (P (a*x+y)%R r1).
Hypothesis be1DefE:(P (u1+al1)%R be1).

Lemma Expr1 : (Fexp r1 <= Fexp be1+1)%Z.
Proof using Cal1 Cu1 Exp3 Fy Nbe1 Nr1 al1Def al2Def be1Def pGivesBound precisionGreaterThanOne r1Def radixMoreThanOne u1Def u2Def.
Admitted.

Lemma Expbe1: (Fexp be1 <= Fexp r1+1)%Z.
Proof using Cal1 Cu1 Evenradix Exp1 Exp2 Fy Nbe1 Nr1 al1Def al2Def be1Def pGivesBound precisionGreaterThanOne r1Def radixMoreThanOne u1Def u2Def.
Admitted.

Lemma Zmin_Zlt : forall z1 z2 z3 : Z,
       (z1 < z2)%Z -> (z1 < z3)%Z -> (z1 < Z.min z2 z3)%Z.
Proof using .
Admitted.

Hypothesis Be2NonZero: ~(FtoRradix be2=0)%R.

Lemma be2MuchSmaller:
  ~(FtoRradix al2=0)%R -> ~(FtoRradix u2=0)%R ->
  (MSB radix al2 < LSB radix be2)%Z.
Proof using Be2NonZero Cal1 Cu1 Fy al1Def al2Def be1Def be2Def pGivesBound precisionGreaterThanOne radixMoreThanZERO u1Def u2Def.
Admitted.

Lemma gaCorrect: exists v:float, (FtoRradix v=be1-r1+be2)%R /\ (Fbounded bo v).
Proof using Be2NonZero Cal1 Cu1 Evenradix Exp1 Exp2 Exp3 Fy Nbe1 Nr1 P2 al1Def al2Def be1Def be1DefE be2Bounded be2Def pGivesBound precisionGreaterThanOne r1Def r1DefE radixMoreThanZERO u1Def u2Def.
Admitted.

Theorem FmaErr_aux2: (a*x+y=r1+ga+al2)%R.
Proof using Be2NonZero Cal1 Cu1 Evenradix Exp1 Exp2 Exp3 Fy Nbe1 Nr1 P2 al1Def al2Def be1Def be1DefE be2Bounded be2Def gaDef gatDef pGivesBound precisionGreaterThanOne r1Def r1DefE radixMoreThanZERO u1Def u2Def.
Admitted.

End Be2NonZero.

Section Final.

Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.
Hypothesis Evenradix: (Even radix).

Variable P: R -> float -> Prop.
Hypothesis P1: forall (r:R) (f:float), (P r f) -> (Closest bo radix r f).
Hypothesis P2: forall (r1 r2:R) (f1 f2:float),
     (P r1 f1) -> (P r2 f2) -> (r1=r2)%R -> (FtoRradix f1=f2)%R.

Variable a x y r1 u1 u2 al1 al2 be1 be2 gat ga :float.

Hypothesis Fa : Fbounded bo a.
Hypothesis Fx : Fbounded bo x.
Hypothesis Fy : Fbounded bo y.

Hypothesis Nbe1:  Fnormal radix bo be1.
Hypothesis Nr1 :  Fnormal radix bo r1.
Hypothesis Cal1:  Fcanonic radix bo al1.
Hypothesis Cu1 :  Fcanonic radix bo u1.
Hypothesis Exp1:  (- dExp bo < Fexp al1)%Z.
Hypothesis Exp2:  (- dExp bo < Fexp u1)%Z.
Hypothesis Exp3:  (- dExp bo+1 < Fexp be1)%Z.

Hypothesis r1Def: (Closest bo radix (a*x+y)%R r1).
Hypothesis u1Def: (Closest bo radix (a*x)%R u1).
Hypothesis u2Def: (FtoRradix u2=a*x-u1)%R.
Hypothesis al1Def:(Closest bo radix (y+u2)%R al1).
Hypothesis al2Def:(FtoRradix al2=y+u2-al1)%R.
Hypothesis be1Def:(Closest bo radix (u1+al1)%R be1).
Hypothesis be2Def:(FtoRradix be2=u1+al1-be1)%R.
Hypothesis gatDef:(Closest bo radix (be1-r1)%R gat).
Hypothesis gaDef: (Closest bo radix (gat+be2)%R ga).
Hypothesis be2Bounded: Fbounded bo be2.

Hypothesis r1DefE: (P (a*x+y)%R r1).
Hypothesis be1DefE:(P (u1+al1)%R be1).

Theorem FmaErr_aux: (a*x+y=r1+ga+al2)%R.
Proof using Cal1 Cu1 Evenradix Exp1 Exp2 Exp3 Fy Nbe1 Nr1 P2 al1Def al2Def be1Def be1DefE be2Bounded be2Def gaDef gatDef pGivesBound precisionGreaterThanOne r1Def r1DefE radixMoreThanOne u1Def u2Def.
Admitted.
End Final.

Section Final2.

Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.
Hypothesis Evenradix: (Even radix).

Lemma ClosestZero1: forall (r:R) (f g:float), (Closest bo radix r f) -> (FtoRradix f=0)%R ->
   (r=g)%R -> (-dExp bo <= Fexp g)%Z -> (r=0)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Lemma ClosestZero2: forall (r:R) (x:float),
  (Closest bo radix r x) -> (r=0)%R -> (FtoRradix x=0)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanOne.
Admitted.

Lemma LeExpRound: forall f g:float, Closest bo radix f g
          -> exists g':float, Fbounded bo g' /\ FtoRradix g'=g /\ (Fexp f <= Fexp g')%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Lemma LeExpRound2: forall (n:Z) (f g:float), Closest bo radix f g
          -> (n <= Fexp f)%Z
          -> exists g':float, Fbounded bo g' /\ FtoRradix g'=g /\ (n <= Fexp g')%Z.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Variable P: R -> float -> Prop.
Hypothesis P1: forall (r:R) (f:float), (P r f) -> (Closest bo radix r f).
Hypothesis P2: forall (r1 r2:R) (f1 f2:float),
     (P r1 f1) -> (P r2 f2) -> (r1=r2)%R -> (FtoRradix f1=f2)%R.

Variable a x y r1 u1 u2 al1 al2 be1 be2 gat ga :float.

Hypothesis Fa : Fbounded bo a.
Hypothesis Fx : Fbounded bo x.
Hypothesis Fy : Fbounded bo y.

Hypothesis Nbe1:  Fcanonic radix bo be1.
Hypothesis Nr1 :  Fcanonic radix bo r1.
Hypothesis Cal1:  Fcanonic radix bo al1.
Hypothesis Cu1 :  Fcanonic radix bo u1.
Hypothesis Exp1:  (- dExp bo < Fexp al1)%Z  \/ (FtoRradix al1=0)%R.
Hypothesis Exp2:  (- dExp bo < Fexp u1)%Z   \/ (FtoRradix u1=0)%R.
Hypothesis Exp3:  (- dExp bo+1 < Fexp be1)%Z\/ (FtoRradix be1=0)%R.
Hypothesis Exp4:  (Fnormal radix bo r1)   \/ (FtoRradix r1=0)%R.
Hypothesis Exp5:  (-dExp bo <= Fexp a+Fexp x)%Z.

Hypothesis u1Def: (Closest bo radix (a*x)%R u1).
Hypothesis u2Def: (FtoRradix u2=a*x-u1)%R.
Hypothesis al1Def:(Closest bo radix (y+u2)%R al1).
Hypothesis al2Def:(FtoRradix al2=y+u2-al1)%R.
Hypothesis be2Def:(FtoRradix be2=u1+al1-be1)%R.
Hypothesis gatDef:(Closest bo radix (be1-r1)%R gat).
Hypothesis gaDef: (Closest bo radix (gat+be2)%R ga).
Hypothesis r1DefE: (P (a*x+y)%R r1).
Hypothesis be1DefE:(P (u1+al1)%R be1).

Theorem FmaErr: (a*x+y=r1+ga+al2)%R.
Proof using Cal1 Cu1 Evenradix Exp1 Exp2 Exp3 Exp4 Exp5 Fa Fx Fy Nbe1 P1 P2 al1Def al2Def be1DefE be2Def gaDef gatDef pGivesBound precisionGreaterThanOne r1DefE radixMoreThanZERO u1Def u2Def.
Admitted.

Theorem Fma_FTS: (exists ga_e:float, exists al2_e:float,
                 (FtoRradix ga_e=ga)%R /\  (FtoRradix al2_e=al2)%R
                  /\ (Fbounded bo ga_e) /\ (Fbounded bo al2_e) /\
                   (Fexp al2_e <= Fexp ga_e)%Z).
Proof using Exp5 Fa Fx Fy P1 al1Def al2Def be1DefE be2Def gaDef gatDef pGivesBound precisionGreaterThanOne r1DefE radixMoreThanZERO u1Def u2Def.
Admitted.

End Final2.

Section tBounded.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.

Variables a x b ph pl uh z:float.

Hypothesis Fb:  Fbounded bo b.
Hypothesis Fa:  Fbounded bo a.
Hypothesis Fx:  Fbounded bo x.
Hypothesis Cb:  Fcanonic radix bo b.
Hypothesis Nph: Fnormal radix bo ph.
Hypothesis Nz:  Fnormal radix bo z.
Hypothesis Nuh: Fnormal radix bo uh.

Hypothesis Exp1: (- dExp bo <= Fexp a+Fexp x)%Z.

Hypothesis zDef : Closest bo radix (a*x+b)%R z.
Hypothesis phDef: Closest bo radix (a*x)%R ph.
Hypothesis plDef: (FtoRradix pl=a*x-ph)%R.
Hypothesis uhDef: Closest bo radix (ph+b)%R uh.
Hypothesis Posit: (0 <= a*x+b)%R.

Lemma zPos: (0 <= z)%R.
Proof using Posit pGivesBound precisionGreaterThanOne radixMoreThanOne zDef.
Admitted.

Lemma uhPos: (0 <= uh)%R.
Proof using Fb Posit pGivesBound phDef precisionGreaterThanOne radixMoreThanOne uhDef.
Admitted.

Theorem tBounded_aux: exists v:float, Fbounded bo v /\ (FtoRradix v=uh-z)%R.
Proof using Cb Exp1 Fa Fb Fx Nph Nuh Nz Posit pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO uhDef zDef.
Admitted.

End tBounded.

Section tBounded2.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.

Variables a x b ph pl uh z:float.

Hypothesis Fb:  Fbounded bo b.
Hypothesis Fa:  Fbounded bo a.
Hypothesis Fx:  Fbounded bo x.
Hypothesis Cb:  Fcanonic radix bo b.
Hypothesis Nph: Fnormal radix bo ph \/ (FtoRradix ph=0).
Hypothesis Nz:  Fnormal radix bo z  \/ (FtoRradix z =0).
Hypothesis Nuh: Fnormal radix bo uh \/ (FtoRradix uh=0).

Hypothesis Exp1: (- dExp bo <= Fexp a+Fexp x)%Z.

Hypothesis zDef : Closest bo radix (a*x+b)%R z.
Hypothesis phDef: Closest bo radix (a*x)%R ph.
Hypothesis plDef: (FtoRradix pl=a*x-ph)%R.
Hypothesis uhDef: Closest bo radix (ph+b)%R uh.

Theorem tBounded: exists v:float, Fbounded bo v /\ (FtoRradix v=uh-z)%R.
Proof using Cb Exp1 Fa Fb Fx Nph Nuh Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO uhDef zDef.
Admitted.

End tBounded2.

Section uhExact.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 3 <= p.

Variables a x b ph pl uh ul z t v w:float.

Hypothesis Fb:  Fbounded bo b.
Hypothesis Fa:  Fbounded bo a.
Hypothesis Fx:  Fbounded bo x.
Hypothesis Cb:  Fcanonic radix bo b.
Hypothesis Nph: Fnormal radix bo ph \/ (FtoRradix ph=0).
Hypothesis Nuh: Fnormal radix bo uh \/ (FtoRradix uh=0).

Hypothesis Nz:  Fnormal radix bo z  \/ (FtoRradix z=0).
Hypothesis Nw:  Fnormal radix bo w  \/ (FtoRradix w=0).
Hypothesis Fpl: Fbounded bo pl.

Hypothesis Exp1: (- dExp bo <= Fexp a+Fexp x)%Z.

Hypothesis zDef : Closest bo radix (a*x+b)%R z.
Hypothesis phDef: Closest bo radix (a*x)%R ph.
Hypothesis plDef: (FtoRradix pl=a*x-ph)%R.
Hypothesis uhDef: Closest bo radix (ph+b)%R uh.
Hypothesis ulDef: (FtoRradix ul=ph+b-uh)%R.
Hypothesis tDef : Closest bo radix (uh-z)%R t.
Hypothesis vDef : Closest bo radix (pl+ul)%R v.
Hypothesis wDef : Closest bo radix (t+v)%R w.

Hypothesis Case1:(FtoRradix ul=0)%R.

Theorem ErrFmaApprox_1_aux:
   Fnormal radix bo z -> Fnormal radix bo w ->
   (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
Proof using Case1 Cb Exp1 Fa Fb Fpl Fx Nph Nuh Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanOne tDef uhDef ulDef vDef wDef zDef.
Admitted.

Theorem ErrFmaApprox_1: (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
Proof using Case1 Cb Exp1 Fa Fb Fpl Fx Nph Nuh Nw Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO tDef uhDef ulDef vDef wDef zDef.
Admitted.

End uhExact.

Section uhInexact.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 4 <= p.

Lemma RleRoundedAbs: forall (f:float) (r:R), (Closest bo radix r f) ->
  (Fnormal radix bo f) -> (-(dExp bo) < Fexp f)%Z ->
  ((powerRZ radix (p - 1) + - / (2 * radix)) * powerRZ radix (Fexp f) <= Rabs r)%R.
Proof using pGivesBound precisionGreaterThanOne radixMoreThanZERO.
Admitted.

Variables a x b ph pl uh ul z t v w:float.

Hypothesis Fb:  Fbounded bo b.
Hypothesis Fa:  Fbounded bo a.
Hypothesis Fx:  Fbounded bo x.
Hypothesis Cb:  Fcanonic radix bo b.
Hypothesis Nph: Fnormal radix bo ph.
Hypothesis Nuh: Fnormal radix bo uh.

Hypothesis Nz:  Fnormal radix bo z.
Hypothesis Nw:  Fnormal radix bo w.
Hypothesis Nv:  Fnormal radix bo v.

Hypothesis Exp1: (- dExp bo <= Fexp a+Fexp x)%Z.

Hypothesis zDef : Closest bo radix (a*x+b)%R z.
Hypothesis phDef: Closest bo radix (a*x)%R ph.
Hypothesis plDef: (FtoRradix pl=a*x-ph)%R.
Hypothesis uhDef: Closest bo radix (ph+b)%R uh.
Hypothesis ulDef: (FtoRradix ul=ph+b-uh)%R.
Hypothesis tDef : Closest bo radix (uh-z)%R t.
Hypothesis vDef : Closest bo radix (pl+ul)%R v.
Hypothesis wDef : Closest bo radix (t+v)%R w.

Hypothesis Case2: ~(FtoRradix ul=0)%R.

Lemma LeExp1: (Fexp ph <= Fexp uh+1)%Z.
Proof using Case2 Fb Nph pGivesBound precisionGreaterThanOne radixMoreThanOne uhDef ulDef.
Admitted.

Lemma LeExp2: (Fexp uh <= Fexp z+1)%Z.
Proof using Case2 Fb Nph Nuh Nz pGivesBound phDef precisionGreaterThanOne radixMoreThanZERO uhDef ulDef zDef.
Admitted.

Lemma LeExp3:  (Fexp ph = Fexp uh+1)%Z -> (Fexp uh = Fexp z+1)%Z -> False.
Proof using Case2 Fb Nph Nz pGivesBound phDef precisionGreaterThanOne radixMoreThanZERO uhDef ulDef zDef.
Admitted.

Lemma LeExp: (powerRZ radix (Fexp ph)+powerRZ radix (Fexp uh) <= 2*powerRZ radix (Fexp z+1))%R.
Proof using Case2 Fb Nph Nuh Nz pGivesBound phDef precisionGreaterThanOne radixMoreThanZERO uhDef ulDef zDef.
Admitted.

Lemma vLe_aux: (Rabs (pl+ul) <= powerRZ radix (Fexp z)*radix)%R.
Proof using Case2 Fb Nph Nuh Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO uhDef ulDef zDef.
Admitted.

Lemma vLe: (Rabs v <= powerRZ radix (Fexp z)*radix)%R.
Proof using Case2 Fb Nph Nuh Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO uhDef ulDef vDef zDef.
Admitted.

Lemma tLe: (Rabs t <= powerRZ radix (Fexp z)*(radix+1))%R.
Proof using Case2 Cb Exp1 Fa Fb Fx Nph Nuh Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO tDef uhDef ulDef zDef.
Admitted.

Lemma wLe: (Rabs w <= powerRZ radix (Fexp z)*(2*radix+1))%R.
Proof using Case2 Cb Exp1 Fa Fb Fx Nph Nuh Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO tDef uhDef ulDef vDef wDef zDef.
Admitted.

Theorem ErrFmaApprox_2_aux: (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
Proof using Case2 Cb Exp1 Fa Fb Fx Nph Nuh Nv Nw Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO tDef uhDef ulDef vDef wDef zDef.
Admitted.

End uhInexact.

Section uhInexact2.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 4 <= p.

Variables a x b ph pl uh ul z t v w:float.

Hypothesis Fb:  Fbounded bo b.
Hypothesis Fa:  Fbounded bo a.
Hypothesis Fx:  Fbounded bo x.
Hypothesis Cb:  Fcanonic radix bo b.

Hypothesis Nph: Fnormal radix bo ph  \/ (FtoRradix ph=0).
Hypothesis Nuh: Fnormal radix bo uh  \/ (FtoRradix uh=0).
Hypothesis Nz:  Fnormal radix bo z   \/ (FtoRradix z =0).
Hypothesis Nw:  Fnormal radix bo w   \/ (FtoRradix w =0).
Hypothesis Nv:  Fnormal radix bo v   \/ (FtoRradix v =0).

Hypothesis Exp1: (- dExp bo <= Fexp a+Fexp x)%Z.

Hypothesis zDef : Closest bo radix (a*x+b)%R z.
Hypothesis phDef: Closest bo radix (a*x)%R ph.
Hypothesis plDef: (FtoRradix pl=a*x-ph)%R.
Hypothesis uhDef: Closest bo radix (ph+b)%R uh.
Hypothesis ulDef: (FtoRradix ul=ph+b-uh)%R.
Hypothesis tDef : Closest bo radix (uh-z)%R t.
Hypothesis vDef : Closest bo radix (pl+ul)%R v.
Hypothesis wDef : Closest bo radix (t+v)%R w.

Hypothesis Case2: ~(FtoRradix ul=0)%R.

Theorem ErrFmaApprox_2: (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
Proof using Case2 Cb Exp1 Fa Fb Fx Nph Nuh Nv Nw Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanZERO tDef uhDef ulDef vDef wDef zDef.
Admitted.

End uhInexact2.

Section Total.
Variable bo : Fbound.
Variable radix : Z.
Variable p : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.

Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).

Hypothesis pGivesBound : Zpos (vNum bo) = Zpower_nat radix p.
Hypothesis precisionGreaterThanOne : 4 <= p.

Variables a x b ph pl uh ul z t v w:float.

Hypothesis Fb:  Fbounded bo b.
Hypothesis Fa:  Fbounded bo a.
Hypothesis Fx:  Fbounded bo x.

Hypothesis Nph: Fnormal radix bo ph  \/ (FtoRradix ph=0).
Hypothesis Nuh: Fnormal radix bo uh  \/ (FtoRradix uh=0).
Hypothesis Nz:  Fnormal radix bo z   \/ (FtoRradix z =0).
Hypothesis Nw:  Fnormal radix bo w   \/ (FtoRradix w =0).
Hypothesis Nv:  Fnormal radix bo v   \/ (FtoRradix v =0).

Hypothesis Exp1: (- dExp bo <= Fexp a+Fexp x)%Z.

Hypothesis zDef : Closest bo radix (a*x+b)%R z.
Hypothesis phDef: Closest bo radix (a*x)%R ph.
Hypothesis plDef: (FtoRradix pl=a*x-ph)%R.
Hypothesis uhDef: Closest bo radix (ph+b)%R uh.
Hypothesis ulDef: (FtoRradix ul=ph+b-uh)%R.
Hypothesis tDef : Closest bo radix (uh-z)%R t.
Hypothesis vDef : Closest bo radix (pl+ul)%R v.
Hypothesis wDef : Closest bo radix (t+v)%R w.

Theorem ErrFmaApprox: (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
Proof using Exp1 Fa Fb Fx Nph Nuh Nv Nw Nz pGivesBound phDef plDef precisionGreaterThanOne radixMoreThanOne tDef uhDef ulDef vDef wDef zDef.
Admitted.

End Total.

Section EFast.
Variable b : Fbound.
Variable precision : nat.

Let radix := 2%Z.

Let TMTO : (1 < radix)%Z := eq_refl.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix  : float >-> R.

Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
Variable Iplus : float -> float -> float.
Hypothesis
  IplusCorrect :
    forall p q : float,
    Fbounded b p -> Fbounded b q -> Closest b radix (p + q) (Iplus p q).
Hypothesis
  IplusComp :
    forall p q r s : float,
    Fbounded b p ->
    Fbounded b q ->
    Fbounded b r ->
    Fbounded b s -> p = r :>R -> q = s :>R -> Iplus p q = Iplus r s :>R.
Hypothesis IplusSym : forall p q : float, Iplus p q = Iplus q p.
Hypothesis
  IplusOp : forall p q : float, Fopp (Iplus p q) = Iplus (Fopp p) (Fopp q).
Variable Iminus : float -> float -> float.
Hypothesis IminusPlus : forall p q : float, Iminus p q = Iplus p (Fopp q).

Theorem IplusOl :
 forall p q : float,
 Fbounded b p -> Fbounded b q -> p = 0%R :>R -> Iplus p q = q :>R.
Proof using IplusCorrect IplusSym.
Admitted.

Let IminusCorrect := IminusCorrect b Iplus IplusCorrect Iminus IminusPlus.

Let IplusBounded := IplusBounded b Iplus IplusCorrect.

Let IminusBounded := IminusBounded b Iplus IplusCorrect Iminus IminusPlus.

Let IminusId := IminusId b Iplus IplusCorrect Iminus IminusPlus.

Theorem MKnuth :
 forall p q : float,
 Fbounded b p ->
 Fbounded b q ->
 Iminus (Iplus p q) p = (Iplus p q - p)%R :>R ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IminusId IplusBounded IplusComp IplusSym pGivesBound precisionGreaterThanOne.
Admitted.

Theorem IplusCorrectEq :
 forall (p q pq : float) (r : R),
 Fbounded b p ->
 Fbounded b q ->
 Fbounded b pq -> r = pq :>R -> (p + q)%R = pq :>R -> Iplus p q = r :>R.
Proof using IplusBounded IplusComp.
Admitted.

Theorem IminusCorrectEq :
 forall (p q pq : float) (r : R),
 Fbounded b p ->
 Fbounded b q ->
 Fbounded b pq -> r = pq :>R -> (p - q)%R = pq :>R -> Iminus p q = r :>R.
Proof using IminusBounded IminusCorrect.
Admitted.

Theorem MKnuth1 :
 forall p q : float,
 Fbounded b p ->
 Fbounded b q ->
 Iminus q (Iminus (Iplus p q) p) = (q - Iminus (Iplus p q) p)%R :>R ->
 Iminus (Iplus p q) (Iminus (Iplus p q) p) =
 (Iplus p q - Iminus (Iplus p q) p)%R :>R ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IplusBounded IplusComp pGivesBound precisionGreaterThanOne.
Admitted.

Theorem MKnuth2 :
 forall p q : float,
 (Rabs q <= Rabs p)%R ->
 Fbounded b p ->
 Fbounded b q ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IminusId IplusBounded IplusComp IplusOp IplusSym pGivesBound precisionGreaterThanOne.
Admitted.

Theorem IminusOp :
 forall p q : float, Fopp (Iminus p q) = Iminus (Fopp p) (Fopp q).
Proof using IminusPlus IplusOp.
Admitted.

Theorem MKnuthOpp :
 forall p q : float,
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) =
 Fopp
   (Iplus
      (Iminus (Fopp p)
         (Iminus (Iplus (Fopp p) (Fopp q))
            (Iminus (Iplus (Fopp p) (Fopp q)) (Fopp p))))
      (Iminus (Fopp q) (Iminus (Iplus (Fopp p) (Fopp q)) (Fopp p)))) :>R.
Proof using IminusPlus IplusOp.
Admitted.

Theorem MKnuth3 :
 forall p q : float,
 (0 <= q)%R ->
 (q <= radix * - p)%R ->
 (- p <= q)%R ->
 Fbounded b p ->
 Fbounded b q ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IminusId IplusBounded IplusComp IplusSym pGivesBound precisionGreaterThanOne.
Admitted.

Theorem MKnuth4 :
 forall p q : float,
 (0 < - p)%R ->
 (0 < q)%R ->
 (radix * - p < q)%R ->
 Fbounded b p ->
 Fbounded b q ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IplusBounded IplusComp pGivesBound precisionGreaterThanOne.
Admitted.

Theorem MKnuth5 :
 forall p q : float,
 (0 < p)%R ->
 (p < q)%R ->
 Fbounded b p ->
 Fbounded b q ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IplusBounded IplusComp pGivesBound precisionGreaterThanOne.
Admitted.

Theorem MKnuth6 :
 forall p q : float,
 Iplus p q = (p + q)%R :>R ->
 Fbounded b p ->
 Fbounded b q ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IminusId IplusBounded IplusComp IplusSym pGivesBound precisionGreaterThanOne.
Admitted.

Theorem MKnuth7 :
 forall p q : float,
 (Rabs p < q)%R ->
 Fbounded b p ->
 Fbounded b q ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IminusId IplusBounded IplusComp IplusSym pGivesBound precisionGreaterThanOne.
Admitted.

Theorem Knuth :
 forall p q : float,
 Fbounded b p ->
 Fbounded b q ->
 Iplus (Iminus p (Iminus (Iplus p q) (Iminus (Iplus p q) p)))
   (Iminus q (Iminus (Iplus p q) p)) = (p + q - Iplus p q)%R :>R.
Proof using IminusBounded IminusCorrect IminusId IplusBounded IplusComp IplusOp IplusSym pGivesBound precisionGreaterThanOne.
Admitted.
End EFast.

Section Round.
Variable b : Fbound.
Variable radix : Z.
Variable p : nat.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis pGreaterThanOne : 1 < p.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix p.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Theorem exp_ln_powerRZ :
 forall u v : Z, (0 < u)%Z -> (exp (ln u * v) = powerRZ u v)%R.
Proof using b pGreaterThanOne.
Admitted.

Theorem ln_radix_pos : (0 < ln radix)%R.
Proof using radixMoreThanOne.
Admitted.

Theorem exp_le_inv : forall x y : R, (exp x <= exp y)%R -> (x <= y)%R.
Proof using .
Admitted.

Theorem exp_monotone : forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
Proof using .
Admitted.

Theorem firstNormalPos_eq :
 FtoRradix (firstNormalPos radix b p) = powerRZ radix (Z.pred p + - dExp b).
Proof using pGreaterThanOne radixMoreThanOne.
Admitted.

Definition IRNDD (r : R) := Z.pred (up r).

Theorem IRNDD_correct1 : forall r : R, (IRNDD r <= r)%R.
Proof using .
Admitted.

Theorem IRNDD_correct2 : forall r : R, (r < Z.succ (IRNDD r))%R.
Proof using .
Admitted.

Theorem IRNDD_correct3 : forall r : R, (r - 1 < IRNDD r)%R.
Proof using .
Admitted.

Theorem IRNDD_pos : forall r : R, (0 <= r)%R -> (0 <= IRNDD r)%R.
Proof using .
Admitted.

Theorem IRNDD_eq :
 forall (r : R) (z : Z), (z <= r)%R -> (r < Z.succ z)%R -> IRNDD r = z.
Proof using b pGreaterThanOne.
Admitted.

Theorem IRNDD_projector : forall z : Z, IRNDD z = z.
Proof using b pGreaterThanOne.
Admitted.

Definition RND_Min_Pos (r : R) :=
  match Rle_dec (firstNormalPos radix b p) r with
  | left _ =>
      let e := IRNDD (ln r / ln radix + (- Z.pred p)%Z) in
      Float (IRNDD (r * powerRZ radix (- e))) e
  | right _ => Float (IRNDD (r * powerRZ radix (dExp b))) (- dExp b)
  end.

Theorem RND_Min_Pos_bounded_aux :
 forall (r : R) (e : Z),
 (0 <= r)%R ->
 (- dExp b <= e)%Z ->
 (r < powerRZ radix (e + p))%R ->
 Fbounded b (Float (IRNDD (r * powerRZ radix (- e))) e).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Min_Pos_canonic :
 forall r : R, (0 <= r)%R -> Fcanonic radix b (RND_Min_Pos r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Min_Pos_Rle : forall r : R, (0 <= r)%R -> (RND_Min_Pos r <= r)%R.
Proof using pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Min_Pos_monotone :
 forall r s : R,
 (0 <= r)%R -> (r <= s)%R -> (RND_Min_Pos r <= RND_Min_Pos s)%R.
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Min_Pos_projector :
 forall f : float,
 (0 <= f)%R -> Fcanonic radix b f -> FtoRradix (RND_Min_Pos f) = f.
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Min_Pos_correct :
 forall r : R, (0 <= r)%R -> isMin b radix r (RND_Min_Pos r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Definition RND_Max_Pos (r : R) :=
  match Req_EM_T r (RND_Min_Pos r) with
  | left _ => RND_Min_Pos r
  | right _ => FSucc b radix p (RND_Min_Pos r)
  end.

Theorem RND_Max_Pos_canonic :
 forall r : R, (0 <= r)%R -> Fcanonic radix b (RND_Max_Pos r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Max_Pos_Rle : forall r : R, (0 <= r)%R -> (r <= RND_Max_Pos r)%R.
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Max_Pos_correct :
 forall r : R, (0 <= r)%R -> isMax b radix r (RND_Max_Pos r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Definition RND_Min (r : R) :=
  match Rle_dec 0 r with
  | left _ => RND_Min_Pos r
  | right _ => Fopp (RND_Max_Pos (- r))
  end.

Theorem RND_Min_canonic : forall r : R, Fcanonic radix b (RND_Min r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Min_correct : forall r : R, isMin b radix r (RND_Min r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Definition RND_Max (r : R) :=
  match Rle_dec 0 r with
  | left _ => RND_Max_Pos r
  | right _ => Fopp (RND_Min_Pos (- r))
  end.

Theorem RND_Max_canonic : forall r : R, Fcanonic radix b (RND_Max r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_Max_correct : forall r : R, isMax b radix r (RND_Max r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Definition RND_EvenClosest (r : R) :=
  match Rle_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r)) with
  | left H =>
      match
        Rle_lt_or_eq_dec (Rabs (RND_Max r - r)) (Rabs (RND_Min r - r)) H
      with
      | left _ => RND_Max r
      | right _ =>
          match OddEvenDec (Fnum (RND_Min r)) with
          | left _ => RND_Max r
          | right _ => RND_Min r
          end
      end
  | right _ => RND_Min r
  end.

Theorem RND_EvenClosest_canonic :
 forall r : R, Fcanonic radix b (RND_EvenClosest r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

Theorem RND_EvenClosest_correct :
 forall r : R, EvenClosest b radix p r (RND_EvenClosest r).
Proof using pGivesBound pGreaterThanOne radixMoreThanOne.
Admitted.

End Round.

End Pff.

End Pff.

End Flocq.

End Flocq_DOT_Pff_DOT_Pff.

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
Admitted.

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
Admitted.

Theorem plus_error :
  forall x y,
  format x -> format y ->
  format (round beta fexp (Znearest choice) (x + y) - (x + y))%R.
Proof using monotone_exp valid_exp.
Admitted.

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
Admitted.

End round_plus_eq_zero_aux.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_plus_neq_0 :
  forall x y,
  format x -> format y ->
  (x + y <> 0)%R ->
  round beta fexp rnd (x + y) <> 0%R.
Proof using exp_not_FTZ valid_exp valid_rnd.
Admitted.

Theorem round_plus_eq_0 :
  forall x y,
  format x -> format y ->
  round beta fexp rnd (x + y) = 0%R ->
  (x + y = 0)%R.
Proof using exp_not_FTZ valid_exp valid_rnd.
Admitted.

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
Admitted.

Variable choice : Z -> bool.

Lemma FLT_plus_error_N_ex : forall x y,
  generic_format beta (FLT_exp emin prec) x ->
  generic_format beta (FLT_exp emin prec) y ->
  exists eps,
  (Rabs eps <= u_ro beta prec / (1 + u_ro beta prec))%R /\
  round beta (FLT_exp emin prec) (Znearest choice) (x + y)
  = ((x + y) * (1 + eps))%R.
Proof using prec_gt_0_.
Admitted.

Lemma FLT_plus_error_N_round_ex : forall x y,
  generic_format beta (FLT_exp emin prec) x ->
  generic_format beta (FLT_exp emin prec) y ->
  exists eps,
  (Rabs eps <= u_ro beta prec)%R /\
  (x + y
   = round beta (FLT_exp emin prec) (Znearest choice) (x + y) * (1 + eps))%R.
Proof using prec_gt_0_.
Admitted.

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
Admitted.

Lemma mag_minus1 :
  forall z, z <> 0%R ->
  (mag beta z - 1)%Z = mag beta (z / IZR beta).
Proof using .
Admitted.

Theorem round_plus_F2R :
  forall x y, format x -> format y -> (x <> 0)%R ->
  exists m,
  round beta fexp rnd (x+y) = F2R (Float beta m (cexp (x / IZR beta))).
Proof using monotone_exp valid_exp valid_rnd.
Admitted.

Context {exp_not_FTZ : Exp_not_FTZ fexp}.

Theorem round_plus_ge_ulp :
  forall x y, format x -> format y ->
  round beta fexp rnd (x+y) <> 0%R ->
  (ulp beta fexp (x/IZR beta) <= Rabs (round beta fexp rnd (x+y)))%R.
Proof using exp_not_FTZ monotone_exp valid_exp valid_rnd.
Admitted.

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
Admitted.

Lemma round_FLT_plus_ge' :
  forall x y e,
  generic_format beta (FLT_exp emin prec) x -> generic_format beta (FLT_exp emin prec) y ->
  (x <> 0%R -> (bpow (e+prec) <= Rabs x)%R) ->
  (x = 0%R -> y <> 0%R -> (bpow e <= Rabs y)%R) ->
  round beta (FLT_exp emin prec) rnd (x+y) <> 0%R ->
  (bpow e <= Rabs (round beta (FLT_exp emin prec) rnd (x+y)))%R.
Proof using prec_gt_0_ valid_rnd.
Admitted.

Theorem round_FLX_plus_ge :
  forall x y e,
  generic_format beta (FLX_exp prec) x -> generic_format beta (FLX_exp prec) y ->
  (bpow (e+prec) <= Rabs x)%R ->
  (round beta (FLX_exp prec) rnd (x+y) <> 0)%R ->
  (bpow e <= Rabs (round beta (FLX_exp prec) rnd (x+y)))%R.
Proof using prec_gt_0_ valid_rnd.
Admitted.

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
Admitted.

Lemma plus_error_le_r :
  forall x y,
  generic_format beta fexp x -> generic_format beta fexp y ->
  (Rabs (round beta fexp (Znearest choice) (x + y) - (x + y)) <= Rabs y)%R.
Proof using valid_exp.
Admitted.

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
Admitted.

Theorem mult_error_FLX :
  forall x y,
  format x -> format y ->
  format (round beta (FLX_exp prec) rnd (x * y) - (x * y))%R.
Proof using prec_gt_0_ valid_rnd.
Admitted.

Lemma mult_bpow_exact_FLX :
  forall x e,
  format x ->
  format (x * bpow e)%R.
Proof using .
Admitted.

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
Admitted.

Lemma F2R_ge: forall (y:float beta),
   (F2R y <> 0)%R -> (bpow (Fexp y) <= Rabs (F2R y))%R.
Proof using .
Admitted.

Theorem mult_error_FLT_ge_bpow :
  forall x y e,
  format x -> format y ->
  (bpow (e+2*prec-1) <= Rabs (x * y))%R ->
  (round beta (FLT_exp emin prec) rnd (x * y) - (x * y) <> 0)%R ->
  (bpow e <= Rabs (round beta (FLT_exp emin prec) rnd (x * y) - (x * y)))%R.
Proof using valid_rnd.
Admitted.

Lemma mult_bpow_exact_FLT :
  forall x e,
  format x ->
  (emin + prec - mag beta x <= e)%Z ->
  format (x * bpow e)%R.
Proof using .
Admitted.

Lemma mult_bpow_pos_exact_FLT :
  forall x e,
  format x ->
  (0 <= e)%Z ->
  format (x * bpow e)%R.
Proof using .
Admitted.

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
Admitted.

Theorem generic_format_plus_weak :
  forall x y,
  format x -> format y ->
  (Rabs (x + y) <= Rmin (Rabs x) (Rabs y))%R ->
  format (x + y)%R.
Proof using monotone_exp valid_exp.
Admitted.

Lemma sterbenz_aux :
  forall x y, format x -> format y ->
  (y <= x <= 2 * y)%R ->
  format (x - y)%R.
Proof using monotone_exp valid_exp.
Admitted.

Theorem sterbenz :
  forall x y, format x -> format y ->
  (y / 2 <= x <= 2 * y)%R ->
  format (x - y)%R.
Proof using monotone_exp valid_exp.
Admitted.

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
Admitted.

Theorem RND_Closest_correct :
 forall r : R, Closest b beta r (RND_Closest r).
Proof using pGivesBound pGreaterThanOne.
Admitted.

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
Admitted.

Lemma make_bound_p:
        Zpos (vNum (make_bound))=(Zpower_nat beta (Z.abs_nat p)).
Proof using precisionNotZero.
Admitted.

Lemma FtoR_F2R: forall (f:Pff.float) (g: float beta), Pff.Fnum f = Fnum g -> Pff.Fexp f = Fexp g ->
  FtoR beta f = F2R g.
Proof using .
Admitted.

End Bounds.
Section b_Bounds.

Definition bsingle := make_bound radix2 24 (-149)%Z.

Lemma psGivesBound: Zpos (vNum bsingle) = Zpower_nat 2 24.
Admitted.

Definition bdouble := make_bound radix2 53 1074.

Lemma pdGivesBound: Zpos (vNum bdouble) = Zpower_nat 2 53.
Admitted.

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
Admitted.

Lemma format_is_pff_format': forall r,
   (generic_format beta (FLT_exp (-dExp b) p) r) ->
    Fbounded b (Pff.Float (Ztrunc (scaled_mantissa beta (FLT_exp (-dExp b) p) r))
                            (cexp beta (FLT_exp (-dExp b) p) r)).
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma format_is_pff_format: forall r,
  (generic_format beta (FLT_exp (-dExp b) p) r)
  -> exists f, FtoR beta f = r /\ Fbounded b f.
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma format_is_pff_format_can: forall r,
  (generic_format beta (FLT_exp (-dExp b) p) r)
  -> exists f, FtoR beta f = r /\ Fcanonic beta b f.
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma equiv_RNDs_aux: forall z, Z.even z = true -> Even z.
Proof using .
Admitted.

Lemma pff_canonic_is_canonic: forall f, Fcanonic beta b f -> FtoR beta f <> 0 ->
  canonical beta (FLT_exp (- dExp b) p)
    (Float beta (Pff.Fnum f) (Pff.Fexp f)).
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma pff_round_NE_is_round: forall (r:R),
   (FtoR beta (RND_EvenClosest b beta (Z.abs_nat p) r)
     =  round beta (FLT_exp (-dExp b) p) rndNE r).
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma round_NE_is_pff_round: forall (r:R),
   exists f:Pff.float, (Fcanonic beta b f /\ (EvenClosest b beta (Z.abs_nat p) r f) /\
    FtoR beta f =  round beta (FLT_exp (-dExp b) p) rndNE r).
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma pff_round_UP_is_round: forall (r:R),
  FtoR beta (RND_Max b beta (Z.abs_nat p) r)
             = round beta (FLT_exp (- dExp b) p) Zceil r.
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma pff_round_DN_is_round: forall (r:R),
  FtoR beta (RND_Min b beta (Z.abs_nat p) r)
             = round beta (FLT_exp (- dExp b) p) Zfloor r.
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma pff_round_N_is_round: forall choice, forall (r:R),
   (FtoR beta (RND_Closest b beta (Z.abs_nat p) choice r)
     =  round beta (FLT_exp (-dExp b) p) (Znearest choice) r).
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma round_N_is_pff_round: forall choice, forall (r:R),
   exists f:Pff.float, (Fcanonic beta b f /\ (Closest b beta r f) /\
    FtoR beta f =  round beta (FLT_exp (-dExp b) p) (Znearest choice) r).
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma pff_round_is_round_N: forall r f, Closest b beta r f ->
    exists (choice:Z->bool),
      FtoR beta f = round beta (FLT_exp (-dExp b) p) (Znearest choice) r.
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma FloatFexp_gt:  forall e f, Fbounded b f ->
  (bpow beta (e+p) <= Rabs (FtoR beta f))%R ->
       (e < Pff.Fexp f)%Z.
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma CanonicGeNormal:  forall f, Fcanonic beta b f ->
  (bpow beta (-dExp b+p-1) <= Rabs (FtoR beta f))%R ->
       (Fnormal beta b f)%Z.
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma Fulp_ulp_aux:  forall f, Fcanonic beta b f ->
   Fulp b beta (Z.abs_nat p) f
    = ulp beta (FLT_exp (-dExp b) p) (FtoR beta f).
Proof using pGivesBound precisionNotZero.
Admitted.

Lemma Fulp_ulp:  forall f, Fbounded b f ->
   Fulp b beta (Z.abs_nat p) f
    = ulp beta (FLT_exp (-dExp b) p) (FtoR beta f).
Proof using pGivesBound precisionNotZero.
Admitted.

End Equiv.

Section Equiv_instanc.

Lemma round_NE_is_pff_round_b32: forall (r:R),
   exists f:Pff.float, (Fcanonic 2 bsingle f /\ (EvenClosest bsingle 2 24 r f) /\
    FtoR 2 f =  round radix2 (FLT_exp (-149) 24) rndNE r).
Admitted.

Lemma round_NE_is_pff_round_b64: forall (r:R),
   exists f:Pff.float, (Fcanonic 2 bdouble f /\ (EvenClosest bdouble 2 53 r f) /\
    FtoR 2 f =  round radix2 (FLT_exp (-1074) 53) rndNE r).
Admitted.

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
Admitted.

Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a := round_flt (x+y).
Let b := round_flt (y+round_flt (x-a)).

Theorem Fast2Sum_correct: Rabs y <= Rabs x -> a+b=x+y.
Proof using Fx Fy choice_sym emin_neg precisionNotZero.
Admitted.

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
Admitted.

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
Admitted.

Theorem Veltkamp_Even:
  (choice = fun z => negb (Z.even z)) ->
   hx = round_flt_s x.
Proof using Fx SGe SLe emin_neg precisionGe3.
Admitted.

Theorem Veltkamp: exists choice': Z->bool ,
   hx = round beta (FLT_exp emin (prec-s)) (Znearest choice') x.
Proof using Fx SGe SLe emin_neg precisionGe3 q.
Admitted.

Theorem Veltkamp_tail:
 x = hx+tx /\  generic_format beta (FLT_exp emin s) tx.
Proof using Fx SGe SLe emin_neg precisionGe3 q.
Admitted.

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
Admitted.

Lemma underf_mult_aux':
 forall x y,
  Fbounded b x ->
  Fbounded b y ->
   (bpow beta (-dExp b + 2 * prec - 1)%Z <= Rabs (FtoR beta x * FtoR beta y)) ->
     (-dExp b <= Pff.Fexp x + Pff.Fexp y)%Z.
Proof using pGivesBound precisionGt1.
Admitted.

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
Admitted.

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
Admitted.

Lemma V1_Und3: u1 = 0 \/ bpow beta (emin + prec) <= Rabs u1.
Proof using V1_Und1 choice prec_gt_0_ precisionGe3.
Admitted.

Lemma ErrFMA_bounded: format r1 /\ format r2 /\ format r3.
Proof using Fa Fx Fy V1_Und1 alpha2 gamma prec_gt_0_.
Admitted.

Lemma ErrFMA_correct:
   a*x+y = r1+r2+r3.
Proof using Even_radix Fa Fx Fy V1_Und1 V1_Und2 V1_Und4 V1_Und5 alpha2 emin_neg gamma prec_gt_0_ precisionGe3.
Admitted.

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
Admitted.

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
Admitted.

Lemma V2_Und4: a*x <> 0 -> beta1 = 0 \/ bpow beta (emin + prec+1) <= Rabs beta1.
Proof using U1 alpha1 prec_gt_0_ precisionGe3.
Admitted.

Lemma V2_Und2:  y <> 0 ->  alpha1 = 0 \/ bpow beta (emin + prec) <= Rabs alpha1.
Proof using Fa Fx Fy U1 U2 prec_gt_0_ precisionGe3 u2.
Admitted.

Lemma V2_Und5: a*x <> 0 -> r1 = 0 \/ bpow beta (emin + prec-1) <= Rabs r1.
Proof using Fa Fx Fy U1 U2 prec_gt_0_ precisionGe3.
Admitted.

Lemma ErrFMA_correct_simpl:
   a*x+y = r1+r2+r3.
Proof using Even_radix Fa Fx Fy U1 U2 alpha2 emin_neg gamma prec_gt_0_ precisionGe3.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma U4_discri1 : b * b <> 0 -> a * c <> 0 -> p - q <> 0 ->
    bpow (emin + prec) <= Rabs d.
Proof using U1 Zd prec_gt_0_ precisionGt.
Admitted.

Lemma format_dp : format dp.
Proof using Fb U1 p prec_gt_0_ precisionGt.
Admitted.

Lemma format_dq : format dq.
Proof using Fa Fc U2 prec_gt_0_ precisionGt q.
Admitted.

Lemma format_d_discri1 : format d.
Proof using dp dq prec_gt_0_.
Admitted.

Lemma U5_discri1_aux : forall x y e, format x -> format y
   -> (emin <= e)%Z -> bpow e <= Rabs x -> bpow e <= Rabs y
   -> round_flt (x+y) <> x+y
   -> bpow e <= Rabs (round_flt (x+y)).
Proof using prec_gt_0_.
Admitted.

Lemma U5_discri1 : b * b <> 0 -> a*c <> 0 ->
  round_flt (dp - dq) <> dp - dq ->
  bpow (emin + prec - 1) <= Rabs (round_flt (dp - dq)).
Proof using Fa Fb Fc U1 U2 prec_gt_0_ precisionGt.
Admitted.

Theorem discri_correct_test :
 Rabs (d-(b*b-a*c)) <= 2* ulp_flt d.
Proof using Fa Fb Fc U1 U2 Zd emin_neg prec_gt_0_ precisionGt.
Admitted.

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
Admitted.

Theorem discri_fp_test :
 Rabs (d-(b*b-a*c)) <= 2* ulp_flt d.
Proof using Fa Fb Fc U1 U2 Zd emin_neg prec_gt_0_ precisionGt.
Admitted.

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
Admitted.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (cexp beta (FLX_exp prec)).

Variable choice : Z -> bool.

Theorem div_error_FLX :
  forall rnd { Zrnd : Valid_rnd rnd } x y,
  format x -> format y ->
  format (x - round beta (FLX_exp prec) rnd (x/y) * y)%R.
Proof using prec_gt_0_.
Admitted.

Variable Hp1 : Z.lt 1 prec.

Theorem sqrt_error_FLX_N :
  forall x, format x ->
  format (x - Rsqr (round beta (FLX_exp prec) (Znearest choice) (sqrt x)))%R.
Proof using Hp1 prec_gt_0_.
Admitted.

Lemma sqrt_error_N_FLX_aux1 x (Fx : format x) (Px : (0 < x)%R) :
  exists (mu : R) (e : Z), (format mu /\ x = mu * bpow (2 * e) :> R
                            /\ 1 <= mu < bpow 2)%R.
Proof using .
Admitted.

Notation u_ro := (u_ro beta prec).

Lemma sqrt_error_N_FLX_aux2 x (Fx : format x) :
  (1 <= x)%R ->
  (x = 1 :> R \/ x = 1 + 2 * u_ro :> R \/ 1 + 4 * u_ro <= x)%R.
Proof using Hp1 prec_gt_0_.
Admitted.

Lemma sqrt_error_N_FLX_aux3 :
  (u_ro / sqrt (1 + 4 * u_ro) <= 1 - 1 / sqrt (1 + 2 * u_ro))%R.
Proof using Hp1 prec_gt_0_.
Admitted.

Lemma om1ds1p2u_ro_pos : (0 <= 1 - 1 / sqrt (1 + 2 * u_ro))%R.
Proof using .
Admitted.

Lemma om1ds1p2u_ro_le_u_rod1pu_ro :
  (1 - 1 / sqrt (1 + 2 * u_ro) <= u_ro / (1 + u_ro))%R.
Proof using .
Admitted.

Lemma s1p2u_rom1_pos : (0 <= sqrt (1 + 2 * u_ro) - 1)%R.
Proof using .
Admitted.

Theorem sqrt_error_N_FLX x (Fx : format x) :
  (Rabs (round beta (FLX_exp prec) (Znearest choice) (sqrt x) - sqrt x)
   <= (1 - 1 / sqrt (1 + 2 * u_ro)) * Rabs (sqrt x))%R.
Proof using Hp1 prec_gt_0_.
Admitted.

Theorem sqrt_error_N_FLX_ex x (Fx : format x) :
  exists eps,
  (Rabs eps <= 1 - 1 / sqrt (1 + 2 * u_ro))%R /\
  round beta (FLX_exp prec) (Znearest choice) (sqrt x)
  = (sqrt x * (1 + eps))%R.
Proof using Hp1 prec_gt_0_.
Admitted.

Lemma sqrt_error_N_round_ex_derive :
  forall x rx,
  (exists eps,
   (Rabs eps <= 1 - 1 / sqrt (1 + 2 * u_ro))%R /\ rx = (x * (1 + eps))%R) ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\ x = (rx * (1 + eps))%R.
Proof using prec_gt_0_.
Admitted.

Theorem sqrt_error_N_FLX_round_ex :
  forall x,
  format x ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\
  sqrt x = (round beta (FLX_exp prec) (Znearest choice) (sqrt x) * (1 + eps))%R.
Proof using Hp1 prec_gt_0_.
Admitted.

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
Admitted.

Theorem sqrt_error_N_FLT_round_ex :
  forall x,
  generic_format beta (FLT_exp emin prec) x ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\
  sqrt x
  = (round beta (FLT_exp emin prec) (Znearest choice) (sqrt x) * (1 + eps))%R.
Proof using Hemin Hp1 prec_gt_0_.
Admitted.

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
Admitted.

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
Admitted.

Theorem format_REM_ZR:
  forall x y : R,
  format x -> format y ->
  format (x - IZR (Ztrunc (x/y)) * y).
Proof using monotone_exp valid_exp.
Admitted.

Theorem format_REM_N :
  forall choice,
  forall x y : R,
  format x -> format y ->
  format (x - IZR (Znearest choice (x/y)) * y).
Proof using monotone_exp valid_exp.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Section Double_round_mult.

Lemma mag_mult_disj :
  forall x y,
  x <> 0 -> y <> 0 ->
  ((mag (x * y) = (mag x + mag y - 1)%Z :> Z)
   \/ (mag (x * y) = (mag x + mag y)%Z :> Z)).
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

End Double_round_mult_FTZ.

End Double_round_mult.

Section Double_round_plus.

Lemma mag_plus_disj :
  forall x y,
  0 < y -> y <= x ->
  ((mag (x + y) = mag x :> Z)
   \/ (mag (x + y) = (mag x + 1)%Z :> Z)).
Proof using .
Admitted.

Lemma mag_plus_separated :
  forall fexp : Z -> Z,
  forall x y,
  0 < x -> 0 <= y ->
  generic_format beta fexp x ->
  (mag y <= fexp (mag x))%Z ->
  (mag (x + y) = mag x :> Z).
Proof using .
Admitted.

Lemma mag_minus_disj :
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= mag x - 2)%Z ->
  ((mag (x - y) = mag x :> Z)
   \/ (mag (x - y) = (mag x - 1)%Z :> Z)).
Proof using .
Admitted.

Lemma mag_minus_separated :
  forall fexp : Z -> Z, Valid_exp fexp ->
  forall x y,
  0 < x -> 0 < y -> y < x ->
  bpow (mag x - 1) < x ->
  generic_format beta fexp x -> (mag y <= fexp (mag x))%Z ->
  (mag (x - y) = mag x :> Z).
Proof using .
Admitted.

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
Admitted.

Lemma round_round_plus_aux0_aux :
  forall (fexp1 fexp2 : Z -> Z),
  forall x y,
  (fexp2 (mag (x + y))%Z <= fexp1 (mag x))%Z ->
  (fexp2 (mag (x + y))%Z <= fexp1 (mag y))%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof using .
Admitted.

Lemma round_round_plus_aux0 :
  forall (fexp1 fexp2 : Z -> Z), Valid_exp fexp1 ->
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  (0 < x)%R -> (0 < y)%R -> (y <= x)%R ->
  (fexp1 (mag x) - 1 <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma round_round_minus_aux0_aux :
  forall (fexp1 fexp2 : Z -> Z),
  forall x y,
  (fexp2 (mag (x - y))%Z <= fexp1 (mag x))%Z ->
  (fexp2 (mag (x - y))%Z <= fexp1 (mag y))%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof using .
Admitted.

Lemma round_round_minus_aux0 :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (fexp1 (mag x) - 1 <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Section Double_round_plus_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_plus_hyp :
  (2 * prec + 1 <= prec')%Z ->
  round_round_plus_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
Admitted.

Theorem round_round_plus_FLX :
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

Theorem round_round_minus_FLX :
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

Theorem round_round_plus_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

Theorem round_round_minus_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

Theorem round_round_plus_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

Theorem round_round_minus_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma round_round_minus_radix_ge_3_aux0 :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (fexp1 (mag x) <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Section Double_round_plus_radix_ge_3_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_plus_radix_ge_3_hyp :
  (2 * prec <= prec')%Z ->
  round_round_plus_radix_ge_3_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
Admitted.

Theorem round_round_plus_radix_ge_3_FLX :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

Theorem round_round_minus_radix_ge_3_FLX :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

Theorem round_round_plus_radix_ge_3_FLT :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

Theorem round_round_minus_radix_ge_3_FLT :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

Theorem round_round_plus_radix_ge_3_FTZ :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x + y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

Theorem round_round_minus_radix_ge_3_FTZ :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x - y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma round_round_sqrt :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_sqrt_hyp fexp1 fexp2 ->
  forall x,
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (sqrt x).
Proof using .
Admitted.

Section Double_round_sqrt_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_sqrt_hyp :
  (2 * prec + 2 <= prec')%Z ->
  round_round_sqrt_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
Admitted.

Theorem round_round_sqrt_FLX :
  forall choice1 choice2,
  (2 * prec + 2 <= prec')%Z ->
  forall x,
  FLX_format beta prec x ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (sqrt x).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Section Double_round_sqrt_radix_ge_4_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_sqrt_radix_ge_4_hyp :
  (2 * prec + 1 <= prec')%Z ->
  round_round_sqrt_radix_ge_4_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
Admitted.

Theorem round_round_sqrt_radix_ge_4_FLX :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x,
  FLX_format beta prec x ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (sqrt x).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma round_round_really_zero :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (mag x <= fexp1 (mag x) - 2)%Z ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof using .
Admitted.

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
Admitted.

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
Admitted.

Lemma mag_div_disj :
  forall x y : R,
  0 < x -> 0 < y ->
  ((mag (x / y) = mag x - mag y :> Z)%Z
   \/ (mag (x / y) = mag x - mag y + 1 :> Z)%Z).
Proof using .
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Section Double_round_div_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_div_hyp :
  (2 * prec <= prec')%Z ->
  round_round_div_hyp (FLX_exp prec) (FLX_exp prec').
Proof using prec_gt_0_.
Admitted.

Theorem round_round_div_FLX :
  forall choice1 choice2,
  (exists n, (beta = 2 * n :> Z)%Z) ->
  (2 * prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x / y).
Proof using prec_gt_0_ prec_gt_0_'.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma Zrnd_odd_Zodd: forall x, x <> (IZR (Zfloor x)) ->
  (Z.even (Zrnd_odd x)) = false.
Admitted.

Lemma Zfloor_plus: forall (n:Z) y,
  (Zfloor (IZR n+y) = n + Zfloor y)%Z.
Admitted.

Lemma Zceil_plus: forall (n:Z) y,
  (Zceil (IZR n+y) = n + Zceil y)%Z.
Admitted.

Lemma Zeven_abs: forall z, Z.even (Z.abs z) = Z.even z.
Admitted.

Lemma Zrnd_odd_plus: forall x y, (x = IZR (Zfloor x)) ->
    Z.even (Zfloor x) = true ->
   (IZR (Zrnd_odd (x+y)) = x+IZR (Zrnd_odd y))%R.
Admitted.

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
Admitted.

Theorem round_odd_opp :
  forall x,
  round beta fexp Zrnd_odd (-x) = (- round beta fexp Zrnd_odd x)%R.
Proof using .
Admitted.

Theorem round_odd_pt :
  forall x,
  Rnd_odd_pt x (round beta fexp Zrnd_odd x).
Proof using exists_NE_ valid_exp.
Admitted.

Theorem Rnd_odd_pt_unique :
  forall x f1 f2 : R,
  Rnd_odd_pt x f1 -> Rnd_odd_pt x f2 ->
  f1 = f2.
Proof using exists_NE_ valid_exp.
Admitted.

Theorem Rnd_odd_pt_monotone :
  round_pred_monotone (Rnd_odd_pt).
Proof using exists_NE_ valid_exp.
Admitted.

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
Admitted.

Lemma exists_even_fexp_lt: forall (c:Z->Z), forall (x:R),
      (exists f:float beta, F2R f = x /\ (c (mag beta x) < Fexp f)%Z) ->
      exists f:float beta, F2R f =x /\ canonical beta c f /\ Z.even (Fnum f) = true.
Proof using Even_beta.
Admitted.

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
Admitted.

Lemma u_eq: F2R u= round beta fexp Zceil x.
Proof using Hu valid_exp.
Admitted.

Lemma d_ge_0: (0 <= F2R d)%R.
Proof using Hd valid_exp xPos.
Admitted.

Lemma mag_d:  (0< F2R d)%R ->
    (mag beta (F2R d) = mag beta x :>Z).
Proof using Hd valid_exp.
Admitted.

Lemma Fexp_d: (0 < F2R d)%R -> Fexp d =fexp (mag beta x).
Proof using Cd Hd valid_exp.
Admitted.

Lemma format_bpow_x: (0 < F2R d)%R
    -> generic_format beta fexp  (bpow (mag beta x)).
Proof using Cd Hd valid_exp.
Admitted.

Lemma format_bpow_d: (0 < F2R d)%R ->
  generic_format beta fexp (bpow (mag beta (F2R d))).
Proof using Cd valid_exp.
Admitted.

Lemma d_le_m: (F2R d <= m)%R.
Proof using Hd Hu.
Admitted.

Lemma m_le_u: (m <= F2R u)%R.
Proof using Hd Hu.
Admitted.

Lemma mag_m: (0 < F2R d)%R -> (mag beta m =mag beta (F2R d) :>Z).
Proof using Cd Hd Hu valid_exp.
Admitted.

Lemma mag_m_0: (0 = F2R d)%R
    -> (mag beta m =mag beta (F2R u)-1:>Z)%Z.
Proof using Hd Hu valid_exp xPos.
Admitted.

Lemma u'_eq:  (0 < F2R d)%R -> exists f:float beta, F2R f = F2R u /\ (Fexp f = Fexp d)%Z.
Proof using Cd Hd Hu valid_exp.
Admitted.

Lemma m_eq :
  (0 < F2R d)%R ->
  exists f:float beta,
  F2R f = m /\ (Fexp f = fexp (mag beta x) - 1)%Z.
Proof using Cd Even_beta Hd Hu valid_exp.
Admitted.

Lemma m_eq_0: (0 = F2R d)%R ->  exists f:float beta,
   F2R f = m /\ (Fexp f = fexp (mag beta (F2R u)) -1)%Z.
Proof using Cu Even_beta Hu.
Admitted.

Lemma fexp_m_eq_0:  (0 = F2R d)%R ->
  (fexp (mag beta (F2R u)-1) < fexp (mag beta (F2R u))+1)%Z.
Proof using Even_beta Hd Hu exists_NE_ valid_exp xPos.
Admitted.

Lemma Fm:  generic_format beta fexpe m.
Proof using Cd Cu Even_beta Hd Hu exists_NE_ fexpe_fexp valid_exp xPos.
Admitted.

Lemma Zm:
   exists g : float beta, F2R g = m /\ canonical beta fexpe g /\ Z.even (Fnum g) = true.
Proof using Cd Cu Even_beta Hd Hu exists_NE_ fexpe_fexp valid_exp xPos.
Admitted.

Lemma DN_odd_d_aux :
  forall z, (F2R d <= z < F2R u)%R ->
  Rnd_DN_pt (generic_format beta fexp) z (F2R d).
Proof using Hd Hu valid_exp.
Admitted.

Lemma UP_odd_d_aux :
  forall z, (F2R d < z <= F2R u)%R ->
  Rnd_UP_pt (generic_format beta fexp) z (F2R u).
Proof using Hd Hu valid_exp.
Admitted.

Lemma round_N_odd_pos :
  round beta fexp (Znearest choice) (round beta fexpe Zrnd_odd x) =
               round beta fexp (Znearest choice) x.
Proof using Cd Cu Even_beta Hd Hu exists_NE_ exists_NE_e fexpe_fexp m valid_exp valid_expe xPos.
Admitted.

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
Admitted.

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
Admitted.

Theorem mag_round_odd: forall (x:R),
 (emin < mag beta x)%Z ->
  (mag_val beta _ (mag beta (round beta (FLT_exp emin prec) Zrnd_odd x))
      = mag_val beta x (mag beta x))%Z.
Proof using Even_beta prec_gt_1.
Admitted.

Theorem fexp_round_odd: forall (x:R),
  (cexp_flt (round beta (FLT_exp emin prec) Zrnd_odd x)
      = cexp_flt x)%Z.
Proof using Even_beta prec_gt_1.
Admitted.

End Odd_propbis.
