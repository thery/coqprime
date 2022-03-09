
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import ZArith Znumtheory Zpow_facts.
Require Import CyclicAxioms Cyclic63 Int63Compat.
From Bignums Require Import DoubleCyclic BigN.
Require Import ZCAux.
Require Import W.
Require Import Mod_op.
Require Import LucasLehmer.
Require Import Bits.
Import CyclicAxioms DoubleType DoubleBase.

Open Scope Z_scope.

Section test.

Variable w: univ_of_cycles.
Variable w_op: ZnZ.Ops w.
Variable op_spec: ZnZ.Specs w_op.
Variable p: positive.
Variable b: w.

Notation "[| x |]" :=
   (ZnZ.to_Z x)  (at level 0, x at level 99).


Hypothesis p_more_1: 2 < Zpos p.
Hypothesis b_p: [|b|] = 2 ^ Zpos p - 1.

Lemma b_pos: 0 < [|b|].
rewrite b_p.
assert (2 ^ 0 < 2 ^ Zpos p).
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_0_r in H; auto with zarith.
Qed.

Hint Resolve b_pos : core.

Variable m_op: mod_op w.
Variable m_op_spec: mod_spec w_op b m_op.

Let w2 := m_op.(add_mod) ZnZ.one ZnZ.one.

Lemma w1_b: [|ZnZ.one|] = 1 mod [|b|].
rewrite ZnZ.spec_1; simpl; auto.
rewrite Zmod_small; auto with zarith.
split; auto with zarith.
rewrite b_p.
assert (H : 2 ^ 1 < 2 ^ Zpos p)
by (apply Zpower_lt_monotone; auto with zarith).
rewrite Zpower_1_r in H; auto with zarith.
Qed.

Lemma w2_b: [|w2|] = 2 mod [|b|].
unfold w2; rewrite (add_mod_spec m_op_spec _ _ _ _ w1_b w1_b).
rewrite w1_b; rewrite <- Zplus_mod; auto with zarith.
Qed.

Let w4 := m_op.(add_mod) w2 w2.

Lemma w4_b: [|w4|] = 4 mod [|b|].
unfold w4; rewrite (add_mod_spec m_op_spec _ _ _ _ w2_b w2_b).
rewrite w2_b; rewrite <- Zplus_mod; auto with zarith.
Qed.

Let square_m2 :=
   let square := m_op.(square_mod) in
   let sub := m_op.(sub_mod) in
   fun x => sub (square x) w2.

Definition lucastest_step x p := iter_pos _ square_m2 x p.

Lemma square_m2_bounded x : 0 <= [|x|] < [|b|] -> 0 <= [|square_m2 x|] < [|b|].
Proof.
intro H.
unfold square_m2.
rewrite (sub_mod_spec m_op_spec _ _  [|square_mod m_op x|] 2).
apply Z.mod_pos_bound; auto with zarith.
rewrite Z.mod_small; auto with zarith.
rewrite (square_mod_spec m_op_spec x [|x|]); auto.
apply Z.mod_pos_bound; auto with zarith.
rewrite Z.mod_small; auto with zarith.
exact w2_b.
Qed.

Lemma lucastest_bounded x p1 : 0 <= [|x|] < [|b|] ->
  0 <= [|lucastest_step x p1|] < [|b|].
Proof.
unfold lucastest_step.
revert p1 x.
intros p1; pattern p1; apply Pind; simpl iter_pos; simpl s; clear p1.
exact square_m2_bounded.
intros p1 IH x Hx.
rewrite Pos.iter_succ.
apply square_m2_bounded.
apply IH; auto.
Qed.

Lemma square_m2_eq x1 x2 :
 [|x1|] < [|b|] ->
[|x1|] = [|x2|] -> [|square_m2 x1|] = [|square_m2 x2|].
Proof.
intros Hx1 Ex1.
assert (H1 : [|x1|] = [|x1|] mod [|b|]).
rewrite Z.mod_small; auto with zarith.
case (ZnZ.spec_to_Z x1); auto with zarith.
assert (H2 : [|x2|] = [|x2|] mod [|b|]).
rewrite <- Ex1; auto.
unfold square_m2.
rewrite (sub_mod_spec m_op_spec _ _  [|square_mod m_op x1|] 2).
rewrite (sub_mod_spec m_op_spec _ _  [|square_mod m_op x2|] 2).
rewrite (square_mod_spec m_op_spec x1 [|x1|]); auto.
rewrite (square_mod_spec m_op_spec x2 [|x2|]); auto.
rewrite Ex1; auto.
rewrite Z.mod_small; auto with zarith.
rewrite (square_mod_spec m_op_spec x2 [|x2|]); auto.
apply Z.mod_bound_pos; auto with zarith.
apply Z.square_nonneg.
exact w2_b.
rewrite Z.mod_small; auto with zarith.
rewrite (square_mod_spec m_op_spec x1 [|x1|]); auto.
apply Z.mod_bound_pos; auto with zarith.
apply Z.square_nonneg.
exact w2_b.
Qed.

Lemma lucastest_eq x1 x2 p1 : [|x1|] < [|b|] ->
  [|x1|] = [|x2|] -> [|lucastest_step x1 p1|] =  [|lucastest_step x2 p1|].
Proof.
unfold lucastest_step.
revert p1 x1 x2.
intros p1; pattern p1; apply Pind; simpl iter_pos; simpl s; clear p1.
exact square_m2_eq.
intros p1 IH x1 x2 Hx1 Hx2.
rewrite !Pos.iter_succ.
apply square_m2_eq.
assert (F : 0 <= [|x1|] < [|b|]).
case (ZnZ.spec_to_Z x1); auto with zarith.
generalize (lucastest_bounded _ p1 F).
unfold lucastest_step; auto with zarith.
apply IH; auto.
Qed.

Theorem lucastest_step_add :
 forall p1 p2 z z1 z2, lucastest_step z p1 = z1 ->
        lucastest_step z1 p2 = z2 -> lucastest_step z (p2 + p1) = z2.
Proof.
unfold lucastest_step.
intros p1 p2 z z1 z2 H1 H2.
rewrite Pos.iter_add, H1; auto.
Qed.

Theorem lucastest_step_correct:
 forall p1 z n, 0 <= n -> [|z|] = fst (s n) mod (2 ^ Zpos p - 1) ->
       [|lucastest_step z p1|] = fst (s (n + Zpos p1)) mod (2 ^ Zpos p - 1).
unfold lucastest_step.
intros p1; pattern p1; apply Pind; simpl iter_pos; simpl s; clear p1.
intros z p1 Hp1 H.
unfold square_m2.
rewrite <- b_p in H.
generalize (square_mod_spec m_op_spec _ _ H); intros H1.
rewrite (sub_mod_spec m_op_spec _ _ _ _ H1 w2_b).
rewrite H1; rewrite w2_b.
rewrite H; rewrite <- Zmult_mod.
rewrite <- Zminus_mod.
rewrite sn by assumption; simpl.
rewrite b_p; auto.
intros p1 Rec w1 z Hz Hw1.
rewrite Pplus_one_succ_l; rewrite iter_pos_plus;
 simpl iter_pos.
match goal with |- context[square_m2 ?X] =>
  set (tmp := X); unfold square_m2; unfold tmp; clear tmp
end.
generalize (Rec _ _ Hz Hw1); intros H1.
rewrite <- b_p in H1.
generalize (square_mod_spec m_op_spec _ _ H1); intros H2.
rewrite (sub_mod_spec m_op_spec _ _ _ _ H2 w2_b).
rewrite H2; rewrite w2_b.
rewrite H1; rewrite <- Zmult_mod.
rewrite <- Zminus_mod.
replace (z + Zpos (1 + p1)) with ((z + Zpos p1) + 1).
rewrite sn; simpl fst; try rewrite b_p; auto with zarith.
rewrite Zpos_plus_distr; auto with zarith.
Qed.

Definition lucastest := [|lucastest_step w4 (Pminus p 2)|].

Theorem lucastest_prop: lucastest = fst(s (Zpos p -2)) mod (2 ^ Zpos p - 1).
unfold lucastest.
assert (F: 0 <= 0); auto with zarith.
generalize (lucastest_step_correct (p -2) w4 F); simpl Zplus;
   rewrite Zpos_minus; auto with zarith.
rewrite Zmax_right; auto with zarith.
intros tmp; apply tmp; clear tmp.
rewrite <- b_p; simpl; exact w4_b.
Qed.

Theorem lucastest_prop_cor: lucastest = 0 -> (2 ^ Zpos p - 1 | fst(s (Zpos p - 2)))%Z.
intros H.
apply Zmod_divide.
assert (H1: 2 ^ 1 < 2 ^ Zpos p).
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_1_r in H1; auto with zarith.
apply trans_equal with (2:= H); apply sym_equal; apply lucastest_prop; auto.
Qed.

Theorem lucastest_prime:  lucastest = 0 -> prime (2 ^ Zpos p - 1).
intros H1; case (prime_dec (2 ^ Zpos p - 1)); auto; intros H2.
case Zdivide_div_prime_le_square with (2 := H2).
assert (H3: 2 ^ 1 < 2 ^ Zpos p).
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_1_r in H3; auto with zarith.
intros q (H3, (H4, H5)).
contradict H5; apply Zlt_not_le.
generalize q_more_than_square; unfold Mp; intros tmp; apply tmp;
  auto; clear tmp.
apply lucastest_prop_cor; auto.
case (Zle_lt_or_eq 2 q); auto.
apply prime_ge_2; auto.
intros H5; subst.
absurd (2 <= 1); auto with arith.
apply Zdivide_le; auto with zarith.
case H4; intros x Hx.
exists (2 ^ (Zpos p -1) - x).
rewrite Zmult_minus_distr_r; rewrite <- Hx; unfold Mp.
pattern 2 at 2; rewrite <- Zpower_1_r; rewrite <- Zpower_exp; auto with zarith.
replace (Zpos p - 1 + 1) with (Zpos p); auto with zarith.
Qed.

End test.

Definition znz_of_Z (w: univ_of_cycles) (op: ZnZ.Ops w) z :=
 match z with
 | Zpos p => snd (ZnZ.of_pos p)
 | _ => ZnZ.zero
 end.

Definition lucas p :=
 let op := cmk_op (Peano.pred (nat_of_P (get_height 63 p))) in
 let b := znz_of_Z op (Zpower 2 (Zpos p) - 1) in
 let zp := znz_of_Z op (Zpos p) in
 let mod_op := mmake_mod_op op b zp in
  lucastest op p mod_op.

Section LucasStep.

Let op p  := cmk_op (Peano.pred (nat_of_P (get_height 63 p))).
Let b p := znz_of_Z (op p) (2 ^ (Zpos p) - 1).
Let zp p := znz_of_Z (op p) (Zpos p).
Let mod_op p := mmake_mod_op (op p) (b p) (zp p).

Let lucas_f1 p : (2 < p)%positive -> Zpos p <= Zpos (ZnZ.digits (op p)).
Proof.
intros Hp.
unfold op, base; rewrite cmk_op_digits.
generalize (get_height_correct 63 p).
replace (Z_of_nat (Peano.pred (nat_of_P (get_height 63 p)))) with
       ((Zpos (get_height 63 p) - 1) ). auto with zarith.
rewrite pred_of_minus; rewrite inj_minus1.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
generalize (lt_O_nat_of_P (get_height 63 p)); auto with zarith.
Qed.

Let lucas_f2 p : (2 < p)%positive -> @ZnZ.to_Z _ (op p) (b p) = 2 ^ (Zpos p) - 1.
Proof.
unfold b; intros Hp.
assert (F1: 0 < 2 ^ (Zpos p) - 1).
assert (F2: 2 ^ 0 < 2 ^ (Zpos p)).
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_0_r in F2; auto with zarith.
case_eq (2 ^ (Zpos p) - 1); simpl ZnZ.to_Z.
intros HH; contradict F1; rewrite HH; auto with zarith.
2: intros p1 HH; contradict F1; rewrite HH;
  apply Zle_not_lt; red; simpl; intros; discriminate.
intros p1 Hp1; apply (@ZnZ.of_pos_correct _ (op p)); auto.
apply cmk_spec.
rewrite <- Hp1.
unfold base.
apply Z.lt_le_trans with (2 ^ (Zpos p)); auto with zarith.
apply Zpower_le_monotone; auto with zarith.
Qed.

Let lucas_f3 p :(2 < p)%positive -> mod_spec (op p) (b p) (mod_op p).
Proof.
intro Hp.
assert (F1 : ZnZ.Specs (op p)).
  apply cmk_spec; auto.
apply mmake_mod_spec with (p := p); auto.
rewrite lucas_f2; auto.
assert (F2: 2 ^ 1 < 2 ^ (Zpos p)).
apply Zpower_lt_monotone. auto with zarith.
assert (2 < Z.pos p); auto with zarith.
rewrite Zpower_1_r in F2; auto with zarith.
unfold zp.
apply ZnZ.of_Z_correct.
split. auto with zarith.
apply Z.le_lt_trans with (1 := lucas_f1 Hp).
unfold base; apply Zpower2_lt_lin; auto with zarith.
Qed.

Theorem lucas_prime:
 forall p, 2 < Zpos p -> lucas p = 0 -> prime (2 ^ Zpos p - 1).
intros p Hp H.
assert(A1: ZnZ.Specs (op p)).
apply cmk_spec; auto.
apply (lucastest_prime A1 Hp (lucas_f2 Hp) (lucas_f3 Hp) H).
Qed.

Definition lucas_step p x p1 :=
 let op := cmk_op (Peano.pred (nat_of_P (get_height 63 p))) in
 let b := znz_of_Z op (Zpower 2 (Zpos p) - 1) in
 let zp := znz_of_Z op (Zpos p) in
 let mod_op := mmake_mod_op op b zp in
  ZnZ.to_Z (lucastest_step op mod_op (znz_of_Z op x) p1).

Lemma lucasE p : 2 < Zpos p -> lucas_step p 4 (p - 2) = 0 -> lucas p = 0.
Proof.
intros H.
unfold lucas, lucas_step, lucastest.
set (o := cmk_op _).
set (m := mmake_mod_op _ _ _).
assert (F0 : 1 < ZnZ.to_Z (b p)).
replace (ZnZ.to_Z (b p)) with (2 ^ Z.pos p - 1).
assert (2 ^ 1 <  2 ^ Z.pos p).
apply Zpower_lt_monotone; auto with zarith.
replace (2 ^ 1) with 2 in H0; auto with zarith.
rewrite <-(lucas_f2 H); auto.
assert (F1 : ZnZ.to_Z ZnZ.one = 1).
rewrite w1_b with (p := p) (b := b p); auto.
rewrite Z.mod_small; auto with zarith.
apply cmk_spec; auto.
rewrite <-(lucas_f2 H); auto.
assert (F2 : ZnZ.to_Z ZnZ.one = 1 mod ZnZ.to_Z (b p)).
rewrite Z.mod_small; auto with zarith.
intro H1; rewrite <-H1.
assert (F3 : ZnZ.to_Z (add_mod m ZnZ.one ZnZ.one) = 2 mod ZnZ.to_Z (b p)).
rewrite (add_mod_spec (lucas_f3 H) _ _ 1 1); auto.
replace (ZnZ.to_Z ZnZ.one) with 1; auto.
apply lucastest_eq with (p := p) (b := b p); auto.
apply cmk_spec; auto.
apply lucas_f2; auto.
apply lucas_f3; auto.
rewrite (add_mod_spec (lucas_f3 H) _ _ 2 2); auto.
match goal with |- ?X < ?Y => enough (0 <= X < Y) by auto with zarith end.
apply Z.mod_pos_bound; auto with zarith.
rewrite (add_mod_spec (lucas_f3 H) _ _ 2 2); auto.
replace ((ZnZ.to_Z (add_mod m ZnZ.one ZnZ.one))) with (2 mod ZnZ.to_Z (b p)).
rewrite <-Z.add_mod.
rewrite Z.mod_small.
simpl.
apply sym_equal.
apply (@ZnZ.of_pos_correct _ o).
apply cmk_spec; auto.
change 4 with (2 ^ 2).
apply Zpower_lt_monotone. auto with zarith.
split. auto with zarith.
assert (F := lucas_f1 H).
unfold op in F; simpl in F; unfold o; auto with zarith.
split. auto with zarith.
change (2 + 2) with (2 ^ 2).
replace (ZnZ.to_Z (b p)) with (2 ^ Z.pos p - 1).
assert (2 ^ 3 <=  2 ^ Z.pos p).
apply Zpower_le_monotone; auto with zarith.
change (2 ^ 3) with 8 in H0.
change (2 ^ 2) with 4; auto with zarith.
rewrite <-(lucas_f2 H); auto.
generalize F0.
set (u := ZnZ.to_Z _).
auto with zarith.
Qed.

Theorem lucas_step_add p p1 p2 z z1 z2 :
   (2 < Zpos p) -> 0 <= z < 2 ^ (Zpos p) - 1 ->
   lucas_step p z p1 = z1 -> lucas_step  p z1 p2 = z2 -> lucas_step p z (p2 + p1) = z2.
Proof.
intros H H0 H1 H2.
assert(A1: ZnZ.Specs (op p)).
apply cmk_spec; auto.
unfold lucas_step.
set (o := cmk_op _).
set (m := mmake_mod_op _ _ _).
assert (F1 : forall z3, 0 <= z3 < ZnZ.to_Z (b p) -> ZnZ.to_Z (znz_of_Z o z3) = z3).
intro z3.
case z3; simpl.
rewrite ZnZ.spec_0; auto.
intros p3 [H3 H4].
apply ZnZ.of_pos_correct.
apply Z.lt_le_trans with (1 := H4).
replace (ZnZ.to_Z (b p)) with (2 ^ Z.pos p - 1).
enough (2 ^ Zpos p <= base (ZnZ.digits o)) by auto with zarith.
apply Zpower_le_monotone. auto with zarith.
assert (F := lucas_f1 H); auto with zarith.
rewrite <-(lucas_f2 H); auto.
intros p3 [[]]; unfold Z.le; simpl; auto.
unfold lucastest_step.
rewrite Pos.iter_add; auto.
change (@ZnZ.to_Z _ o (lucastest_step o m (lucastest_step o m (znz_of_Z o z) p1) p2) = z2).
assert (F :  ZnZ.to_Z (lucastest_step  o m (znz_of_Z o z) p1) =
            ZnZ.to_Z (znz_of_Z o z1)).
unfold lucas_step in H1; fold o in H1; fold m in H1; rewrite H1.
rewrite F1. reflexivity.
rewrite <- H1.
apply (lucastest_bounded A1 H (lucas_f2 H) (lucas_f3 H)).
rewrite F1.
rewrite (lucas_f2 H); auto with zarith.
replace (ZnZ.to_Z (b p)) with (2 ^ Z.pos p - 1). auto with zarith.
rewrite <-(lucas_f2 H); auto with zarith.
rewrite lucastest_eq with (p := p) (b := b p) (6 := F); auto.
apply lucas_f2; auto.
apply lucas_f3; auto.
assert (0 <=  ZnZ.to_Z (lucastest_step o m (znz_of_Z o z) p1) < ZnZ.to_Z (b p)).
apply (lucastest_bounded A1 H (lucas_f2 H) (lucas_f3 H)).
rewrite F1.
replace (ZnZ.to_Z (b p)) with (2 ^ Z.pos p - 1). auto with zarith.
rewrite <-(lucas_f2 H); auto with zarith.
replace (ZnZ.to_Z (b p)) with (2 ^ Z.pos p - 1). auto with zarith.
rewrite <-(lucas_f2 H); auto with zarith.
auto with zarith.
Qed.

Lemma lucas_step_same_p : forall p x p1 p2 z,
   p1 = p2 -> lucas_step p x p1 = z -> lucas_step p x p2 = z.
Proof.
intros p x p1 p2 z Hp Hz.
apply trans_equal with (2 := Hz).
apply f_equal2 with (f := lucas_step p); auto.
Qed.

End LucasStep.

Ltac vmtac :=
match goal with |- _ = ?x =>
vm_cast_no_check  (refl_equal x)
end.

Lemma lucas_Zpos p : 2 < Zpos p -> 0 <= 4 < 2 ^ (Zpos p) - 1.
Proof.
intros H; split; auto with zarith.
assert (8 <= 2 ^Zpos p); auto with zarith.
replace 8 with (2 ^ 3); auto with zarith.
apply Zpow_facts.Zpower_le_monotone; auto with zarith.
Qed.
