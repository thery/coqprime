Require Import ZArith Zpow_facts.

Open Scope Z_scope.

Fixpoint plength (p: positive) : positive :=
  match p with
    xH => xH
  | xO p1 => Pos.succ (plength p1)
  | xI p1 => Pos.succ (plength p1)
  end.

Theorem plength_correct: forall p, (Zpos p < 2 ^ Zpos (plength p))%Z.
assert (F: (forall p, 2 ^ (Zpos (Pos.succ p)) = 2 * 2 ^ Zpos p)%Z).
intros p; replace (Zpos (Pos.succ p)) with (1 + Zpos p)%Z.
rewrite Zpower_exp. 1-2: auto with zarith.
red; intros; discriminate.
rewrite Zpos_succ_morphism; unfold Z.succ; auto with zarith.
intros p; elim p; simpl plength; auto.
intros p1 Hp1; rewrite F; repeat rewrite Zpos_xI.
assert (tmp: (forall p, 2 * p = p + p)%Z);
  try repeat rewrite tmp; auto with zarith.
intros p1 Hp1; rewrite F; rewrite (Zpos_xO p1).
assert (tmp: (forall p, 2 * p = p + p)%Z);
  try repeat rewrite tmp; auto with zarith.
rewrite Zpower_1_r; auto with zarith.
Qed.

Theorem plength_pred_correct: forall p, (Zpos p <= 2 ^ Zpos (plength (Pos.pred p)))%Z.
intros p; case (Psucc_pred p); intros H1.
subst; simpl plength.
rewrite Zpower_1_r; auto with zarith.
pattern p at 1; rewrite <- H1.
rewrite Zpos_succ_morphism; unfold Z.succ; auto with zarith.
generalize (plength_correct (Pos.pred p)); auto with zarith.
Qed.

Definition Pdiv p q :=
  match Z.div (Zpos p) (Zpos q) with
    Zpos q1 => match (Zpos p) - (Zpos q) * (Zpos q1) with
                 Z0 => q1
               | _ => (Pos.succ q1)
               end
  |  _ => xH
  end.

Theorem Pdiv_le: forall p q,
  Zpos p <= Zpos q * Zpos (Pdiv p q).
intros p q.
unfold Pdiv.
assert (H1: Zpos q > 0); auto with zarith.
assert (H1b: Zpos p >= 0).
  red; intros; discriminate.
generalize (Z_div_ge0 (Zpos p) (Zpos q) H1 H1b).
generalize (Z_div_mod_eq (Zpos p) (Zpos q) H1); case Z.div.
  intros HH _; rewrite HH; rewrite Zmult_0_r; rewrite Zmult_1_r; simpl.
case (Z_mod_lt (Zpos p) (Zpos q) H1); auto with zarith.
intros q1 H2.
replace (Zpos p - Zpos q * Zpos q1) with (Zpos p mod Zpos q).
  2: pattern (Zpos p) at 2; rewrite H2; auto with zarith.
generalize H2 (Z_mod_lt (Zpos p) (Zpos q) H1); clear H2;
  case Zmod.
  intros HH _; rewrite HH; auto with zarith.
  intros r1 HH (_,HH1); rewrite HH; rewrite Zpos_succ_morphism.
  unfold Z.succ; rewrite Zmult_plus_distr_r; auto with zarith.
  intros r1 _ (HH,_); case HH; auto.
intros q1 HH; rewrite HH.
unfold Z.ge; simpl Z.compare; intros HH1; case HH1; auto.
Qed.

Definition is_one p := match p with xH => true | _ => false end.

Theorem is_one_one: forall p, is_one p = true -> p = xH.
intros p; case p; auto; intros p1 H1; discriminate H1.
Qed.

Definition get_height digits p :=
  let r := Pdiv p digits in
   if is_one r then xH else Pos.succ (plength (Pos.pred r)).

Theorem get_height_correct:
  forall digits N,
   Zpos N <= Zpos digits * (2 ^ (Zpos (get_height digits N) -1)).
intros digits N.
unfold get_height.
assert (H1 := Pdiv_le N digits).
case_eq (is_one (Pdiv N digits)); intros H2.
rewrite (is_one_one _ H2) in H1.
rewrite Zmult_1_r in H1.
change (2^(1-1))%Z with 1; rewrite Zmult_1_r; auto.
clear H2.
apply Z.le_trans with (1 := H1).
apply Zmult_le_compat_l; auto with zarith.
rewrite Zpos_succ_morphism; unfold Z.succ.
rewrite Zplus_comm; rewrite Zminus_plus.
apply plength_pred_correct.
Qed.
