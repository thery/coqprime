(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Import ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import List.
Require Import Lia.
Require Import UList.

Section ZnZ.

Variable n: Z.
Hypothesis n_pos: 0 < n.

Structure znz: Set:=
 mkznz {val: Z;
        inZnZ: val = Zmod val n}.

Theorem znz_inj: forall a b, a = b -> val a = val b.
intros; subst; auto.
Qed.

Theorem Zeq_iok: forall x y, x = y -> Zeq_bool x y = true.
intros x y H; subst.
unfold Zeq_bool; rewrite Z.compare_refl; auto.
Qed.

Lemma modz: forall x,
  (x mod n) = (x mod n) mod n.
intros x; rewrite Zmod_mod; auto with zarith.
Qed.

Definition zero:= mkznz _ (modz 0).

Definition one:= mkznz _ (modz 1).

Definition add v1 v2 := mkznz _ (modz (val v1 + val v2)).

Definition sub v1 v2 := mkznz _ (modz (val v1 - val v2)).

Definition mul v1 v2 := mkznz _ (modz (val v1 * val v2)).

Definition opp v := mkznz _ (modz (-val v)).


Theorem zirr: forall x1 x2 H1 H2,
 x1 = x2 -> mkznz x1 H1 = mkznz x2 H2.
Proof.
intros x1 x2 H1 H2 H3.
subst x1.
rewrite (fun H => eq_proofs_unicity H H1 H2); auto.
intros x y; case (Z.eq_dec x y); auto.
Qed.

Lemma znz1: forall x, x mod 1 = 0.
intros x; apply Zdivide_mod; auto with zarith.
Qed.

Definition RZnZ:  ring_theory zero one add mul sub opp (@eq znz).
split; auto.
intros p; case p; intros x H;
   refine (zirr _ _ _ _ _); simpl; auto.
intros [x Hx] [y Hy].
  refine (zirr _ _ _ _ _); simpl.
  rewrite Zplus_comm; auto.
intros [x Hx] [y Hy] [z Hz].
  refine (zirr _ _ _ _ _); simpl.
  rewrite Zplus_mod; auto.
  rewrite (Zplus_mod((x + y) mod n)); auto.
  repeat rewrite Zmod_mod; auto.
  repeat rewrite <- Zplus_mod; auto; rewrite Zplus_assoc; auto.
intros p; case p; intros x H.
   refine (zirr _ _ _ _ _); simpl.
   case (Zle_lt_or_eq 1 n); auto with zarith; intros Hz.
     rewrite (Zmod_small 1); auto with zarith.
     rewrite Zmult_1_l; auto.
     clear p; subst n; rewrite znz1; rewrite H; rewrite znz1; auto.
intros [x Hx] [y Hy].
  refine (zirr _ _ _ _ _); simpl.
  rewrite Zmult_comm; auto.
intros [x Hx] [y Hy] [z Hz].
  refine (zirr _ _ _ _ _); simpl.
  rewrite Zmult_mod; auto.
  rewrite (Zmult_mod ((x * y) mod n)); auto.
  repeat rewrite Zmod_mod; auto.
  repeat rewrite <- Zmult_mod; auto; rewrite Zmult_assoc; auto.
intros [x Hx] [y Hy] [z Hz].
  refine (zirr _ _ _ _ _); simpl.
  rewrite Zmult_mod; auto.
  rewrite Zmod_mod; auto.
  rewrite <- Zmult_mod; auto.
  rewrite (Zplus_mod ((x*z) mod n)); auto.
  repeat rewrite Zmod_mod; auto.
  rewrite <- Zplus_mod; auto.
  apply f_equal2 with (f := Zmod); auto; ring.
intros [x Hx] [y Hy].
  refine (zirr _ _ _ _ _); simpl.
  rewrite Zplus_mod; auto.
  repeat rewrite Zmod_mod; auto.
  rewrite <- Zplus_mod; auto.
intros [x Hx].
  refine (zirr _ _ _ _ _); simpl.
  rewrite Zplus_mod; auto.
  repeat rewrite Zmod_mod; auto.
  rewrite <- Zplus_mod; auto.
  apply f_equal2 with (f := Zmod); auto; ring.
Defined.

Add Ring RZnZ : RZnZ.

(* It is finite *)
Fixpoint mklist (n: nat): list nat :=
  match n with O => nil | (S n) => cons n (mklist n) end.

Lemma mklist_length: forall n1, length (mklist n1) = n1.
Proof.
intros n1; elim n1; simpl; auto; clear n1.
Qed.

Theorem mklist_lt: forall n1 x, (In x (mklist n1)) -> (x < n1)%nat.
intros n1; elim n1; simpl; auto; clear n1.
 intros x H; case H.
intros n1 Hrec x [H1 | H1]; try subst x; auto with arith.
Qed.

Theorem lt_mklist_lt: forall n1 x, (x < n1)%nat -> (In x (mklist n1)).
intros n1 x H; elim H; simpl; auto.
Qed.

Theorem uniq_mklist: forall m, ulist (mklist m).
intros m; elim m; simpl; auto; clear m.
intros m H; constructor; auto.
intros H1; absurd (m < m)%nat; auto with arith.
apply mklist_lt; auto.
Qed.

Theorem nat_z_kt: forall x, (x < Z.abs_nat n)%nat -> (Z_of_nat x) = (Z_of_nat x) mod n.
Proof. intros x H; rewrite Zmod_small; lia. Qed.

Definition mkzlist:
  forall (l: list nat), (forall x, In x l -> (x < Z.abs_nat n)%nat) -> list znz.
fix mkzlist 1; intros l; case l.
  intros; exact nil.
intros n1 l1 Hn.
  assert (F1: forall x, In x l1 -> (x < Z.abs_nat n)%nat).
    intros; apply Hn; simpl; auto.
  assert (F2: (n1 < Z.abs_nat n)%nat).
    apply Hn; simpl; auto.
  exact (cons (mkznz _ (nat_z_kt _ F2)) (mkzlist _ F1)).
Defined.

Lemma mkzlist_length: forall l H, length (mkzlist l H) = length l.
Proof.
intros l; elim l; simpl; auto; clear l.
Qed.

Theorem in_mkzlist:
   forall l a Ha Hl, In (mkznz (Z_of_nat a) Ha) (mkzlist l Hl) -> In a l.
intros l1; elim l1; simpl; auto; clear l1.
intros a1 l1 Hrec1 a2 l2 Hl2 [H4 | H4].
generalize (znz_inj _ _ H4); simpl; clear H4; intros H4; left.
rewrite <- (Zabs_nat_Z_of_nat a1); rewrite H4; rewrite Zabs_nat_Z_of_nat; auto.
right; apply (Hrec1 _ _ _ H4).
Qed.

Theorem mkzlist_in:
   forall l a Ha Hl, In (Z.abs_nat a) l -> In (mkznz a Ha) (mkzlist l Hl).
intros l1; elim l1; simpl; auto; clear l1.
intros a1 l1 Hrec1 a2 l2 Hl2 [H4 | H4]; auto.
  left; apply zirr; auto.
  rewrite H4; rewrite inj_Zabs_nat; auto.
  rewrite Z.abs_eq; auto with zarith.
  case (Z_mod_lt a2 n); auto with zarith.
Qed.

Theorem mkzlist_uniq: forall l H,
  ulist l -> ulist (mkzlist l H).
intros l H H1; generalize H; elim H1; simpl; auto; clear l H H1.
intros a l H1 H2 Hrec H3; constructor; auto.
  intros HH; case H1; generalize HH; clear HH H1.
  assert (F1: forall l a Ha Hl, In (mkznz (Z_of_nat a) Ha) (mkzlist l Hl) -> In a l); auto.
    intros l1; elim l1; simpl; auto; clear l1.
    intros a1 l1 Hrec1 a2 l2 Hl2 [H4 | H4].
      generalize (znz_inj _ _ H4); simpl; clear H4; intros H4; left.
      rewrite <- (Zabs_nat_Z_of_nat a1); rewrite H4; rewrite Zabs_nat_Z_of_nat; auto.
    right; apply (Hrec1 _ _ _ H4).
  apply in_mkzlist.
Qed.

Definition all_znz: list znz :=
  (mkzlist (mklist (Z.abs_nat n)) (mklist_lt _)).


Lemma all_znz_length: length all_znz = (Z.abs_nat n).
Proof.
unfold all_znz; rewrite mkzlist_length.
rewrite mklist_length; auto.
Qed.

Theorem uniq_all_znz: ulist all_znz.
unfold all_znz; apply mkzlist_uniq.
apply uniq_mklist.
Qed.

Theorem in_all_znz: forall z, In z all_znz.
intros (z1, Hz1).
unfold all_znz; apply mkzlist_in.
apply lt_mklist_lt.
case (Z_mod_lt z1 n). auto with zarith.
rewrite <- Hz1; intros H1 H2.
case (le_or_lt (Z.abs_nat n) (Z.abs_nat z1)); auto; intros H3.
absurd (z1 < n); auto; apply Zle_not_lt.
rewrite <- Z.abs_eq; auto.
rewrite <- inj_Zabs_nat; auto.
rewrite <- (Z.abs_eq n) by auto with zarith.
rewrite <- (inj_Zabs_nat n); auto.
apply inj_le; auto.
Qed.

End ZnZ.


Require Import Field.
Require Import Pmod.

Section ZpZ.

Variable p: Z.
Variable p_prime: prime p.

Theorem p_pos: 0 < p.
generalize (prime_ge_2 _ p_prime); auto with zarith.
Qed.

Definition inv v := mkznz _ _ (modz p (fst (fst (Zegcd (val p v) p)))).

Definition div v1 v2 := mul _ v1 (inv v2).

Definition FZpZ:  field_theory (zero _) (one _)
                               (add _) (mul _)
                              (sub _) (opp _)
                               div inv (@eq (znz p)).
assert (Hmp := p_pos).
split; auto.
exact (RZnZ _ p_pos).
intros H; injection H; repeat rewrite Zmod_small;
  auto with zarith.
generalize (prime_ge_2 _ p_prime); auto with zarith.
intros (n, Hn); unfold zero, one, inv, mul; simpl.
intros H; apply zirr.
generalize (Zegcd_is_egcd n p); case Zegcd; intros (u,v) w (Hu, (Hv, Hw));
  simpl.
assert (F1: rel_prime n p).
  apply rel_prime_le_prime; auto.
  rewrite Hn; auto.
case (Z_mod_lt n p); try (intros H1 H2; split); auto with zarith.
case (Zle_lt_or_eq _ _ H1); auto with zarith.
rewrite <- Hn; intros H3;
  case H; apply zirr; rewrite <- H3; auto.
red in F1.
case (Zis_gcd_unique _ _ _ _ Hv F1);
  auto with zarith;
 intros; subst w.
rewrite <- H0.
rewrite Zmult_mod; repeat rewrite Zmod_mod; try rewrite <- Zmult_mod;
  auto.
rewrite Z_mod_plus; auto with zarith.
Defined.

End ZpZ.
