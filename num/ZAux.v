(**********************************************************************
     Aux.v                                                                                           
                                                                                                          
     Auxillary functions & Theorems                                              
                                                                                                          
                                                                                                          
                                    Laurent.Thery@inria.fr (2003)                  
  **********************************************************************)
Require Export ZArith.
Require Export Znumtheory.
Require Export Tactic.
(* Require Import MOmega. *)


Open Scope Z_scope. 

Hint  Extern 2 (Zle _ _) => 
 (match goal with
   |- Zpos _ <= Zpos _ => exact (refl_equal _)
|   H: _ <=  ?p |- _ <= ?p => apply Zle_trans with (2 := H)
|   H: _ <  ?p |- _ <= ?p => apply Zlt_le_weak; apply Zle_lt_trans with (2 := H)
  end).

Hint  Extern 2 (Zlt _ _) => 
 (match goal with
   |- Zpos _ < Zpos _ => exact (refl_equal _)
|      H: _ <=  ?p |- _ <= ?p => apply Zlt_le_trans with (2 := H)
|   H: _ <  ?p |- _ <= ?p => apply Zle_lt_trans with (2 := H)
  end).

(************************************** 
   Properties of order and product
 **************************************)

Theorem Zmult_interval: forall p q, 0 < p * q  -> 1 < p -> 0 < q < p * q.
intros p q H1 H2; assert (0 < q).
case (Zle_or_lt q 0); auto; intros H3; contradict H1; apply Zle_not_lt.
rewrite <- (Zmult_0_r p).
apply Zmult_le_compat_l; auto with zarith.
split; auto.
pattern q at 1; rewrite <- (Zmult_1_l q).
apply Zmult_lt_compat_r; auto with zarith.
Qed.

Theorem Zmult_lt_compat: forall n m p q : Z, 0 < n <= p -> 0 < m < q -> n * m < p * q.
intros n m p q (H1, H2) (H3, H4).
apply Zle_lt_trans with (p * m).
apply Zmult_le_compat_r; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
Qed.

Theorem Zle_square_mult: forall a b, 0 <= a <= b -> a * a <= b * b.
intros a b (H1, H2); apply Zle_trans with (a * b); auto with zarith.
Qed.

Theorem Zlt_square_mult: forall a b, 0 <= a < b -> a * a < b * b.
intros a b (H1, H2); apply Zle_lt_trans with (a * b); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
Qed.

Theorem Zlt_square_mult_inv: forall a b, 0 <= a -> 0 <= b -> a * a < b * b -> a < b.
intros a b H1 H2 H3; case (Zle_or_lt b a); auto; intros H4; apply Zmult_lt_reg_r with a; 
   contradict H3; apply Zle_not_lt; apply Zle_square_mult; auto.
Qed.

(************************************** 
  Some properties of Zodd and Zeven
**************************************)

Theorem Zeven_ex: forall p, Zeven p -> exists q, p = 2 * q.
intros p; case p; simpl; auto.
intros _; exists 0; auto.
intros p1; case p1; try ((intros H; case H; fail) || intros z H; case H; fail).
intros p2 _; exists (Zpos p2); auto.
intros p1; case p1; try ((intros H; case H; fail) || intros z H; case H; fail).
intros p2 _; exists (Zneg p2); auto.
Qed.

Theorem Zodd_ex: forall p, Zodd p -> exists q, p = 2 * q + 1.
intros p HH; case (Zle_or_lt 0 p); intros HH1.
exists (Zdiv2 p); apply Zodd_div2; auto with zarith.
exists ((Zdiv2 p) - 1); pattern p at 1; rewrite Zodd_div2_neg; auto with zarith.
Qed.

Theorem Zeven_2p: forall p, Zeven (2 * p).
intros p; case p; simpl; auto.
Qed.

Theorem Zodd_2p_plus_1: forall p, Zodd (2 * p + 1).
intros p; case p; simpl; auto.
intros p1; case p1; simpl; auto.
Qed.

Theorem Zeven_plus_Zodd_Zodd: forall z1 z2, Zeven z1 -> Zodd z2 -> Zodd (z1 + z2).
intros z1 z2 HH1 HH2; case Zeven_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
case Zodd_ex with (1 := HH2); intros y HH4; try rewrite HH4; auto.
replace (2 * x + (2 * y + 1)) with (2 * (x + y) + 1); try apply Zodd_2p_plus_1; auto with zarith.
Qed.

Theorem Zeven_plus_Zeven_Zeven: forall z1 z2, Zeven z1 -> Zeven z2 -> Zeven (z1 + z2).
intros z1 z2 HH1 HH2; case Zeven_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
case Zeven_ex with (1 := HH2); intros y HH4; try rewrite HH4; auto.
replace (2 * x + 2 * y) with (2 * (x + y)); try apply Zeven_2p; auto with zarith.
Qed.

Theorem Zodd_plus_Zeven_Zodd: forall z1 z2, Zodd z1 -> Zeven z2 -> Zodd (z1 + z2).
intros z1 z2 HH1 HH2; rewrite Zplus_comm; apply Zeven_plus_Zodd_Zodd; auto.
Qed.

Theorem Zodd_plus_Zodd_Zeven: forall z1 z2, Zodd z1 -> Zodd z2 -> Zeven (z1 + z2).
intros z1 z2 HH1 HH2; case Zodd_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
case Zodd_ex with (1 := HH2); intros y HH4; try rewrite HH4; auto.
replace ((2 * x + 1) + (2 * y + 1)) with (2 * (x + y + 1)); try apply Zeven_2p; try ring.
Qed.

Theorem Zeven_mult_Zeven_l: forall z1 z2, Zeven z1 -> Zeven (z1 * z2).
intros z1 z2 HH1; case Zeven_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
replace (2 * x * z2) with (2 * (x * z2)); try apply Zeven_2p; auto with zarith.
Qed.

Theorem Zeven_mult_Zeven_r: forall z1 z2, Zeven z2 -> Zeven (z1 * z2).
intros z1 z2 HH1; case Zeven_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
replace (z1 * (2 * x)) with (2 * (x * z1)); try apply Zeven_2p; try ring.
Qed.

Theorem Zodd_mult_Zodd_Zodd: forall z1 z2, Zodd z1 -> Zodd z2 -> Zodd (z1 * z2).
intros z1 z2 HH1 HH2; case Zodd_ex with (1 := HH1); intros x HH3; try rewrite HH3; auto.
case Zodd_ex with (1 := HH2); intros y HH4; try rewrite HH4; auto.
replace ((2 * x + 1) * (2 * y + 1)) with (2 * (2 * x * y + x + y) + 1); try apply Zodd_2p_plus_1; try ring.
Qed.

Definition Zmult_lt_0_compat := Zmult_lt_O_compat.

Hint Rewrite Zmult_1_r Zmult_0_r Zmult_1_l Zmult_0_l Zplus_0_l Zplus_0_r Zminus_0_r: rm10.
Hint Rewrite Zmult_plus_distr_r Zmult_plus_distr_l Zmult_minus_distr_r Zmult_minus_distr_l: distr.

Theorem Zmult_lt_compat_bis:
    forall n m p q : Z, 0 <= n < p -> 0 <= m < q -> n * m < p * q.
intros n m p q (H1, H2) (H3,H4).
case Zle_lt_or_eq with (1 := H1); intros H5; auto with zarith.
case Zle_lt_or_eq with (1 := H3); intros H6; auto with zarith.
apply Zlt_trans with (n * q).
apply Zmult_lt_compat_l; auto.
apply Zmult_lt_compat_r; auto with zarith.
rewrite <- H6; autorewrite with rm10; apply Zmult_lt_0_compat; auto with zarith.
rewrite <- H5; autorewrite with rm10; apply Zmult_lt_0_compat; auto with zarith.
Qed.


Theorem nat_of_P_xO: 
  forall p,  nat_of_P (xO p) =  (2 * nat_of_P p)%nat.
intros p; unfold nat_of_P; simpl; rewrite Pmult_nat_2_mult_2_permute; auto with arith.
Qed.

Theorem nat_of_P_xI: 
  forall p,  nat_of_P (xI p) =  (2 * nat_of_P p + 1)%nat.
intros p; unfold nat_of_P; simpl; rewrite Pmult_nat_2_mult_2_permute; auto with arith.
rewrite S_to_plus_one;  ring.
Qed.

Theorem nat_of_P_xH: nat_of_P xH = 1%nat.
trivial.
Qed.

Hint Rewrite
  nat_of_P_xO nat_of_P_xI nat_of_P_xH
  nat_of_P_succ_morphism
  nat_of_P_plus_carry_morphism
  nat_of_P_plus_morphism
  nat_of_P_mult_morphism
  nat_of_P_minus_morphism: pos_morph.

Ltac pos_tac :=
  match goal with |- ?X = ?Y => 
    assert (tmp: Zpos X = Zpos Y); 
     [idtac; repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P; eq_tac | injection tmp; auto]
  end; autorewrite with pos_morph.


Close Scope Z_scope.
