(**********************************************************************
    ZPowerAux.v                                                                                           
                                                                                                          
     Auxillary functions & Theorems for Zpower                                             
                                                                                                          
                                                                                                          
                                    Laurent.Thery@inria.fr (2005)                  
  **********************************************************************)
Require Export ZArith.
Require Export Znumtheory.
Require Export Tactic.

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

Hint Resolve Zlt_gt Zle_ge: zarith.

(**************************************
  Properties Zpower
**************************************)

Theorem Zpower_1: forall a, 0 <= a ->  1 ^ a = 1.
intros a Ha; pattern a; apply natlike_ind; auto with zarith.
intros x Hx Hx1; unfold Zsucc.
rewrite Zpower_exp; auto with zarith.
rewrite Hx1; simpl; auto.
Qed.

Theorem Zpower_exp_0: forall a,  a ^ 0 = 1.
simpl; unfold Zpower_pos; simpl; auto with zarith.
Qed.

Theorem Zpower_exp_1: forall a,  a ^ 1 = a.
simpl; unfold Zpower_pos; simpl; auto with zarith.
Qed.

Theorem Zpower_Zabs: forall a b,  Zabs (a ^ b) = (Zabs a) ^ b.
intros a b; case (Zle_or_lt 0 b).
intros Hb; pattern b; apply natlike_ind; auto with zarith.
intros x Hx Hx1; unfold Zsucc.
(repeat rewrite Zpower_exp); auto with zarith.
rewrite Zabs_Zmult; rewrite Hx1.
eq_tac; auto.
replace (a ^ 1) with a; auto.
simpl; unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto.
simpl; unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto.
case b; simpl; auto with zarith.
intros p Hp; discriminate.
Qed.

Theorem Zpower_Zsucc: forall p n,  0 <= n -> p ^Zsucc n = p * p ^ n.
intros p n H.
unfold Zsucc; rewrite Zpower_exp; auto with zarith.
rewrite Zpower_exp_1; apply Zmult_comm.
Qed.

Theorem Zpower_mult: forall p q r,  0 <= q -> 0 <=  r -> p ^ (q * r) = (p ^ q) ^
 r.
intros p q r H1 H2; generalize H2; pattern r; apply natlike_ind; auto.
intros H3; rewrite Zmult_0_r; repeat rewrite Zpower_exp_0; auto.
intros r1 H3 H4 H5.
unfold Zsucc; rewrite Zpower_exp; auto with zarith.
rewrite <- H4; try rewrite Zpower_exp_1; try rewrite <- Zpower_exp; try eq_tac;
auto with zarith.
ring.
Qed.

Theorem Zpower_lt_0: forall a b: Z, 0 < a -> 0 <= b-> 0 < a ^b.
intros a b; case b; auto with zarith.
simpl; intros; auto with zarith.
2: intros p H H1; case H1; auto.
intros p H1 H; generalize H; pattern (Zpos p); apply natlike_ind; auto.
intros; case a; compute; auto.
intros p1 H2 H3 _; unfold Zsucc; rewrite Zpower_exp; simpl; auto with zarith.
apply Zmult_lt_O_compat; auto with zarith.
generalize H1; case a; compute; intros; auto; discriminate.
Qed.

Theorem Zpower_le_monotone: forall a b c: Z, 0 < a -> 0 <= b <= c -> a ^ b <= a ^ c.
intros a b c H (H1, H2).
rewrite <- (Zmult_1_r (a ^ b)); replace c with (b + (c - b)); auto with zarith.
rewrite Zpower_exp; auto with zarith.
apply Zmult_le_compat_l; auto with zarith.
assert (0 < a ^ (c - b)); auto with zarith.
apply Zpower_lt_0; auto with zarith.
apply Zlt_le_weak; apply Zpower_lt_0; auto with zarith.
Qed.


Theorem Zpower_le_0: forall a b: Z, 0 <= a -> 0 <= a ^b. 
intros a b; case b; auto with zarith.
simpl; auto with zarith.
intros p H1; assert (H: 0 <= Zpos p); auto with zarith.
generalize H; pattern (Zpos p); apply natlike_ind; auto.
intros p1 H2 H3 _; unfold Zsucc; rewrite Zpower_exp; simpl; auto with zarith.
apply Zmult_le_0_compat; auto with zarith.
generalize H1; case a; compute; intros; auto; discriminate.
Qed.

Hint Resolve Zpower_le_0 Zpower_lt_0: zarith.

Theorem Zpower_prod: forall p q r,  0 <= q -> 0 <=  r -> (p * q) ^ r = p ^ r * q ^ r.
intros p q r H1 H2; generalize H2; pattern r; apply natlike_ind; auto.
intros r1 H3 H4 H5.
unfold Zsucc; rewrite Zpower_exp; auto with zarith.
rewrite  H4;  repeat (rewrite Zpower_exp_1 || rewrite Zpower_exp); auto with zarith; ring.
Qed.

Theorem Zpower_le_monotone_exp: forall a b c: Z, 0 <= c -> 0 <= a <= b -> a ^ c <=  b ^ c.
intros a b c H (H1, H2).
generalize H; pattern c; apply natlike_ind; auto.
intros x HH HH1 _; unfold Zsucc; repeat rewrite Zpower_exp; auto with zarith.
repeat rewrite Zpower_exp_1.
apply Zle_trans with (a ^x * b); auto with zarith.
Qed.

