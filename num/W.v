Set Implicit Arguments.

Require Import Basic_type.
Require Import ZnZ.
Require Import Zn2Z.
Require Import W2_op.
Require Import ZArith.

(* ** Type of words ** *)


(* Make the words *)

Definition mk_word (w: Set) (n:nat): Set.
fix 2.
intros w n; case n; simpl.
exact w2.
intros n1; exact (zn2z (mk_word w n1)).
Defined.

(* Make the op *)

Fixpoint mk_op (w : Set) (op : znz_op w) (n : nat) {struct n} :
  znz_op (word w n) :=
  match n as n0 return (znz_op (word w n0)) with
  | O => op
  | S n1 => mk_zn2z_op_karatsuba (mk_op op n1)
  end.

Theorem mk_op_digits: forall w (op: znz_op w) n, 
  (Zpos (znz_digits (mk_op op n)) = 2 ^ Z_of_nat n * Zpos (znz_digits op))%Z.
intros w op n; elim n; simpl mk_op; auto; clear n.
intros n Rec; simpl znz_digits.
rewrite Zpos_xO; rewrite Rec.
rewrite Zmult_assoc; apply f_equal2 with (f := Zmult); auto.
rewrite inj_S; unfold Zsucc; rewrite Zplus_comm.
rewrite Zpower_exp; auto with zarith.
Qed.

(* ** Operators ** *)
Definition w2_1_op := mk_zn2z_op w2_op.           
Definition w2_2_op := mk_zn2z_op w2_1_op.
Definition w2_3_op := mk_zn2z_op w2_2_op.
Definition w2_4_op := mk_zn2z_op_karatsuba w2_3_op.
Definition w2_5_op := mk_zn2z_op_karatsuba w2_4_op.
Definition w2_6_op := mk_zn2z_op_karatsuba w2_5_op.
Definition w2_7_op := mk_zn2z_op_karatsuba w2_6_op.
Definition w2_8_op := mk_zn2z_op_karatsuba w2_7_op.
Definition w2_9_op := mk_zn2z_op_karatsuba w2_8_op.
Definition w2_10_op := mk_zn2z_op_karatsuba w2_9_op.
Definition w2_11_op := mk_zn2z_op_karatsuba w2_10_op.
Definition w2_12_op := mk_zn2z_op_karatsuba w2_11_op.
Definition w2_13_op := mk_zn2z_op_karatsuba w2_12_op.
Definition w2_14_op := mk_zn2z_op_karatsuba w2_13_op.

Definition cmk_op (n: nat): znz_op (word w2 n).
intros n; case n; clear n.
exact w2_op.
intros n; case n; clear n.
exact w2_1_op.
intros n; case n; clear n.
exact w2_2_op.
intros n; case n; clear n.
exact w2_3_op.
intros n; case n; clear n.
exact w2_4_op.
intros n; case n; clear n.
exact w2_5_op.
intros n; case n; clear n.
exact w2_6_op.
intros n; case n; clear n.
exact w2_7_op.
intros n; case n; clear n.
exact w2_8_op.
intros n; case n; clear n.
exact w2_9_op.
intros n; case n; clear n.
exact w2_10_op.
intros n; case n; clear n.
exact w2_11_op.
intros n; case n; clear n.
exact w2_12_op.
intros n; case n; clear n.
exact w2_13_op.
intros n; case n; clear n.
exact w2_14_op.
intros n.
match goal with |- context[S ?X] =>
 exact (mk_op w2_op (S X))
end.
Defined.

Theorem cmk_op_digits: forall n, 
  (Zpos (znz_digits (cmk_op n)) = 2 ^ Z_of_nat (S n))%Z.
do 15 (intros n; case n; clear n; [reflexivity | idtac]).
intros n; unfold cmk_op; lazy beta.
rewrite mk_op_digits.
simpl znz_digits.
match goal with |- (_ = 2 ^ Z_of_nat (S ?X))%Z =>
  rewrite (inj_S X)
end; unfold Zsucc; rewrite Zpower_exp; auto with zarith.
Qed.
