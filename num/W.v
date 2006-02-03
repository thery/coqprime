Set Implicit Arguments.

Require Import Basic_type.
Require Import ZnZ.
Require Import Zn2Z.
Require Import W2_op.
Require Import ZArith.
Require Import MkSpec.

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
  match n return (znz_op (word w n)) with
  | O => op
  | S n1 => mk_zn2z_op_karatsuba (mk_op op n1)
  end.

Fixpoint mk_spec (w : Set) (op : znz_op w) (op_spec : znz_spec op) (n : nat)
            {struct n} : znz_spec (mk_op op n) :=
  match n return (znz_spec (mk_op op n)) with
  | O => op_spec
  | S n1 =>
      mk_znz2_karatsuba_spec (word w n1) (mk_op op n1)
        (mk_spec op_spec n1)
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

Require Import W2_op_spec.

Definition cmk_spec n: znz_spec (cmk_op n).
assert (S1: znz_spec w2_1_op).
unfold w2_1_op; apply mk_znz2_spec.
exact w2_op_spec.
assert (S2: znz_spec w2_2_op).
unfold w2_2_op; apply mk_znz2_spec.
exact S1.
assert (S3: znz_spec w2_3_op).
unfold w2_3_op; apply mk_znz2_spec.
exact S2.
assert (S4: znz_spec w2_4_op).
unfold w2_4_op; apply mk_znz2_karatsuba_spec.
exact S3.
assert (S5: znz_spec w2_5_op).
unfold w2_5_op; apply mk_znz2_karatsuba_spec.
exact S4.
assert (S6: znz_spec w2_6_op).
unfold w2_6_op; apply mk_znz2_karatsuba_spec.
exact S5.
assert (S7: znz_spec w2_7_op).
unfold w2_7_op; apply mk_znz2_karatsuba_spec.
exact S6.
assert (S8: znz_spec w2_8_op).
unfold w2_8_op; apply mk_znz2_karatsuba_spec.
exact S7.
assert (S9: znz_spec w2_9_op).
unfold w2_9_op; apply mk_znz2_karatsuba_spec.
exact S8.
assert (S10: znz_spec w2_10_op).
unfold w2_10_op; apply mk_znz2_karatsuba_spec.
exact S9.
assert (S11: znz_spec w2_11_op).
unfold w2_11_op; apply mk_znz2_karatsuba_spec.
exact S10.
assert (S12: znz_spec w2_12_op).
unfold w2_12_op; apply mk_znz2_karatsuba_spec.
exact S11.
assert (S13: znz_spec w2_13_op).
unfold w2_13_op; apply mk_znz2_karatsuba_spec.
exact S12.
assert (S14: znz_spec w2_14_op).
unfold w2_14_op; apply mk_znz2_karatsuba_spec.
exact S13.
intros n; case n; clear n.
exact w2_op_spec.
intros n; case n; clear n.
exact S1.
intros n; case n; clear n.
exact S2.
intros n; case n; clear n.
exact S3.
intros n; case n; clear n.
exact S4.
intros n; case n; clear n.
exact S5.
intros n; case n; clear n.
exact S6.
intros n; case n; clear n.
exact S7.
intros n; case n; clear n.
exact S8.
intros n; case n; clear n.
exact S9.
intros n; case n; clear n.
exact S10.
intros n; case n; clear n.
exact S11.
intros n; case n; clear n.
exact S12.
intros n; case n; clear n.
exact S13.
intros n; case n; clear n.
exact S14.
intro n.
simpl cmk_op.
repeat match goal with |- znz_spec (mk_zn2z_op_karatsuba ?X) =>
  generalize (@mk_znz2_karatsuba_spec _ X); intros tmp;
  apply tmp; clear tmp
end.
apply mk_spec.
exact w2_op_spec.
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
