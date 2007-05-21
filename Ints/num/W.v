
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import Basic_type.
Require Import ZnZ.
Require Import Zn2Z.
Require Import BigN.
Require Import ZArith.

(* ** Type of words ** *)


(* Make the words *)

Definition mk_word (w: Set) (n:nat): Set.
fix 2.
intros w n; case n; simpl.
exact int31.
intros n1; exact (zn2z (mk_word w n1)).
Defined.

(* Make the op *)

Fixpoint mk_op (w : Set) (op : znz_op w) (n : nat) {struct n} :
  znz_op (word w n) :=
  match n return (znz_op (word w n)) with
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

Theorem digits_pos: forall w (op: znz_op w) n,
  (1 < Zpos (znz_digits op) ->  1 < Zpos (znz_digits (mk_op op n)))%Z.
intros w op n H.
rewrite mk_op_digits.
rewrite <- (Zmult_1_r 1).
apply Zle_lt_trans with (2 ^ (Z_of_nat n) * 1)%Z.
apply Zmult_le_compat_r; auto with zarith.
rewrite <- (ZAux.Zpower_exp_0 2).
apply ZAux.Zpower_le_monotone; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
Qed.

Fixpoint mk_spec (w : Set) (op : znz_op w) (op_spec : znz_spec op) 
    (H: (1 < Zpos (znz_digits op))%Z)  (n : nat)
            {struct n} : znz_spec (mk_op op n) :=
  match n return (znz_spec (mk_op op n)) with
  | O => op_spec
  | S n1 =>
      @mk_znz2_karatsuba_spec (word w n1) (mk_op op n1)
        (digits_pos op n1 H) (mk_spec op_spec H n1)
  end.

(* ** Operators ** *)
Definition w31_1_op := mk_zn2z_op int31_op.           
Definition w31_2_op := mk_zn2z_op w31_1_op.
Definition w31_3_op := mk_zn2z_op w31_2_op.
Definition w31_4_op := mk_zn2z_op_karatsuba w31_3_op.
Definition w31_5_op := mk_zn2z_op_karatsuba w31_4_op.
Definition w31_6_op := mk_zn2z_op_karatsuba w31_5_op.
Definition w31_7_op := mk_zn2z_op_karatsuba w31_6_op.
Definition w31_8_op := mk_zn2z_op_karatsuba w31_7_op.
Definition w31_9_op := mk_zn2z_op_karatsuba w31_8_op.
Definition w31_10_op := mk_zn2z_op_karatsuba w31_9_op.
Definition w31_11_op := mk_zn2z_op_karatsuba w31_10_op.
Definition w31_12_op := mk_zn2z_op_karatsuba w31_11_op.
Definition w31_13_op := mk_zn2z_op_karatsuba w31_12_op.
Definition w31_14_op := mk_zn2z_op_karatsuba w31_13_op.

Definition cmk_op (n: nat): znz_op (word int31 n).
intros n; case n; clear n.
exact int31_op.
intros n; case n; clear n.
exact w31_1_op.
intros n; case n; clear n.
exact w31_2_op.
intros n; case n; clear n.
exact w31_3_op.
intros n; case n; clear n.
exact w31_4_op.
intros n; case n; clear n.
exact w31_5_op.
intros n; case n; clear n.
exact w31_6_op.
intros n; case n; clear n.
exact w31_7_op.
intros n; case n; clear n.
exact w31_8_op.
intros n; case n; clear n.
exact w31_9_op.
intros n; case n; clear n.
exact w31_10_op.
intros n; case n; clear n.
exact w31_11_op.
intros n; case n; clear n.
exact w31_12_op.
intros n; case n; clear n.
exact w31_13_op.
intros n; case n; clear n.
exact w31_14_op.
intros n.
match goal with |- context[S ?X] =>
 exact (mk_op int31_op (S X))
end.
Defined.

Definition cmk_spec n: znz_spec (cmk_op n).
assert (S1: znz_spec w31_1_op).
unfold w31_1_op; apply mk_znz2_spec; auto with zarith.
exact int31_spec.
assert (S2: znz_spec w31_2_op).
unfold w31_2_op; apply mk_znz2_spec; auto with zarith.
assert (S3: znz_spec w31_3_op).
unfold w31_3_op; apply mk_znz2_spec; auto with zarith.
assert (S4: znz_spec w31_4_op).
unfold w31_4_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S5: znz_spec w31_5_op).
unfold w31_5_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S6: znz_spec w31_6_op).
unfold w31_6_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S7: znz_spec w31_7_op).
unfold w31_7_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S8: znz_spec w31_8_op).
unfold w31_8_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S9: znz_spec w31_9_op).
unfold w31_9_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S10: znz_spec w31_10_op).
unfold w31_10_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S11: znz_spec w31_11_op).
unfold w31_11_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S12: znz_spec w31_12_op).
unfold w31_12_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S13: znz_spec w31_13_op).
unfold w31_13_op; apply mk_znz2_karatsuba_spec; auto with zarith.
assert (S14: znz_spec w31_14_op).
unfold w31_14_op; apply mk_znz2_karatsuba_spec; auto with zarith.
intros n; case n; clear n.
exact int31_spec.
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
  apply tmp; clear tmp; auto with zarith
end.
apply digits_pos.
auto with zarith.
apply mk_spec.
exact int31_spec.
auto with zarith.
Defined.


Theorem cmk_op_digits: forall n, 
  (Zpos (znz_digits (cmk_op n)) = 2 ^ (Z_of_nat n) * 31)%Z.
do 15 (intros n; case n; clear n; [try reflexivity | idtac]).
intros n; unfold cmk_op; lazy beta.
rewrite mk_op_digits; auto.
Qed.
