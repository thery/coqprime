
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.
Require Import CyclicAxioms Cyclic63 Int63Compat.
From Bignums Require Import DoubleCyclic BigN.
Require Import ZArith ZCAux Mod_op.

(* ** Type of words ** *)


(* Make the words *)

Definition mk_word: forall (w: Type) (n:nat), Type.
fix mk_word 2.
intros w n; case n; simpl.
exact int.
intros n1; exact (zn2z (mk_word w n1)).
Defined.

(* Make the op *)
Fixpoint mk_op (w : univ_of_cycles) (op : ZnZ.Ops w) (n : nat) {struct n} :
  ZnZ.Ops (word w n) :=
  match n return (ZnZ.Ops (word w n)) with
  | O => op
  | S n1 => mk_zn2z_ops_karatsuba (mk_op op n1)
  end.

Theorem mk_op_digits: forall (w:univ_of_cycles) (op: ZnZ.Ops w) n,
  (Zpos (ZnZ.digits (mk_op op n)) = 2 ^ Z_of_nat n * Zpos (ZnZ.digits op))%Z.
intros w op n; elim n; simpl mk_op; auto; clear n.
intros n Rec; simpl ZnZ.digits.
rewrite Zpos_xO; rewrite Rec.
rewrite Zmult_assoc; apply f_equal2 with (f := Zmult); auto.
rewrite inj_S; unfold Z.succ; rewrite Zplus_comm.
rewrite Zpower_exp; auto with zarith.
Qed.

Theorem digits_pos: forall (w:univ_of_cycles) (op: ZnZ.Ops w) n,
  (1 < Zpos (ZnZ.digits op) ->  1 < Zpos (ZnZ.digits (mk_op op n)))%Z.
intros w op n H.
rewrite mk_op_digits.
rewrite <- (Zmult_1_r 1).
apply Z.le_lt_trans with (2 ^ (Z_of_nat n) * 1)%Z.
apply Zmult_le_compat_r;[ | auto with zarith].
rewrite <- (Zpower_0_r 2).
apply Zpower_le_monotone; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
Qed.

Fixpoint mk_spec (w : univ_of_cycles) (op : ZnZ.Ops w) (op_spec : ZnZ.Specs op)
    (H: (1 < Zpos (ZnZ.digits op))%Z)  (n : nat)
            {struct n} : ZnZ.Specs (mk_op op n) :=
  match n return (ZnZ.Specs (mk_op op n)) with
  | O => op_spec
  | S n1 =>
      @mk_zn2z_specs_karatsuba (word w n1) (mk_op op n1)
        (* (digits_pos op n1 H) *) (mk_spec op_spec H n1)
  end.

(* ** Operators ** *)
Definition w63_1_op := mk_zn2z_ops int_ops.
Definition w63_2_op := mk_zn2z_ops w63_1_op.
Definition w63_3_op := mk_zn2z_ops w63_2_op.
Definition w63_4_op := mk_zn2z_ops_karatsuba w63_3_op.
Definition w63_5_op := mk_zn2z_ops_karatsuba w63_4_op.
Definition w63_6_op := mk_zn2z_ops_karatsuba w63_5_op.
Definition w63_7_op := mk_zn2z_ops_karatsuba w63_6_op.
Definition w63_8_op := mk_zn2z_ops_karatsuba w63_7_op.
Definition w63_9_op := mk_zn2z_ops_karatsuba w63_8_op.
Definition w63_10_op := mk_zn2z_ops_karatsuba w63_9_op.
Definition w63_11_op := mk_zn2z_ops_karatsuba w63_10_op.
Definition w63_12_op := mk_zn2z_ops_karatsuba w63_11_op.
Definition w63_13_op := mk_zn2z_ops_karatsuba w63_12_op.
Definition w63_14_op := mk_zn2z_ops_karatsuba w63_13_op.

Definition cmk_op: forall (n: nat), ZnZ.Ops (word int n).
intros n; case n; clear n.
exact int_ops.
intros n; case n; clear n.
exact w63_1_op.
intros n; case n; clear n.
exact w63_2_op.
intros n; case n; clear n.
exact w63_3_op.
intros n; case n; clear n.
exact w63_4_op.
intros n; case n; clear n.
exact w63_5_op.
intros n; case n; clear n.
exact w63_6_op.
intros n; case n; clear n.
exact w63_7_op.
intros n; case n; clear n.
exact w63_8_op.
intros n; case n; clear n.
exact w63_9_op.
intros n; case n; clear n.
exact w63_10_op.
intros n; case n; clear n.
exact w63_11_op.
intros n; case n; clear n.
exact w63_12_op.
intros n; case n; clear n.
exact w63_13_op.
intros n; case n; clear n.
exact w63_14_op.
intros n.
match goal with |- context[S ?X] =>
 exact (mk_op int_ops (S X))
end.
Defined.

Definition cmk_spec: forall n, ZnZ.Specs (cmk_op n).
assert (S1: ZnZ.Specs w63_1_op).
unfold w63_1_op; apply mk_zn2z_specs; auto with zarith.
exact int_specs.
assert (S2: ZnZ.Specs w63_2_op).
unfold w63_2_op; apply mk_zn2z_specs; auto with zarith.
assert (S3: ZnZ.Specs w63_3_op).
unfold w63_3_op; apply mk_zn2z_specs; auto with zarith.
assert (S4: ZnZ.Specs w63_4_op).
unfold w63_4_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S5: ZnZ.Specs w63_5_op).
unfold w63_5_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S6: ZnZ.Specs w63_6_op).
unfold w63_6_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S7: ZnZ.Specs w63_7_op).
unfold w63_7_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S8: ZnZ.Specs w63_8_op).
unfold w63_8_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S9: ZnZ.Specs w63_9_op).
unfold w63_9_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S10: ZnZ.Specs w63_10_op).
unfold w63_10_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S11: ZnZ.Specs w63_11_op).
unfold w63_11_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S12: ZnZ.Specs w63_12_op).
unfold w63_12_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S13: ZnZ.Specs w63_13_op).
unfold w63_13_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S14: ZnZ.Specs w63_14_op).
unfold w63_14_op; apply mk_zn2z_specs_karatsuba; auto with zarith.
intros n; case n; clear n.
exact int_specs.
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
repeat match goal with |- ZnZ.Specs
 (mk_zn2z_ops_karatsuba ?X) =>
  generalize (@mk_zn2z_specs_karatsuba _ X); intros tmp;
  apply tmp; clear tmp; auto with zarith
end.
(*
apply digits_pos.
*)
auto with zarith.
apply mk_spec.
exact int_specs.
auto with zarith.
Defined.


Theorem cmk_op_digits: forall n,
  (Zpos (ZnZ.digits (cmk_op n)) = 2 ^ (Z_of_nat n) * 63)%Z.
do 15 (intros n; case n; clear n; [try reflexivity | idtac]).
intros n; unfold cmk_op; lazy beta.
rewrite mk_op_digits; auto.
Qed.
