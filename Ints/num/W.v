
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.
Require Import CyclicAxioms DoubleCyclic BigN Cyclic31 Int31.
Require Import ZArith ZCAux.

(* ** Type of words ** *)


(* Make the words *)

Definition mk_word (w: Type) (n:nat): Type.
fix 2.
intros w n; case n; simpl.
exact int31.
intros n1; exact (zn2z (mk_word w n1)).
Defined.

(* Make the op *)

Fixpoint mk_op (w : Type) (op : ZnZ.Ops w) (n : nat) {struct n} :
  ZnZ.Ops (word w n) :=
  match n return (ZnZ.Ops (word w n)) with
  | O => op
  | S n1 => mk_zn2z_ops_karatsuba (mk_op op n1)
  end.

Theorem mk_op_digits: forall w (op: ZnZ.Ops w) n, 
  (Zpos (ZnZ.digits (mk_op op n)) = 2 ^ Z_of_nat n * Zpos (ZnZ.digits op))%Z.
intros w op n; elim n; simpl mk_op; auto; clear n.
intros n Rec; simpl ZnZ.digits.
rewrite Zpos_xO; rewrite Rec.
rewrite Zmult_assoc; apply f_equal2 with (f := Zmult); auto.
rewrite inj_S; unfold Zsucc; rewrite Zplus_comm.
rewrite Zpower_exp; auto with zarith.
Qed.

Theorem digits_pos: forall w (op: ZnZ.Ops w) n,
  (1 < Zpos (ZnZ.digits op) ->  1 < Zpos (ZnZ.digits (mk_op op n)))%Z.
intros w op n H.
rewrite mk_op_digits.
rewrite <- (Zmult_1_r 1).
apply Zle_lt_trans with (2 ^ (Z_of_nat n) * 1)%Z.
apply Zmult_le_compat_r; auto with zarith.
rewrite <- (Zpower_0_r 2).
apply Zpower_le_monotone; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
Qed.

Fixpoint mk_spec (w : Type) (op : ZnZ.Ops w) (op_spec : ZnZ.Specs op) 
    (H: (1 < Zpos (ZnZ.digits op))%Z)  (n : nat)
            {struct n} : ZnZ.Specs (mk_op op n) :=
  match n return (ZnZ.Specs (mk_op op n)) with
  | O => op_spec
  | S n1 =>
      @mk_zn2z_specs_karatsuba (word w n1) (mk_op op n1)
        (* (digits_pos op n1 H) *) (mk_spec op_spec H n1)
  end.

(* ** Operators ** *)
Definition w31_1_ops := mk_zn2z_ops int31_ops.           
Definition w31_2_ops := mk_zn2z_ops w31_1_ops.
Definition w31_3_ops := mk_zn2z_ops w31_2_ops.
Definition w31_4_ops := mk_zn2z_ops_karatsuba w31_3_ops.
Definition w31_5_ops := mk_zn2z_ops_karatsuba w31_4_ops.
Definition w31_6_ops := mk_zn2z_ops_karatsuba w31_5_ops.
Definition w31_7_ops := mk_zn2z_ops_karatsuba w31_6_ops.
Definition w31_8_ops := mk_zn2z_ops_karatsuba w31_7_ops.
Definition w31_9_ops := mk_zn2z_ops_karatsuba w31_8_ops.
Definition w31_10_ops := mk_zn2z_ops_karatsuba w31_9_ops.
Definition w31_11_ops := mk_zn2z_ops_karatsuba w31_10_ops.
Definition w31_12_ops := mk_zn2z_ops_karatsuba w31_11_ops.
Definition w31_13_ops := mk_zn2z_ops_karatsuba w31_12_ops.
Definition w31_14_ops := mk_zn2z_ops_karatsuba w31_13_ops.

Definition cmk_ops (n: nat): ZnZ.Ops (word int31 n).
intros n; case n; clear n.
exact int31_ops.
intros n; case n; clear n.
exact w31_1_ops.
intros n; case n; clear n.
exact w31_2_ops.
intros n; case n; clear n.
exact w31_3_ops.
intros n; case n; clear n.
exact w31_4_ops.
intros n; case n; clear n.
exact w31_5_ops.
intros n; case n; clear n.
exact w31_6_ops.
intros n; case n; clear n.
exact w31_7_ops.
intros n; case n; clear n.
exact w31_8_ops.
intros n; case n; clear n.
exact w31_9_ops.
intros n; case n; clear n.
exact w31_10_ops.
intros n; case n; clear n.
exact w31_11_ops.
intros n; case n; clear n.
exact w31_12_ops.
intros n; case n; clear n.
exact w31_13_ops.
intros n; case n; clear n.
exact w31_14_ops.
intros n.
match goal with |- context[S ?X] =>
 exact (mk_op int31_ops (S X))
end.
Defined.

Definition cmk_spec n: ZnZ.Specs (cmk_ops n).
assert (S1: ZnZ.Specs w31_1_ops).
unfold w31_1_ops; apply mk_zn2z_specs; auto with zarith.
exact int31_specs.
assert (S2: ZnZ.Specs w31_2_ops).
unfold w31_2_ops; apply mk_zn2z_specs; auto with zarith.
assert (S3: ZnZ.Specs w31_3_ops).
unfold w31_3_ops; apply mk_zn2z_specs; auto with zarith.
assert (S4: ZnZ.Specs w31_4_ops).
unfold w31_4_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S5: ZnZ.Specs w31_5_ops).
unfold w31_5_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S6: ZnZ.Specs w31_6_ops).
unfold w31_6_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S7: ZnZ.Specs w31_7_ops).
unfold w31_7_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S8: ZnZ.Specs w31_8_ops).
unfold w31_8_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S9: ZnZ.Specs w31_9_ops).
unfold w31_9_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S10: ZnZ.Specs w31_10_ops).
unfold w31_10_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S11: ZnZ.Specs w31_11_ops).
unfold w31_11_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S12: ZnZ.Specs w31_12_ops).
unfold w31_12_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S13: ZnZ.Specs w31_13_ops).
unfold w31_13_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
assert (S14: ZnZ.Specs w31_14_ops).
unfold w31_14_ops; apply mk_zn2z_specs_karatsuba; auto with zarith.
intros n; case n; clear n.
exact int31_specs.
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
simpl cmk_ops.
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
exact int31_specs.
auto with zarith.
Defined.


Theorem cmk_ops_digits: forall n, 
  (Zpos (ZnZ.digits (cmk_ops n)) = 2 ^ (Z_of_nat n) * 31)%Z.
do 15 (intros n; case n; clear n; [try reflexivity | idtac]).
intros n; unfold cmk_ops; lazy beta.
rewrite mk_op_digits; auto.
Qed.
