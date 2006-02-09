Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Require Import W2_basic_spec.
Open Local Scope w2_scope.
Require Import W2_op.


Require Import W2_opp_spec.
Require Import W2_compare_spec.
Require Import W2_succ_c_spec.
Require Import W2_add_c_spec.
Require Import W2_add_carry_c_spec.
Require Import W2_add_spec.
Require Import W2_add_carry_spec.
Require Import W2_pred_c_spec.
Require Import W2_sub_c_spec.
Require Import W2_sub_carry_c_spec.
Require Import W2_sub_spec.
Require Import W2_sub_carry_spec.
Require Import W2_mul_c_spec.
Require Import W2_mul_spec.
Require Import W2_square_c_spec.
Require Import W2_div_wB_spec.
Require Import W2_div_spec.
Require Import W2_head0_spec.
Require Import W2_add_mul_div_spec.
Require Import W2_pos_mod_spec.
Require Import ZnZ.
Lemma w2_op_spec : znz_spec w2_op.
Admitted.

