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
Proof.
 apply mk_znz_spec.
 exact w2_to_Z_spec.
 exact w2_of_pos_spec.
 exact w2_0_spec.
 exact w2_1_spec.
 exact w2_Bm1_spec.
 exact w2_WW_spec.
 exact w2_CW_spec.
 exact w2_compare_spec.
 exact w2_opp_c_spec.
 exact w2_opp_spec.
 exact w2_opp_carry_spec.
 exact w2_succ_c_spec.
 exact w2_add_c_spec.
 exact w2_add_carry_c_spec.
 exact w2_succ_spec.
 exact w2_add_spec.
 exact w2_add_carry_spec.
 exact w2_pred_c_spec.
 exact w2_sub_c_spec.
 exact w2_sub_carry_c_spec.
 exact w2_pred_spec.
 exact w2_sub_spec.
 exact w2_sub_carry_spec.
 exact w2_mul_c_spec.
 exact w2_mul_spec.
 exact w2_square_c_spec.
 exact w2_div21_spec.
 exact w2_divn1_spec.
 exact w2_div_gt_spec.
 exact w2_div_spec.
 exact w2_modn1_spec.
 exact w2_mod_gt_spec.
 exact w2_mod_spec.
 exact w2_gcd_gt_spec.
 exact w2_gcd_spec.
 exact w2_head0_spec.
 exact w2_add_mul_div_spec.
 exact w2_pos_mod_spec.
Qed.

