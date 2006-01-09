Require Import ZArith.
Open Local Scope Z_scope.
Require Import W8_basic.
Require Import W8_basic_spec.
Open Local Scope w8_scope.
Require Import W8_op.


Require Import W8_opp_spec.
Require Import W8_compare_spec.
Require Import W8_succ_c_spec.
Require Import W8_add_c_spec.
Require Import W8_add_carry_c_spec.
Require Import W8_add_spec.
Require Import W8_add_carry_spec.
Require Import W8_pred_c_spec.
Require Import W8_sub_c_spec.
Require Import W8_sub_carry_c_spec.
Require Import W8_sub_spec.
Require Import W8_sub_carry_spec.
Require Import W8_mul_c_spec.
Require Import W8_mul_spec.
Require Import W8_square_c_spec.
Require Import W8_div_wB_spec.
Require Import W8_div_spec.
Require Import W8_head0_spec.
Require Import W8_add_mul_div_spec.
Require Import ZnZ.
Lemma w8_op_spec : znz_spec w8_op.
Proof.
 apply mk_znz_spec.
 exact w8_to_Z_spec.
 exact w8_of_pos_spec.
 exact w8_0_spec.
 exact w8_1_spec.
 exact w8_Bm1_spec.
 exact w8_WW_spec.
 exact w8_CW_spec.
 exact w8_compare_spec.
 exact w8_opp_c_spec.
 exact w8_opp_spec.
 exact w8_opp_carry_spec.
 exact w8_succ_c_spec.
 exact w8_add_c_spec.
 exact w8_add_carry_c_spec.
 exact w8_succ_spec.
 exact w8_add_spec.
 exact w8_add_carry_spec.
 exact w8_pred_c_spec.
 exact w8_sub_c_spec.
 exact w8_sub_carry_c_spec.
 exact w8_pred_spec.
 exact w8_sub_spec.
 exact w8_sub_carry_spec.
 exact w8_mul_c_spec.
 exact w8_mul_spec.
 exact w8_square_c_spec.
 exact w8_div21_spec.
 exact w8_divn1_spec.
 exact w8_div_gt_spec.
 exact w8_div_spec.
 exact w8_modn1_spec.
 exact w8_mod_gt_spec.
 exact w8_mod_spec.
 exact w8_gcd_gt_spec.
 exact w8_gcd_spec.
 exact w8_head0_spec.
 exact w8_add_mul_div_spec.
Qed.

