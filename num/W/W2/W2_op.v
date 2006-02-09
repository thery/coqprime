Require Export W2_basic.
Require Export W2_compare.
Require Export W2_opp.
Require Export W2_add.
Require Export W2_sub.
Require Export W2_mul.
Require Export W2_div.
Require Export W2_lift.
Require Export W2_pos_mod.
Require Import ZnZ.



(* ** Record of basic operators for base 4 ** *)

Definition w2_op  :=
 mk_znz_op 2
       w2_to_Z w2_of_pos w2_head0
       OO OI II
       w2_WW w2_CW
       w2_compare
       w2_opp_c w2_opp w2_opp_carry
       w2_succ_c w2_add_c w2_add_carry_c
       w2_succ w2_add w2_add_carry
       w2_pred_c w2_sub_c w2_sub_carry_c
       w2_pred w2_sub w2_sub_carry
       w2_mul_c w2_mul w2_square_c
       w2_div21 w2_divn1 w2_div w2_div
       w2_modn1 w2_mod w2_mod
       w2_gcd w2_gcd w2_add_mul_div w2_pos_mod.

