Require Export W8_basic.
Require Export W8_compare.
Require Export W8_opp.
Require Export W8_add.
Require Export W8_sub.
Require Export W8_mul.
Require Export W8_div.
Require Export W8_lift.
Require Import ZnZ.



(* ** Record of basic operators for base 256 ** *)

Definition w8_op  :=
 mk_znz_op 8
       w8_to_Z w8_of_pos w8_head0
       OOOOOOOO OOOOOOOI IIIIIIII
       w8_WW w8_CW
       w8_compare
       w8_opp_c w8_opp_carry
       w8_succ_c
       w8_add_c w8_add_carry_c w8_add
       w8_pred_c
       w8_sub_c w8_sub_carry_c w8_sub
       w8_mul_c w8_mul w8_square_c
       w8_div21 w8_add_mul_div.

