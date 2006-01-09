Require Import ZArith.
Open Local Scope Z_scope.
Require Import W8_basic.
Open Local Scope w8_scope.


Require Import ZnZDivn1.
Require Import W8_compare.
Require Import W8_add.
Require Import W8_sub.
Require Export W8_div_aux.
Require Export W8_lift.

(* ** Division of two digits by one ** *)

Definition w8_div21 a1 a2 b :=
 let (q,s) := w8_div_wB a1 b in
 match w8_add_c s a2 with
 | C0 r =>
   match w8_compare r b with
   | Eq => (w8_succ q, OOOOOOOO)
   | Lt => (q, r)
   | Gt => (w8_succ q, w8_sub r b)
   end
 | C1 r =>
   let q := w8_succ q in
   let r' := w8_sub r b in
   match w8_compare r' b with
   | Eq => (w8_succ q, OOOOOOOO)
   | Lt => (q, r')
   | Gt => (w8_succ q, w8_sub r' b)
   end
 end.


(* ** Division of n digits by one ** *)

Definition w8_divn1  :=
 let _gen_divn1 := gen_divn1 8 OOOOOOOO w8_WW w8_head0 w8_add_mul_div w8_div21 in
 fun n x y => _gen_divn1 n 
   (match word_tr_word w8 n in (_ = y) return y with
    | refl_equal => x
    end) y.


(* ** Modulo of n digits by one ** *)

Definition w8_modn1  :=
 let _gen_modn1 := gen_modn1 8 OOOOOOOO  w8_head0 w8_add_mul_div w8_div21 in
 fun n x y => _gen_modn1 n 
   (match word_tr_word w8 n in (_ = y) return y with
    | refl_equal => x
    end) y.

