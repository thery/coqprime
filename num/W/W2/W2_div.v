Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.


Require Import ZnZDivn1.
Require Import W2_compare.
Require Import W2_add.
Require Import W2_sub.
Require Export W2_div_aux.
Require Export W2_lift.

(* ** Division of two digits by one ** *)

Definition w2_div21 a1 a2 b :=
 let (q,s) := w2_div_wB a1 b in
 match w2_add_c s a2 with
 | C0 r =>
   match w2_compare r b with
   | Eq => (w2_succ q, OO)
   | Lt => (q, r)
   | Gt => (w2_succ q, w2_sub r b)
   end
 | C1 r =>
   let q := w2_succ q in
   let r' := w2_sub r b in
   match w2_compare r' b with
   | Eq => (w2_succ q, OO)
   | Lt => (q, r')
   | Gt => (w2_succ q, w2_sub r' b)
   end
 end.


(* ** Division of n digits by one ** *)

Definition w2_divn1  :=
 let _gen_divn1 := gen_divn1 2 OO w2_WW w2_head0 w2_add_mul_div w2_div21 in
 fun n x y => _gen_divn1 n 
   (match word_tr_word w2 n in (_ = y) return y with
    | refl_equal => x
    end) y.


(* ** Modulo of n digits by one ** *)

Definition w2_modn1  :=
 let _gen_modn1 := gen_modn1 2 OO  w2_head0 w2_add_mul_div w2_div21 in
 fun n x y => _gen_modn1 n 
   (match word_tr_word w2 n in (_ = y) return y with
    | refl_equal => x
    end) y.

