Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.


Require Import W2_compare.
Require Import W2_add.
Require Import W2_sub.

(* ** Division ** *)

Definition w2_div_wB x y :=
 match y with
 | OO => (C0 OO, OO)
 | OI => (C0 OO, OO)
 | IO =>
    match x with
    | OO => (C0 OO, OO)
    | OI => (C0 IO, OO)
    | IO => (C1 OO, OO)
    | II => (C1 IO, OO)
   end
 | II =>
    match x with
    | OO => (C0 OO, OO)
    | OI => (C0 OI, OI)
    | IO => (C0 IO, IO)
    | II => (C1 OO, OO)
   end
 end.

Definition w2_div21 a1 a2 b :=
 let (q,s) := w2_div_wB a1 b in
 match w2_add_c s a2 with
 | C0 r =>
   match w2_compare r b with
   | Eq => (w2_carry_succ_c q, OO)
   | Lt => (q, r)
   | Gt => (w2_carry_succ_c q, w2_sub r b)
   end
 | C1 r =>
   let q := w2_carry_succ_c q in
   let r' := w2_sub r b in
   match w2_compare r' b with
   | Eq => (w2_carry_succ_c q, OO)
   | Lt => (q, r')
   | Gt => (w2_carry_succ_c q, w2_sub r' b)
   end
 end.

