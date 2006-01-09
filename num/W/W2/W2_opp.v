Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Opposites ** *)

Definition w2_opp_c x :=
 match x with
 | OO => C0 OO
 | OI => C1 II
 | IO => C1 IO
 | II => C1 OI
 end.

Definition w2_opp x :=
 match x with
 | OO => OO
 | OI => II
 | IO => IO
 | II => OI
 end.

Definition w2_opp_carry x :=
 match x with
 | OO => II
 | OI => IO
 | IO => OI
 | II => OO
 end.

