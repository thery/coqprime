Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Mod ** *)

Definition w2_pos_mod (p: positive) (x: w2) := 
  match p with 
    xH => match x with OO => OO | OI => OI | IO => OO | II => OI end
  |  _  => x
  end.