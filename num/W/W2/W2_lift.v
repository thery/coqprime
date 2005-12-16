Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Lift operations ** *)

Definition w2_head0 x :=
 match x with
 | OO => Npos (xO xH)
 | OI => Npos xH
 | IO => N0
 | II => N0
 end.

Definition w2_add_mul_div1 x y :=
 match x with
 | OO =>
    match y with
    | OO => OO
    | OI => OO
    | IO => OI
    | II => OI
    end
 | OI =>
    match y with
    | OO => IO
    | OI => IO
    | IO => II
    | II => II
    end
 | IO =>
    match y with
    | OO => OO
    | OI => OO
    | IO => OI
    | II => OI
    end
 | II =>
    match y with
    | OO => IO
    | OI => IO
    | IO => II
    | II => II
    end
 end.

Definition w2_add_mul_div x y p :=
 match p with
 | xH => w2_add_mul_div1 x y
 | _ => OO
 end.
