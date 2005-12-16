Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Multiplcations ** *)

Definition w2_mul_c x y :=
 match x with
 | OO => W0
 | OI => WW OO y
 | IO =>
    match y with
    | OO => W0
    | OI => WW OO IO
    | IO => WW OI OO
    | II => WW OI IO
    end
 | II =>
    match y with
    | OO => W0
    | OI => WW OO II
    | IO => WW OI IO
    | II => WW IO OI
    end
 end.

Definition w2_mul x y :=
 match w2_mul_c x y with
 | W0 => OO
 | WW _ l => l
 end.

Definition w2_square_c x :=
 match x with
 | OO => W0
 | OI => WW OO OI
 | IO => WW OI OO
 | II => WW IO OI
 end.

