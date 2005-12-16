Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Subtractions ** *)

Definition w2_pred_c x :=
 match x with
 | OO => C1 II
 | OI => C0 OO
 | IO => C0 OI
 | II => C0 IO
 end.

Definition w2_sub_c x y :=
 match y with
 | OO => C0 x
 | OI => 
    match x with
    | OO => C1 II
    | OI => C0 OO
    | IO => C0 OI
    | II => C0 IO
    end
 | IO => 
    match x with
    | OO => C1 IO
    | OI => C1 II
    | IO => C0 OO
    | II => C0 OI
    end
 | II => 
    match x with
    | OO => C1 OI
    | OI => C1 IO
    | IO => C1 II
    | II => C0 OO
    end
 end.

Definition w2_sub_carry_c x y :=
 match y with
 | OO =>
    match x with
    | OO => C1 II
    | OI => C0 OO
    | IO => C0 OI
    | II => C0 IO
    end
 | OI =>
    match x with
    | OO => C1 IO
    | OI => C1 II
    | IO => C0 OO
    | II => C0 OI
    end
 | IO =>
    match x with
    | OO => C1 OI
    | OI => C1 IO
    | IO => C1 II
    | II => C0 OO
    end
 | II => C1 x
 end.

Definition w2_sub x y :=
 match y with
 | OO => x
 | OI =>
    match x with
    | OO => II
    | OI => OO
    | IO => OI
    | II => IO
    end
 | IO =>
    match x with
    | OO => IO
    | OI => II
    | IO => OO
    | II => OI
    end
 | II =>
    match x with
    | OO => OI
    | OI => IO
    | IO => II
    | II => OO
    end
 end.

