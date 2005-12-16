Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Comparison ** *)

Definition w2_compare x y :=
 match x with
 | OO => 
    match y with
    | OO => Eq
    | _ => Lt end
 | OI => 
    match y with
    | OO => Gt
    | OI => Eq
    | _ => Lt end
 | IO => 
    match y with
    | OO => Gt
    | OI => Gt
    | IO => Eq
    | _ => Lt end
 | II => 
    match y with
    | OO => Gt
    | OI => Gt
    | IO => Gt
    | II => Eq
    end
 end.

