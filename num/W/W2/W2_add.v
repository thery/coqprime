Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Additions ** *)

Definition w2_succ_c x :=
 match x with
 | OO => C0 OI
 | OI => C0 IO
 | IO => C0 II
 | II => C1 OO
 end.

Definition w2_carry_succ_c cx :=
 Eval compute in
 match cx with
 | C0 x => w2_succ_c x
 | C1 x => 
    match x with
    | OO => C1 OI
    | OI => C1 IO
    | IO => C1 II
    | II => C1 OO
    end
 end.

Definition w2_add_c x y :=
 match x with
 | OO => C0 y
 | OI => 
    match y with
    | OO => C0 OI
    | OI => C0 IO
    | IO => C0 II
    | II => C1 OO
    end
 | IO => 
    match y with
    | OO => C0 IO
    | OI => C0 II
    | IO => C1 OO
    | II => C1 OI
    end
 | II => 
    match y with
    | OO => C0 II
    | OI => C1 OO
    | IO => C1 OI
    | II => C1 IO
    end
 end.

Definition w2_add_carry_c x y :=
 match x with
 | OO => 
    match y with
    | OO => C0 OI
    | OI => C0 IO
    | IO => C0 II
    | II => C1 OO
    end
 | OI => 
    match y with
    | OO => C0 IO
    | OI => C0 II
    | IO => C1 OO
    | II => C1 OI
    end
 | IO => 
    match y with
    | OO => C0 II
    | OI => C1 OO
    | IO => C1 OI
    | II => C1 IO
    end
 | II => C1 y
 end.

Definition w2_add x y :=
 match x with
 | OO => y
 | OI => 
    match y with
    | OO => OI
    | OI => IO
    | IO => II
    | II => OO
    end
 | IO => 
    match y with
    | OO => IO
    | OI => II
    | IO => OO
    | II => OI
    end
 | II => 
    match y with
    | OO => II
    | OI => OO
    | IO => OI
    | II => IO
    end
 end.

