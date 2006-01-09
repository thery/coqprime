Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Division ** *)

Definition w2_div x y :=
 match y with
 | OO => (OO, OO)
 | OI => 
    match x with
    | OO => (OO, OO)
    | OI => (OI, OO)
    | IO => (IO, OO)
    | II => (II, OO)
    end
 | IO => 
    match x with
    | OO => (OO, OO)
    | OI => (OO, OI)
    | IO => (OI, OO)
    | II => (OI, OI)
    end
 | II => 
    match x with
    | OO => (OO, OO)
    | OI => (OO, OI)
    | IO => (OO, IO)
    | II => (OI, OO)
    end
 end.

Definition w2_div_wB x y :=
 match y with
 | OO => (OO, OO)
 | OI => (OO, OO)
 | IO =>
    match x with
    | OO => (OO, OO)
    | OI => (IO, OO)
    | IO => (OO, OO)
    | II => (OO, OO)
   end
 | II =>
    match x with
    | OO => (OO, OO)
    | OI => (OI, OI)
    | IO => (IO, IO)
    | II => (OO, OO)
   end
 end.

Definition w2_mod x y :=
 match y with
 | OO => OO
 | OI => 
    match x with
    | OO => OO
    | OI => OO
    | IO => OO
    | II => OO
    end
 | IO => 
    match x with
    | OO => OO
    | OI => OI
    | IO => OO
    | II => OI
    end
 | II => 
    match x with
    | OO => OO
    | OI => OI
    | IO => IO
    | II => OO
    end
 end.

Definition w2_gcd x y :=
 match x with
 | OO => 
 match y with
    | OO => OO
    | OI => OI
    | IO => IO
    | II => II
   end
 | OI => 
 match y with
    | OO => OI
    | OI => OI
    | IO => OI
    | II => OI
   end
 | IO => 
 match y with
    | OO => IO
    | OI => OI
    | IO => IO
    | II => OI
   end
 | II => 
 match y with
    | OO => II
    | OI => OI
    | IO => OI
    | II => II
   end
 end.

