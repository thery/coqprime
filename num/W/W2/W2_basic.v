Require Import ZArith.
Require Export Basic_type.


Open Local Scope Z_scope.

Inductive w2 : Set :=
 | OO : w2
 | OI : w2
 | IO : w2
 | II : w2.


(* ** Conversion functions with Z, N and positive ** *)

Definition w2_B := 4.
Definition w2_to_Z x :=
 match x with
 | OO => 0
 | OI => 1
 | IO => 2
 | II => 3
 end.

Definition w2_of_pos p :=
 match p with
 | xH => (N0, OI)
 | (xO xH) => (N0, IO)
 | (xI xH) => (N0, II)
 | (xO (xO p)) => (Npos p, OO)
 | (xI (xO p)) => (Npos p, OI)
 | (xO (xI p)) => (Npos p, IO)
 | (xI (xI p)) => (Npos p, II)
 end.

Definition w2_of_N n :=
 match n with
 | N0 => (N0, OO)
 | Npos p => w2_of_pos p
 end.


(* ** Constructors for the next level ** *)

Definition w2_WW xh xl :=
 match xh, xl with
 | OO, OO => W0
 | _, _ => WW xh xl
end.

Definition w2_W0 h :=
 match h with
 | OO => W0
 | _ => WW h OO
end.

Definition w2_0W l :=
 match l with
 | OO => W0
 | _ => WW OO l
end.

Notation "[| x |]" := (w2_to_Z x)  (at level 0, x at level 99) : w2_scope.
Notation "[+| x |]" := (interp_carry 1 w2_B w2_to_Z x)  (at level 0, x at level 99) : w2_scope.
Notation "[-| x |]" := (interp_carry (-1) w2_B w2_to_Z x)  (at level 0, x at level 99) : w2_scope.
Notation "[|| x ||]" := (zn2z_to_Z w2_B w2_to_Z x)  (at level 0, x at level 99) : w2_scope.
