Require Import ZArith.
Require Import ZnZ.

(*
Unset Boxed Definitions.
*)

Open Local Scope Z_scope.

Inductive w4 : Set :=
 | OOOO : w4
 | OOOI : w4
 | OOIO : w4
 | OOII : w4
 | OIOO : w4
 | OIOI : w4
 | OIIO : w4
 | OIII : w4
 | IOOO : w4
 | IOOI : w4
 | IOIO : w4
 | IOII : w4
 | IIOO : w4
 | IIOI : w4
 | IIIO : w4
 | IIII : w4.


(* ** Conversion functions with Z, N and positive ** *)

Definition w4_to_Z x :=
 match x with
 | OOOO => 0
 | OOOI => 1
 | OOIO => 2
 | OOII => 3
 | OIOO => 4
 | OIOI => 5
 | OIIO => 6
 | OIII => 7
 | IOOO => 8
 | IOOI => 9
 | IOIO => 10
 | IOII => 11
 | IIOO => 12
 | IIOI => 13
 | IIIO => 14
 | IIII => 15
 end.

Definition w4_of_pos p :=
 match p with
 | xH => (N0, OOOI)
 | (xO xH) => (N0, OOIO)
 | (xI xH) => (N0, OOII)
 | (xO (xO xH)) => (N0, OIOO)
 | (xI (xO xH)) => (N0, OIOI)
 | (xO (xI xH)) => (N0, OIIO)
 | (xI (xI xH)) => (N0, OIII)
 | (xO (xO (xO xH))) => (N0, IOOO)
 | (xI (xO (xO xH))) => (N0, IOOI)
 | (xO (xI (xO xH))) => (N0, IOIO)
 | (xI (xI (xO xH))) => (N0, IOII)
 | (xO (xO (xI xH))) => (N0, IIOO)
 | (xI (xO (xI xH))) => (N0, IIOI)
 | (xO (xI (xI xH))) => (N0, IIIO)
 | (xI (xI (xI xH))) => (N0, IIII)
 | (xO (xO (xO (xO p)))) => (Npos p, OOOO)
 | (xI (xO (xO (xO p)))) => (Npos p, OOOI)
 | (xO (xI (xO (xO p)))) => (Npos p, OOIO)
 | (xI (xI (xO (xO p)))) => (Npos p, OOII)
 | (xO (xO (xI (xO p)))) => (Npos p, OIOO)
 | (xI (xO (xI (xO p)))) => (Npos p, OIOI)
 | (xO (xI (xI (xO p)))) => (Npos p, OIIO)
 | (xI (xI (xI (xO p)))) => (Npos p, OIII)
 | (xO (xO (xO (xI p)))) => (Npos p, IOOO)
 | (xI (xO (xO (xI p)))) => (Npos p, IOOI)
 | (xO (xI (xO (xI p)))) => (Npos p, IOIO)
 | (xI (xI (xO (xI p)))) => (Npos p, IOII)
 | (xO (xO (xI (xI p)))) => (Npos p, IIOO)
 | (xI (xO (xI (xI p)))) => (Npos p, IIOI)
 | (xO (xI (xI (xI p)))) => (Npos p, IIIO)
 | (xI (xI (xI (xI p)))) => (Npos p, IIII)
 end.

Definition w4_head0 x :=
 match x with
 | OOOO => Npos (xO (xO xH))
 | OOOI => Npos (xI xH)
 | OOIO => Npos (xO xH)
 | OOII => Npos (xO xH)
 | OIOO => Npos xH
 | OIOI => Npos xH
 | OIIO => Npos xH
 | OIII => Npos xH
 | IOOO => N0
 | IOOI => N0
 | IOIO => N0
 | IOII => N0
 | IIOO => N0
 | IIOI => N0
 | IIIO => N0
 | IIII => N0
 end.

Definition w4_of_N n :=
 match n with
 | N0 => (N0, OOOO)
 | Npos p => w4_of_pos p
 end.


(* ** Constructors for the next level ** *)

Definition w4_WW xh xl :=
 match xh, xl with
 | OOOO, OOOO => W0
 | _, _ => WW xh xl
end.

Definition w4_CW ch xl :=
 match ch with
 | C0 xh => C0 (w4_WW xh xl)
 | C1 xh => C1 (w4_WW xh xl)
 end.


(* ** Comparison ** *)

Definition w4_compare x y :=
 match x with
 | OOOO => match y with  | OOOO => Eq | _ => Lt end
 | OOOI => match y with  | OOOO => Gt | OOOI => Eq | _ => Lt end
 | OOIO => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Eq | _ => Lt end
 | OOII => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Eq | _ => Lt end
 | OIOO => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Eq | _ => Lt end
 | OIOI => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Eq | _ => Lt end
 | OIIO => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Eq | _ => Lt end
 | OIII => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Eq | _ => Lt end
 | IOOO => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Gt | IOOO => Eq | _ => Lt end
 | IOOI => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Gt | IOOO => Gt | IOOI => Eq | _ => Lt end
 | IOIO => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Gt | IOOO => Gt | IOOI => Gt | IOIO => Eq | _ => Lt end
 | IOII => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Gt | IOOO => Gt | IOOI => Gt | IOIO => Gt | IOII => Eq | _ => Lt end
 | IIOO => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Gt | IOOO => Gt | IOOI => Gt | IOIO => Gt | IOII => Gt | IIOO => Eq | _ => Lt end
 | IIOI => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Gt | IOOO => Gt | IOOI => Gt | IOIO => Gt | IOII => Gt | IIOO => Gt | IIOI => Eq | _ => Lt end
 | IIIO => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Gt | IOOO => Gt | IOOI => Gt | IOIO => Gt | IOII => Gt | IIOO => Gt | IIOI => Gt | IIIO => Eq | _ => Lt end
 | IIII => match y with  | OOOO => Gt | OOOI => Gt | OOIO => Gt | OOII => Gt | OIOO => Gt | OIOI => Gt | OIIO => Gt | OIII => Gt | IOOO => Gt | IOOI => Gt | IOIO => Gt | IOII => Gt | IIOO => Gt | IIOI => Gt | IIIO => Gt | IIII => Eq end
 end.


(* ** Opposites ** *)

Definition w4_opp_c x :=
 match x with
 | OOOO => C0 OOOO
 | OOOI => C1 IIII
 | OOIO => C1 IIIO
 | OOII => C1 IIOI
 | OIOO => C1 IIOO
 | OIOI => C1 IOII
 | OIIO => C1 IOIO
 | OIII => C1 IOOI
 | IOOO => C1 IOOO
 | IOOI => C1 OIII
 | IOIO => C1 OIIO
 | IOII => C1 OIOI
 | IIOO => C1 OIOO
 | IIOI => C1 OOII
 | IIIO => C1 OOIO
 | IIII => C1 OOOI
 end.

Definition w4_opp_carry x :=
 match x with
 | OOOO => IIII
 | OOOI => IIIO
 | OOIO => IIOI
 | OOII => IIOO
 | OIOO => IOII
 | OIOI => IOIO
 | OIIO => IOOI
 | OIII => IOOO
 | IOOO => OIII
 | IOOI => OIIO
 | IOIO => OIOI
 | IOII => OIOO
 | IIOO => OOII
 | IIOI => OOIO
 | IIIO => OOOI
 | IIII => OOOO
 end.


(* ** Additions ** *)

Definition w4_succ_c x :=
 match x with
 | OOOO => C0 OOOI
 | OOOI => C0 OOIO
 | OOIO => C0 OOII
 | OOII => C0 OIOO
 | OIOO => C0 OIOI
 | OIOI => C0 OIIO
 | OIIO => C0 OIII
 | OIII => C0 IOOO
 | IOOO => C0 IOOI
 | IOOI => C0 IOIO
 | IOIO => C0 IOII
 | IOII => C0 IIOO
 | IIOO => C0 IIOI
 | IIOI => C0 IIIO
 | IIIO => C0 IIII
 | IIII => C1 OOOO
 end.

Definition w4_carry_succ_c cx :=
 match cx with
 | C0 x => w4_succ_c x
 | C1 x => C1 (without_c (w4_succ_c x))
 end.

Definition w4_add_c x y :=
 match x with
 | OOOO => C0 y
 | OOOI => match y with OOOO => C0 OOOI | OOOI => C0 OOIO | OOIO => C0 OOII | OOII => C0 OIOO | OIOO => C0 OIOI | OIOI => C0 OIIO | OIIO => C0 OIII | OIII => C0 IOOO | IOOO => C0 IOOI | IOOI => C0 IOIO | IOIO => C0 IOII | IOII => C0 IIOO | IIOO => C0 IIOI | IIOI => C0 IIIO | IIIO => C0 IIII | IIII => C1 OOOO end
 | OOIO => match y with OOOO => C0 OOIO | OOOI => C0 OOII | OOIO => C0 OIOO | OOII => C0 OIOI | OIOO => C0 OIIO | OIOI => C0 OIII | OIIO => C0 IOOO | OIII => C0 IOOI | IOOO => C0 IOIO | IOOI => C0 IOII | IOIO => C0 IIOO | IOII => C0 IIOI | IIOO => C0 IIIO | IIOI => C0 IIII | IIIO => C1 OOOO | IIII => C1 OOOI end
 | OOII => match y with OOOO => C0 OOII | OOOI => C0 OIOO | OOIO => C0 OIOI | OOII => C0 OIIO | OIOO => C0 OIII | OIOI => C0 IOOO | OIIO => C0 IOOI | OIII => C0 IOIO | IOOO => C0 IOII | IOOI => C0 IIOO | IOIO => C0 IIOI | IOII => C0 IIIO | IIOO => C0 IIII | IIOI => C1 OOOO | IIIO => C1 OOOI | IIII => C1 OOIO end
 | OIOO => match y with OOOO => C0 OIOO | OOOI => C0 OIOI | OOIO => C0 OIIO | OOII => C0 OIII | OIOO => C0 IOOO | OIOI => C0 IOOI | OIIO => C0 IOIO | OIII => C0 IOII | IOOO => C0 IIOO | IOOI => C0 IIOI | IOIO => C0 IIIO | IOII => C0 IIII | IIOO => C1 OOOO | IIOI => C1 OOOI | IIIO => C1 OOIO | IIII => C1 OOII end
 | OIOI => match y with OOOO => C0 OIOI | OOOI => C0 OIIO | OOIO => C0 OIII | OOII => C0 IOOO | OIOO => C0 IOOI | OIOI => C0 IOIO | OIIO => C0 IOII | OIII => C0 IIOO | IOOO => C0 IIOI | IOOI => C0 IIIO | IOIO => C0 IIII | IOII => C1 OOOO | IIOO => C1 OOOI | IIOI => C1 OOIO | IIIO => C1 OOII | IIII => C1 OIOO end
 | OIIO => match y with OOOO => C0 OIIO | OOOI => C0 OIII | OOIO => C0 IOOO | OOII => C0 IOOI | OIOO => C0 IOIO | OIOI => C0 IOII | OIIO => C0 IIOO | OIII => C0 IIOI | IOOO => C0 IIIO | IOOI => C0 IIII | IOIO => C1 OOOO | IOII => C1 OOOI | IIOO => C1 OOIO | IIOI => C1 OOII | IIIO => C1 OIOO | IIII => C1 OIOI end
 | OIII => match y with OOOO => C0 OIII | OOOI => C0 IOOO | OOIO => C0 IOOI | OOII => C0 IOIO | OIOO => C0 IOII | OIOI => C0 IIOO | OIIO => C0 IIOI | OIII => C0 IIIO | IOOO => C0 IIII | IOOI => C1 OOOO | IOIO => C1 OOOI | IOII => C1 OOIO | IIOO => C1 OOII | IIOI => C1 OIOO | IIIO => C1 OIOI | IIII => C1 OIIO end
 | IOOO => match y with OOOO => C0 IOOO | OOOI => C0 IOOI | OOIO => C0 IOIO | OOII => C0 IOII | OIOO => C0 IIOO | OIOI => C0 IIOI | OIIO => C0 IIIO | OIII => C0 IIII | IOOO => C1 OOOO | IOOI => C1 OOOI | IOIO => C1 OOIO | IOII => C1 OOII | IIOO => C1 OIOO | IIOI => C1 OIOI | IIIO => C1 OIIO | IIII => C1 OIII end
 | IOOI => match y with OOOO => C0 IOOI | OOOI => C0 IOIO | OOIO => C0 IOII | OOII => C0 IIOO | OIOO => C0 IIOI | OIOI => C0 IIIO | OIIO => C0 IIII | OIII => C1 OOOO | IOOO => C1 OOOI | IOOI => C1 OOIO | IOIO => C1 OOII | IOII => C1 OIOO | IIOO => C1 OIOI | IIOI => C1 OIIO | IIIO => C1 OIII | IIII => C1 IOOO end
 | IOIO => match y with OOOO => C0 IOIO | OOOI => C0 IOII | OOIO => C0 IIOO | OOII => C0 IIOI | OIOO => C0 IIIO | OIOI => C0 IIII | OIIO => C1 OOOO | OIII => C1 OOOI | IOOO => C1 OOIO | IOOI => C1 OOII | IOIO => C1 OIOO | IOII => C1 OIOI | IIOO => C1 OIIO | IIOI => C1 OIII | IIIO => C1 IOOO | IIII => C1 IOOI end
 | IOII => match y with OOOO => C0 IOII | OOOI => C0 IIOO | OOIO => C0 IIOI | OOII => C0 IIIO | OIOO => C0 IIII | OIOI => C1 OOOO | OIIO => C1 OOOI | OIII => C1 OOIO | IOOO => C1 OOII | IOOI => C1 OIOO | IOIO => C1 OIOI | IOII => C1 OIIO | IIOO => C1 OIII | IIOI => C1 IOOO | IIIO => C1 IOOI | IIII => C1 IOIO end
 | IIOO => match y with OOOO => C0 IIOO | OOOI => C0 IIOI | OOIO => C0 IIIO | OOII => C0 IIII | OIOO => C1 OOOO | OIOI => C1 OOOI | OIIO => C1 OOIO | OIII => C1 OOII | IOOO => C1 OIOO | IOOI => C1 OIOI | IOIO => C1 OIIO | IOII => C1 OIII | IIOO => C1 IOOO | IIOI => C1 IOOI | IIIO => C1 IOIO | IIII => C1 IOII end
 | IIOI => match y with OOOO => C0 IIOI | OOOI => C0 IIIO | OOIO => C0 IIII | OOII => C1 OOOO | OIOO => C1 OOOI | OIOI => C1 OOIO | OIIO => C1 OOII | OIII => C1 OIOO | IOOO => C1 OIOI | IOOI => C1 OIIO | IOIO => C1 OIII | IOII => C1 IOOO | IIOO => C1 IOOI | IIOI => C1 IOIO | IIIO => C1 IOII | IIII => C1 IIOO end
 | IIIO => match y with OOOO => C0 IIIO | OOOI => C0 IIII | OOIO => C1 OOOO | OOII => C1 OOOI | OIOO => C1 OOIO | OIOI => C1 OOII | OIIO => C1 OIOO | OIII => C1 OIOI | IOOO => C1 OIIO | IOOI => C1 OIII | IOIO => C1 IOOO | IOII => C1 IOOI | IIOO => C1 IOIO | IIOI => C1 IOII | IIIO => C1 IIOO | IIII => C1 IIOI end
 | IIII => match y with OOOO => C0 IIII | OOOI => C1 OOOO | OOIO => C1 OOOI | OOII => C1 OOIO | OIOO => C1 OOII | OIOI => C1 OIOO | OIIO => C1 OIOI | OIII => C1 OIIO | IOOO => C1 OIII | IOOI => C1 IOOO | IOIO => C1 IOOI | IOII => C1 IOIO | IIOO => C1 IOII | IIOI => C1 IIOO | IIIO => C1 IIOI | IIII => C1 IIIO end
 end.

Definition w4_add_carry_c x y :=
 match x with
 | OOOO => match y with OOOO => C0 OOOI | OOOI => C0 OOIO | OOIO => C0 OOII | OOII => C0 OIOO | OIOO => C0 OIOI | OIOI => C0 OIIO | OIIO => C0 OIII | OIII => C0 IOOO | IOOO => C0 IOOI | IOOI => C0 IOIO | IOIO => C0 IOII | IOII => C0 IIOO | IIOO => C0 IIOI | IIOI => C0 IIIO | IIIO => C0 IIII | IIII => C1 OOOO end
 | OOOI => match y with OOOO => C0 OOIO | OOOI => C0 OOII | OOIO => C0 OIOO | OOII => C0 OIOI | OIOO => C0 OIIO | OIOI => C0 OIII | OIIO => C0 IOOO | OIII => C0 IOOI | IOOO => C0 IOIO | IOOI => C0 IOII | IOIO => C0 IIOO | IOII => C0 IIOI | IIOO => C0 IIIO | IIOI => C0 IIII | IIIO => C1 OOOO | IIII => C1 OOOI end
 | OOIO => match y with OOOO => C0 OOII | OOOI => C0 OIOO | OOIO => C0 OIOI | OOII => C0 OIIO | OIOO => C0 OIII | OIOI => C0 IOOO | OIIO => C0 IOOI | OIII => C0 IOIO | IOOO => C0 IOII | IOOI => C0 IIOO | IOIO => C0 IIOI | IOII => C0 IIIO | IIOO => C0 IIII | IIOI => C1 OOOO | IIIO => C1 OOOI | IIII => C1 OOIO end
 | OOII => match y with OOOO => C0 OIOO | OOOI => C0 OIOI | OOIO => C0 OIIO | OOII => C0 OIII | OIOO => C0 IOOO | OIOI => C0 IOOI | OIIO => C0 IOIO | OIII => C0 IOII | IOOO => C0 IIOO | IOOI => C0 IIOI | IOIO => C0 IIIO | IOII => C0 IIII | IIOO => C1 OOOO | IIOI => C1 OOOI | IIIO => C1 OOIO | IIII => C1 OOII end
 | OIOO => match y with OOOO => C0 OIOI | OOOI => C0 OIIO | OOIO => C0 OIII | OOII => C0 IOOO | OIOO => C0 IOOI | OIOI => C0 IOIO | OIIO => C0 IOII | OIII => C0 IIOO | IOOO => C0 IIOI | IOOI => C0 IIIO | IOIO => C0 IIII | IOII => C1 OOOO | IIOO => C1 OOOI | IIOI => C1 OOIO | IIIO => C1 OOII | IIII => C1 OIOO end
 | OIOI => match y with OOOO => C0 OIIO | OOOI => C0 OIII | OOIO => C0 IOOO | OOII => C0 IOOI | OIOO => C0 IOIO | OIOI => C0 IOII | OIIO => C0 IIOO | OIII => C0 IIOI | IOOO => C0 IIIO | IOOI => C0 IIII | IOIO => C1 OOOO | IOII => C1 OOOI | IIOO => C1 OOIO | IIOI => C1 OOII | IIIO => C1 OIOO | IIII => C1 OIOI end
 | OIIO => match y with OOOO => C0 OIII | OOOI => C0 IOOO | OOIO => C0 IOOI | OOII => C0 IOIO | OIOO => C0 IOII | OIOI => C0 IIOO | OIIO => C0 IIOI | OIII => C0 IIIO | IOOO => C0 IIII | IOOI => C1 OOOO | IOIO => C1 OOOI | IOII => C1 OOIO | IIOO => C1 OOII | IIOI => C1 OIOO | IIIO => C1 OIOI | IIII => C1 OIIO end
 | OIII => match y with OOOO => C0 IOOO | OOOI => C0 IOOI | OOIO => C0 IOIO | OOII => C0 IOII | OIOO => C0 IIOO | OIOI => C0 IIOI | OIIO => C0 IIIO | OIII => C0 IIII | IOOO => C1 OOOO | IOOI => C1 OOOI | IOIO => C1 OOIO | IOII => C1 OOII | IIOO => C1 OIOO | IIOI => C1 OIOI | IIIO => C1 OIIO | IIII => C1 OIII end
 | IOOO => match y with OOOO => C0 IOOI | OOOI => C0 IOIO | OOIO => C0 IOII | OOII => C0 IIOO | OIOO => C0 IIOI | OIOI => C0 IIIO | OIIO => C0 IIII | OIII => C1 OOOO | IOOO => C1 OOOI | IOOI => C1 OOIO | IOIO => C1 OOII | IOII => C1 OIOO | IIOO => C1 OIOI | IIOI => C1 OIIO | IIIO => C1 OIII | IIII => C1 IOOO end
 | IOOI => match y with OOOO => C0 IOIO | OOOI => C0 IOII | OOIO => C0 IIOO | OOII => C0 IIOI | OIOO => C0 IIIO | OIOI => C0 IIII | OIIO => C1 OOOO | OIII => C1 OOOI | IOOO => C1 OOIO | IOOI => C1 OOII | IOIO => C1 OIOO | IOII => C1 OIOI | IIOO => C1 OIIO | IIOI => C1 OIII | IIIO => C1 IOOO | IIII => C1 IOOI end
 | IOIO => match y with OOOO => C0 IOII | OOOI => C0 IIOO | OOIO => C0 IIOI | OOII => C0 IIIO | OIOO => C0 IIII | OIOI => C1 OOOO | OIIO => C1 OOOI | OIII => C1 OOIO | IOOO => C1 OOII | IOOI => C1 OIOO | IOIO => C1 OIOI | IOII => C1 OIIO | IIOO => C1 OIII | IIOI => C1 IOOO | IIIO => C1 IOOI | IIII => C1 IOIO end
 | IOII => match y with OOOO => C0 IIOO | OOOI => C0 IIOI | OOIO => C0 IIIO | OOII => C0 IIII | OIOO => C1 OOOO | OIOI => C1 OOOI | OIIO => C1 OOIO | OIII => C1 OOII | IOOO => C1 OIOO | IOOI => C1 OIOI | IOIO => C1 OIIO | IOII => C1 OIII | IIOO => C1 IOOO | IIOI => C1 IOOI | IIIO => C1 IOIO | IIII => C1 IOII end
 | IIOO => match y with OOOO => C0 IIOI | OOOI => C0 IIIO | OOIO => C0 IIII | OOII => C1 OOOO | OIOO => C1 OOOI | OIOI => C1 OOIO | OIIO => C1 OOII | OIII => C1 OIOO | IOOO => C1 OIOI | IOOI => C1 OIIO | IOIO => C1 OIII | IOII => C1 IOOO | IIOO => C1 IOOI | IIOI => C1 IOIO | IIIO => C1 IOII | IIII => C1 IIOO end
 | IIOI => match y with OOOO => C0 IIIO | OOOI => C0 IIII | OOIO => C1 OOOO | OOII => C1 OOOI | OIOO => C1 OOIO | OIOI => C1 OOII | OIIO => C1 OIOO | OIII => C1 OIOI | IOOO => C1 OIIO | IOOI => C1 OIII | IOIO => C1 IOOO | IOII => C1 IOOI | IIOO => C1 IOIO | IIOI => C1 IOII | IIIO => C1 IIOO | IIII => C1 IIOI end
 | IIIO => match y with OOOO => C0 IIII | OOOI => C1 OOOO | OOIO => C1 OOOI | OOII => C1 OOIO | OIOO => C1 OOII | OIOI => C1 OIOO | OIIO => C1 OIOI | OIII => C1 OIIO | IOOO => C1 OIII | IOOI => C1 IOOO | IOIO => C1 IOOI | IOII => C1 IOIO | IIOO => C1 IOII | IIOI => C1 IIOO | IIIO => C1 IIOI | IIII => C1 IIIO end
 | IIII => C1 y
 end.

Definition w4_add x y :=
 without_c (w4_add_c x y).


(* ** Subtractions ** *)

Definition w4_pred_c x :=
 match x with
 | OOOO => C1 IIII
 | OOOI => C0 OOOO
 | OOIO => C0 OOOI
 | OOII => C0 OOIO
 | OIOO => C0 OOII
 | OIOI => C0 OIOO
 | OIIO => C0 OIOI
 | OIII => C0 OIIO
 | IOOO => C0 OIII
 | IOOI => C0 IOOO
 | IOIO => C0 IOOI
 | IOII => C0 IOIO
 | IIOO => C0 IOII
 | IIOI => C0 IIOO
 | IIIO => C0 IIOI
 | IIII => C0 IIIO
 end.

Definition w4_sub_c x y :=
 match y with
 | OOOO => C0 x
 | OOOI => match x with OOOO => C1 IIII | OOOI => C0 OOOO | OOIO => C0 OOOI | OOII => C0 OOIO | OIOO => C0 OOII | OIOI => C0 OIOO | OIIO => C0 OIOI | OIII => C0 OIIO | IOOO => C0 OIII | IOOI => C0 IOOO | IOIO => C0 IOOI | IOII => C0 IOIO | IIOO => C0 IOII | IIOI => C0 IIOO | IIIO => C0 IIOI | IIII => C0 IIIO end
 | OOIO => match x with OOOO => C1 IIIO | OOOI => C1 IIII | OOIO => C0 OOOO | OOII => C0 OOOI | OIOO => C0 OOIO | OIOI => C0 OOII | OIIO => C0 OIOO | OIII => C0 OIOI | IOOO => C0 OIIO | IOOI => C0 OIII | IOIO => C0 IOOO | IOII => C0 IOOI | IIOO => C0 IOIO | IIOI => C0 IOII | IIIO => C0 IIOO | IIII => C0 IIOI end
 | OOII => match x with OOOO => C1 IIOI | OOOI => C1 IIIO | OOIO => C1 IIII | OOII => C0 OOOO | OIOO => C0 OOOI | OIOI => C0 OOIO | OIIO => C0 OOII | OIII => C0 OIOO | IOOO => C0 OIOI | IOOI => C0 OIIO | IOIO => C0 OIII | IOII => C0 IOOO | IIOO => C0 IOOI | IIOI => C0 IOIO | IIIO => C0 IOII | IIII => C0 IIOO end
 | OIOO => match x with OOOO => C1 IIOO | OOOI => C1 IIOI | OOIO => C1 IIIO | OOII => C1 IIII | OIOO => C0 OOOO | OIOI => C0 OOOI | OIIO => C0 OOIO | OIII => C0 OOII | IOOO => C0 OIOO | IOOI => C0 OIOI | IOIO => C0 OIIO | IOII => C0 OIII | IIOO => C0 IOOO | IIOI => C0 IOOI | IIIO => C0 IOIO | IIII => C0 IOII end
 | OIOI => match x with OOOO => C1 IOII | OOOI => C1 IIOO | OOIO => C1 IIOI | OOII => C1 IIIO | OIOO => C1 IIII | OIOI => C0 OOOO | OIIO => C0 OOOI | OIII => C0 OOIO | IOOO => C0 OOII | IOOI => C0 OIOO | IOIO => C0 OIOI | IOII => C0 OIIO | IIOO => C0 OIII | IIOI => C0 IOOO | IIIO => C0 IOOI | IIII => C0 IOIO end
 | OIIO => match x with OOOO => C1 IOIO | OOOI => C1 IOII | OOIO => C1 IIOO | OOII => C1 IIOI | OIOO => C1 IIIO | OIOI => C1 IIII | OIIO => C0 OOOO | OIII => C0 OOOI | IOOO => C0 OOIO | IOOI => C0 OOII | IOIO => C0 OIOO | IOII => C0 OIOI | IIOO => C0 OIIO | IIOI => C0 OIII | IIIO => C0 IOOO | IIII => C0 IOOI end
 | OIII => match x with OOOO => C1 IOOI | OOOI => C1 IOIO | OOIO => C1 IOII | OOII => C1 IIOO | OIOO => C1 IIOI | OIOI => C1 IIIO | OIIO => C1 IIII | OIII => C0 OOOO | IOOO => C0 OOOI | IOOI => C0 OOIO | IOIO => C0 OOII | IOII => C0 OIOO | IIOO => C0 OIOI | IIOI => C0 OIIO | IIIO => C0 OIII | IIII => C0 IOOO end
 | IOOO => match x with OOOO => C1 IOOO | OOOI => C1 IOOI | OOIO => C1 IOIO | OOII => C1 IOII | OIOO => C1 IIOO | OIOI => C1 IIOI | OIIO => C1 IIIO | OIII => C1 IIII | IOOO => C0 OOOO | IOOI => C0 OOOI | IOIO => C0 OOIO | IOII => C0 OOII | IIOO => C0 OIOO | IIOI => C0 OIOI | IIIO => C0 OIIO | IIII => C0 OIII end
 | IOOI => match x with OOOO => C1 OIII | OOOI => C1 IOOO | OOIO => C1 IOOI | OOII => C1 IOIO | OIOO => C1 IOII | OIOI => C1 IIOO | OIIO => C1 IIOI | OIII => C1 IIIO | IOOO => C1 IIII | IOOI => C0 OOOO | IOIO => C0 OOOI | IOII => C0 OOIO | IIOO => C0 OOII | IIOI => C0 OIOO | IIIO => C0 OIOI | IIII => C0 OIIO end
 | IOIO => match x with OOOO => C1 OIIO | OOOI => C1 OIII | OOIO => C1 IOOO | OOII => C1 IOOI | OIOO => C1 IOIO | OIOI => C1 IOII | OIIO => C1 IIOO | OIII => C1 IIOI | IOOO => C1 IIIO | IOOI => C1 IIII | IOIO => C0 OOOO | IOII => C0 OOOI | IIOO => C0 OOIO | IIOI => C0 OOII | IIIO => C0 OIOO | IIII => C0 OIOI end
 | IOII => match x with OOOO => C1 OIOI | OOOI => C1 OIIO | OOIO => C1 OIII | OOII => C1 IOOO | OIOO => C1 IOOI | OIOI => C1 IOIO | OIIO => C1 IOII | OIII => C1 IIOO | IOOO => C1 IIOI | IOOI => C1 IIIO | IOIO => C1 IIII | IOII => C0 OOOO | IIOO => C0 OOOI | IIOI => C0 OOIO | IIIO => C0 OOII | IIII => C0 OIOO end
 | IIOO => match x with OOOO => C1 OIOO | OOOI => C1 OIOI | OOIO => C1 OIIO | OOII => C1 OIII | OIOO => C1 IOOO | OIOI => C1 IOOI | OIIO => C1 IOIO | OIII => C1 IOII | IOOO => C1 IIOO | IOOI => C1 IIOI | IOIO => C1 IIIO | IOII => C1 IIII | IIOO => C0 OOOO | IIOI => C0 OOOI | IIIO => C0 OOIO | IIII => C0 OOII end
 | IIOI => match x with OOOO => C1 OOII | OOOI => C1 OIOO | OOIO => C1 OIOI | OOII => C1 OIIO | OIOO => C1 OIII | OIOI => C1 IOOO | OIIO => C1 IOOI | OIII => C1 IOIO | IOOO => C1 IOII | IOOI => C1 IIOO | IOIO => C1 IIOI | IOII => C1 IIIO | IIOO => C1 IIII | IIOI => C0 OOOO | IIIO => C0 OOOI | IIII => C0 OOIO end
 | IIIO => match x with OOOO => C1 OOIO | OOOI => C1 OOII | OOIO => C1 OIOO | OOII => C1 OIOI | OIOO => C1 OIIO | OIOI => C1 OIII | OIIO => C1 IOOO | OIII => C1 IOOI | IOOO => C1 IOIO | IOOI => C1 IOII | IOIO => C1 IIOO | IOII => C1 IIOI | IIOO => C1 IIIO | IIOI => C1 IIII | IIIO => C0 OOOO | IIII => C0 OOOI end
 | IIII => match x with OOOO => C1 OOOI | OOOI => C1 OOIO | OOIO => C1 OOII | OOII => C1 OIOO | OIOO => C1 OIOI | OIOI => C1 OIIO | OIIO => C1 OIII | OIII => C1 IOOO | IOOO => C1 IOOI | IOOI => C1 IOIO | IOIO => C1 IOII | IOII => C1 IIOO | IIOO => C1 IIOI | IIOI => C1 IIIO | IIIO => C1 IIII | IIII => C0 OOOO end
 end.

Definition w4_sub_carry_c x y :=
 match y with
 | OOOO => match x with OOOO => C1 IIII | OOOI => C0 OOOO | OOIO => C0 OOOI | OOII => C0 OOIO | OIOO => C0 OOII | OIOI => C0 OIOO | OIIO => C0 OIOI | OIII => C0 OIIO | IOOO => C0 OIII | IOOI => C0 IOOO | IOIO => C0 IOOI | IOII => C0 IOIO | IIOO => C0 IOII | IIOI => C0 IIOO | IIIO => C0 IIOI | IIII => C0 IIIO end
 | OOOI => match x with OOOO => C1 IIIO | OOOI => C1 IIII | OOIO => C0 OOOO | OOII => C0 OOOI | OIOO => C0 OOIO | OIOI => C0 OOII | OIIO => C0 OIOO | OIII => C0 OIOI | IOOO => C0 OIIO | IOOI => C0 OIII | IOIO => C0 IOOO | IOII => C0 IOOI | IIOO => C0 IOIO | IIOI => C0 IOII | IIIO => C0 IIOO | IIII => C0 IIOI end
 | OOIO => match x with OOOO => C1 IIOI | OOOI => C1 IIIO | OOIO => C1 IIII | OOII => C0 OOOO | OIOO => C0 OOOI | OIOI => C0 OOIO | OIIO => C0 OOII | OIII => C0 OIOO | IOOO => C0 OIOI | IOOI => C0 OIIO | IOIO => C0 OIII | IOII => C0 IOOO | IIOO => C0 IOOI | IIOI => C0 IOIO | IIIO => C0 IOII | IIII => C0 IIOO end
 | OOII => match x with OOOO => C1 IIOO | OOOI => C1 IIOI | OOIO => C1 IIIO | OOII => C1 IIII | OIOO => C0 OOOO | OIOI => C0 OOOI | OIIO => C0 OOIO | OIII => C0 OOII | IOOO => C0 OIOO | IOOI => C0 OIOI | IOIO => C0 OIIO | IOII => C0 OIII | IIOO => C0 IOOO | IIOI => C0 IOOI | IIIO => C0 IOIO | IIII => C0 IOII end
 | OIOO => match x with OOOO => C1 IOII | OOOI => C1 IIOO | OOIO => C1 IIOI | OOII => C1 IIIO | OIOO => C1 IIII | OIOI => C0 OOOO | OIIO => C0 OOOI | OIII => C0 OOIO | IOOO => C0 OOII | IOOI => C0 OIOO | IOIO => C0 OIOI | IOII => C0 OIIO | IIOO => C0 OIII | IIOI => C0 IOOO | IIIO => C0 IOOI | IIII => C0 IOIO end
 | OIOI => match x with OOOO => C1 IOIO | OOOI => C1 IOII | OOIO => C1 IIOO | OOII => C1 IIOI | OIOO => C1 IIIO | OIOI => C1 IIII | OIIO => C0 OOOO | OIII => C0 OOOI | IOOO => C0 OOIO | IOOI => C0 OOII | IOIO => C0 OIOO | IOII => C0 OIOI | IIOO => C0 OIIO | IIOI => C0 OIII | IIIO => C0 IOOO | IIII => C0 IOOI end
 | OIIO => match x with OOOO => C1 IOOI | OOOI => C1 IOIO | OOIO => C1 IOII | OOII => C1 IIOO | OIOO => C1 IIOI | OIOI => C1 IIIO | OIIO => C1 IIII | OIII => C0 OOOO | IOOO => C0 OOOI | IOOI => C0 OOIO | IOIO => C0 OOII | IOII => C0 OIOO | IIOO => C0 OIOI | IIOI => C0 OIIO | IIIO => C0 OIII | IIII => C0 IOOO end
 | OIII => match x with OOOO => C1 IOOO | OOOI => C1 IOOI | OOIO => C1 IOIO | OOII => C1 IOII | OIOO => C1 IIOO | OIOI => C1 IIOI | OIIO => C1 IIIO | OIII => C1 IIII | IOOO => C0 OOOO | IOOI => C0 OOOI | IOIO => C0 OOIO | IOII => C0 OOII | IIOO => C0 OIOO | IIOI => C0 OIOI | IIIO => C0 OIIO | IIII => C0 OIII end
 | IOOO => match x with OOOO => C1 OIII | OOOI => C1 IOOO | OOIO => C1 IOOI | OOII => C1 IOIO | OIOO => C1 IOII | OIOI => C1 IIOO | OIIO => C1 IIOI | OIII => C1 IIIO | IOOO => C1 IIII | IOOI => C0 OOOO | IOIO => C0 OOOI | IOII => C0 OOIO | IIOO => C0 OOII | IIOI => C0 OIOO | IIIO => C0 OIOI | IIII => C0 OIIO end
 | IOOI => match x with OOOO => C1 OIIO | OOOI => C1 OIII | OOIO => C1 IOOO | OOII => C1 IOOI | OIOO => C1 IOIO | OIOI => C1 IOII | OIIO => C1 IIOO | OIII => C1 IIOI | IOOO => C1 IIIO | IOOI => C1 IIII | IOIO => C0 OOOO | IOII => C0 OOOI | IIOO => C0 OOIO | IIOI => C0 OOII | IIIO => C0 OIOO | IIII => C0 OIOI end
 | IOIO => match x with OOOO => C1 OIOI | OOOI => C1 OIIO | OOIO => C1 OIII | OOII => C1 IOOO | OIOO => C1 IOOI | OIOI => C1 IOIO | OIIO => C1 IOII | OIII => C1 IIOO | IOOO => C1 IIOI | IOOI => C1 IIIO | IOIO => C1 IIII | IOII => C0 OOOO | IIOO => C0 OOOI | IIOI => C0 OOIO | IIIO => C0 OOII | IIII => C0 OIOO end
 | IOII => match x with OOOO => C1 OIOO | OOOI => C1 OIOI | OOIO => C1 OIIO | OOII => C1 OIII | OIOO => C1 IOOO | OIOI => C1 IOOI | OIIO => C1 IOIO | OIII => C1 IOII | IOOO => C1 IIOO | IOOI => C1 IIOI | IOIO => C1 IIIO | IOII => C1 IIII | IIOO => C0 OOOO | IIOI => C0 OOOI | IIIO => C0 OOIO | IIII => C0 OOII end
 | IIOO => match x with OOOO => C1 OOII | OOOI => C1 OIOO | OOIO => C1 OIOI | OOII => C1 OIIO | OIOO => C1 OIII | OIOI => C1 IOOO | OIIO => C1 IOOI | OIII => C1 IOIO | IOOO => C1 IOII | IOOI => C1 IIOO | IOIO => C1 IIOI | IOII => C1 IIIO | IIOO => C1 IIII | IIOI => C0 OOOO | IIIO => C0 OOOI | IIII => C0 OOIO end
 | IIOI => match x with OOOO => C1 OOIO | OOOI => C1 OOII | OOIO => C1 OIOO | OOII => C1 OIOI | OIOO => C1 OIIO | OIOI => C1 OIII | OIIO => C1 IOOO | OIII => C1 IOOI | IOOO => C1 IOIO | IOOI => C1 IOII | IOIO => C1 IIOO | IOII => C1 IIOI | IIOO => C1 IIIO | IIOI => C1 IIII | IIIO => C0 OOOO | IIII => C0 OOOI end
 | IIIO => match x with OOOO => C1 OOOI | OOOI => C1 OOIO | OOIO => C1 OOII | OOII => C1 OIOO | OIOO => C1 OIOI | OIOI => C1 OIIO | OIIO => C1 OIII | OIII => C1 IOOO | IOOO => C1 IOOI | IOOI => C1 IOIO | IOIO => C1 IOII | IOII => C1 IIOO | IIOO => C1 IIOI | IIOI => C1 IIIO | IIIO => C1 IIII | IIII => C0 OOOO end
 | IIII => C1 x
 end.

Definition w4_sub x y :=
 without_c (w4_sub_c x y).


(* ** Multiplcations ** *)

Definition w4_mul_c x y :=
 match x with
 | OOOO => W0
 | OOOI => WW OOOO y
 | OOIO => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOO OIOO | OOII => WW OOOO OIIO | OIOO => WW OOOO IOOO | OIOI => WW OOOO IOIO | OIIO => WW OOOO IIOO | OIII => WW OOOO IIIO | IOOO => WW OOOI OOOO | IOOI => WW OOOI OOIO | IOIO => WW OOOI OIOO | IOII => WW OOOI OIIO | IIOO => WW OOOI IOOO | IIOI => WW OOOI IOIO | IIIO => WW OOOI IIOO | IIII => WW OOOI IIIO end
 | OOII => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOO OIIO | OOII => WW OOOO IOOI | OIOO => WW OOOO IIOO | OIOI => WW OOOO IIII | OIIO => WW OOOI OOIO | OIII => WW OOOI OIOI | IOOO => WW OOOI IOOO | IOOI => WW OOOI IOII | IOIO => WW OOOI IIIO | IOII => WW OOIO OOOI | IIOO => WW OOIO OIOO | IIOI => WW OOIO OIII | IIIO => WW OOIO IOIO | IIII => WW OOIO IIOI end
 | OIOO => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOO IOOO | OOII => WW OOOO IIOO | OIOO => WW OOOI OOOO | OIOI => WW OOOI OIOO | OIIO => WW OOOI IOOO | OIII => WW OOOI IIOO | IOOO => WW OOIO OOOO | IOOI => WW OOIO OIOO | IOIO => WW OOIO IOOO | IOII => WW OOIO IIOO | IIOO => WW OOII OOOO | IIOI => WW OOII OIOO | IIIO => WW OOII IOOO | IIII => WW OOII IIOO end
 | OIOI => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOO IOIO | OOII => WW OOOO IIII | OIOO => WW OOOI OIOO | OIOI => WW OOOI IOOI | OIIO => WW OOOI IIIO | OIII => WW OOIO OOII | IOOO => WW OOIO IOOO | IOOI => WW OOIO IIOI | IOIO => WW OOII OOIO | IOII => WW OOII OIII | IIOO => WW OOII IIOO | IIOI => WW OIOO OOOI | IIIO => WW OIOO OIIO | IIII => WW OIOO IOII end
 | OIIO => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOO IIOO | OOII => WW OOOI OOIO | OIOO => WW OOOI IOOO | OIOI => WW OOOI IIIO | OIIO => WW OOIO OIOO | OIII => WW OOIO IOIO | IOOO => WW OOII OOOO | IOOI => WW OOII OIIO | IOIO => WW OOII IIOO | IOII => WW OIOO OOIO | IIOO => WW OIOO IOOO | IIOI => WW OIOO IIIO | IIIO => WW OIOI OIOO | IIII => WW OIOI IOIO end
 | OIII => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOO IIIO | OOII => WW OOOI OIOI | OIOO => WW OOOI IIOO | OIOI => WW OOIO OOII | OIIO => WW OOIO IOIO | OIII => WW OOII OOOI | IOOO => WW OOII IOOO | IOOI => WW OOII IIII | IOIO => WW OIOO OIIO | IOII => WW OIOO IIOI | IIOO => WW OIOI OIOO | IIOI => WW OIOI IOII | IIIO => WW OIIO OOIO | IIII => WW OIIO IOOI end
 | IOOO => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOI OOOO | OOII => WW OOOI IOOO | OIOO => WW OOIO OOOO | OIOI => WW OOIO IOOO | OIIO => WW OOII OOOO | OIII => WW OOII IOOO | IOOO => WW OIOO OOOO | IOOI => WW OIOO IOOO | IOIO => WW OIOI OOOO | IOII => WW OIOI IOOO | IIOO => WW OIIO OOOO | IIOI => WW OIIO IOOO | IIIO => WW OIII OOOO | IIII => WW OIII IOOO end
 | IOOI => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOI OOIO | OOII => WW OOOI IOII | OIOO => WW OOIO OIOO | OIOI => WW OOIO IIOI | OIIO => WW OOII OIIO | OIII => WW OOII IIII | IOOO => WW OIOO IOOO | IOOI => WW OIOI OOOI | IOIO => WW OIOI IOIO | IOII => WW OIIO OOII | IIOO => WW OIIO IIOO | IIOI => WW OIII OIOI | IIIO => WW OIII IIIO | IIII => WW IOOO OIII end
 | IOIO => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOI OIOO | OOII => WW OOOI IIIO | OIOO => WW OOIO IOOO | OIOI => WW OOII OOIO | OIIO => WW OOII IIOO | OIII => WW OIOO OIIO | IOOO => WW OIOI OOOO | IOOI => WW OIOI IOIO | IOIO => WW OIIO OIOO | IOII => WW OIIO IIIO | IIOO => WW OIII IOOO | IIOI => WW IOOO OOIO | IIIO => WW IOOO IIOO | IIII => WW IOOI OIIO end
 | IOII => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOI OIIO | OOII => WW OOIO OOOI | OIOO => WW OOIO IIOO | OIOI => WW OOII OIII | OIIO => WW OIOO OOIO | OIII => WW OIOO IIOI | IOOO => WW OIOI IOOO | IOOI => WW OIIO OOII | IOIO => WW OIIO IIIO | IOII => WW OIII IOOI | IIOO => WW IOOO OIOO | IIOI => WW IOOO IIII | IIIO => WW IOOI IOIO | IIII => WW IOIO OIOI end
 | IIOO => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOI IOOO | OOII => WW OOIO OIOO | OIOO => WW OOII OOOO | OIOI => WW OOII IIOO | OIIO => WW OIOO IOOO | OIII => WW OIOI OIOO | IOOO => WW OIIO OOOO | IOOI => WW OIIO IIOO | IOIO => WW OIII IOOO | IOII => WW IOOO OIOO | IIOO => WW IOOI OOOO | IIOI => WW IOOI IIOO | IIIO => WW IOIO IOOO | IIII => WW IOII OIOO end
 | IIOI => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOI IOIO | OOII => WW OOIO OIII | OIOO => WW OOII OIOO | OIOI => WW OIOO OOOI | OIIO => WW OIOO IIIO | OIII => WW OIOI IOII | IOOO => WW OIIO IOOO | IOOI => WW OIII OIOI | IOIO => WW IOOO OOIO | IOII => WW IOOO IIII | IIOO => WW IOOI IIOO | IIOI => WW IOIO IOOI | IIIO => WW IOII OIIO | IIII => WW IIOO OOII end
 | IIIO => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOI IIOO | OOII => WW OOIO IOIO | OIOO => WW OOII IOOO | OIOI => WW OIOO OIIO | OIIO => WW OIOI OIOO | OIII => WW OIIO OOIO | IOOO => WW OIII OOOO | IOOI => WW OIII IIIO | IOIO => WW IOOO IIOO | IOII => WW IOOI IOIO | IIOO => WW IOIO IOOO | IIOI => WW IOII OIIO | IIIO => WW IIOO OIOO | IIII => WW IIOI OOIO end
 | IIII => match y with OOOO => W0 | OOOI => WW OOOO x | OOIO => WW OOOI IIIO | OOII => WW OOIO IIOI | OIOO => WW OOII IIOO | OIOI => WW OIOO IOII | OIIO => WW OIOI IOIO | OIII => WW OIIO IOOI | IOOO => WW OIII IOOO | IOOI => WW IOOO OIII | IOIO => WW IOOI OIIO | IOII => WW IOIO OIOI | IIOO => WW IOII OIOO | IIOI => WW IIOO OOII | IIIO => WW IIOI OOIO | IIII => WW IIIO OOOI end
 end.

Definition w4_mul x y :=
 match w4_mul_c x y with
 | W0 => OOOO
 | WW _ l => l
 end.

Definition w4_square_c x :=
 match x with
 | OOOO => WW OOOO OOOO
 | OOOI => WW OOOO OOOI
 | OOIO => WW OOOO OIOO
 | OOII => WW OOOO IOOI
 | OIOO => WW OOOI OOOO
 | OIOI => WW OOOI IOOI
 | OIIO => WW OOIO OIOO
 | OIII => WW OOII OOOI
 | IOOO => WW OIOO OOOO
 | IOOI => WW OIOI OOOI
 | IOIO => WW OIIO OIOO
 | IOII => WW OIII IOOI
 | IIOO => WW IOOI OOOO
 | IIOI => WW IOIO IOOI
 | IIIO => WW IIOO OIOO
 | IIII => WW IIIO OOOI
 end.


(* ** Division ** *)

Definition w4_div_wB x y :=
 match y with
 | OOOO => (C0 OOOO, OOOO)
 | OOOI => (C0 OOOO, OOOO)
 | OOIO => (C0 OOOO, OOOO)
 | OOII => (C0 OOOO, OOOO)
 | OIOO => (C0 OOOO, OOOO)
 | OIOI => (C0 OOOO, OOOO)
 | OIIO => (C0 OOOO, OOOO)
 | OIII => (C0 OOOO, OOOO)
 | IOOO => match x with OOOO => (C0 OOOO, OOOO) | OOOI => (C0 OOIO, OOOO) | OOIO => (C0 OIOO, OOOO) | OOII => (C0 OIIO, OOOO) | OIOO => (C0 IOOO, OOOO) | OIOI => (C0 IOIO, OOOO) | OIIO => (C0 IIOO, OOOO) | OIII => (C0 IIIO, OOOO) | IOOO => (C1 OOOO, OOOO) | IOOI => (C1 OOIO, OOOO) | IOIO => (C1 OIOO, OOOO) | IOII => (C1 OIIO, OOOO) | IIOO => (C1 IOOO, OOOO) | IIOI => (C1 IOIO, OOOO) | IIIO => (C1 IIOO, OOOO) | IIII => (C1 IIIO, OOOO)   end
 | IOOI => match x with OOOO => (C0 OOOO, OOOO) | OOOI => (C0 OOOI, OIII) | OOIO => (C0 OOII, OIOI) | OOII => (C0 OIOI, OOII) | OIOO => (C0 OIII, OOOI) | OIOI => (C0 IOOO, IOOO) | OIIO => (C0 IOIO, OIIO) | OIII => (C0 IIOO, OIOO) | IOOO => (C0 IIIO, OOIO) | IOOI => (C1 OOOO, OOOO) | IOIO => (C1 OOOI, OIII) | IOII => (C1 OOII, OIOI) | IIOO => (C1 OIOI, OOII) | IIOI => (C1 OIII, OOOI) | IIIO => (C1 IOOO, IOOO) | IIII => (C1 IOIO, OIIO)   end
 | IOIO => match x with OOOO => (C0 OOOO, OOOO) | OOOI => (C0 OOOI, OIIO) | OOIO => (C0 OOII, OOIO) | OOII => (C0 OIOO, IOOO) | OIOO => (C0 OIIO, OIOO) | OIOI => (C0 IOOO, OOOO) | OIIO => (C0 IOOI, OIIO) | OIII => (C0 IOII, OOIO) | IOOO => (C0 IIOO, IOOO) | IOOI => (C0 IIIO, OIOO) | IOIO => (C1 OOOO, OOOO) | IOII => (C1 OOOI, OIIO) | IIOO => (C1 OOII, OOIO) | IIOI => (C1 OIOO, IOOO) | IIIO => (C1 OIIO, OIOO) | IIII => (C1 IOOO, OOOO)   end
 | IOII => match x with OOOO => (C0 OOOO, OOOO) | OOOI => (C0 OOOI, OIOI) | OOIO => (C0 OOIO, IOIO) | OOII => (C0 OIOO, OIOO) | OIOO => (C0 OIOI, IOOI) | OIOI => (C0 OIII, OOII) | OIIO => (C0 IOOO, IOOO) | OIII => (C0 IOIO, OOIO) | IOOO => (C0 IOII, OIII) | IOOI => (C0 IIOI, OOOI) | IOIO => (C0 IIIO, OIIO) | IOII => (C1 OOOO, OOOO) | IIOO => (C1 OOOI, OIOI) | IIOI => (C1 OOIO, IOIO) | IIIO => (C1 OIOO, OIOO) | IIII => (C1 OIOI, IOOI)   end
 | IIOO => match x with OOOO => (C0 OOOO, OOOO) | OOOI => (C0 OOOI, OIOO) | OOIO => (C0 OOIO, IOOO) | OOII => (C0 OIOO, OOOO) | OIOO => (C0 OIOI, OIOO) | OIOI => (C0 OIIO, IOOO) | OIIO => (C0 IOOO, OOOO) | OIII => (C0 IOOI, OIOO) | IOOO => (C0 IOIO, IOOO) | IOOI => (C0 IIOO, OOOO) | IOIO => (C0 IIOI, OIOO) | IOII => (C0 IIIO, IOOO) | IIOO => (C1 OOOO, OOOO) | IIOI => (C1 OOOI, OIOO) | IIIO => (C1 OOIO, IOOO) | IIII => (C1 OIOO, OOOO)   end
 | IIOI => match x with OOOO => (C0 OOOO, OOOO) | OOOI => (C0 OOOI, OOII) | OOIO => (C0 OOIO, OIIO) | OOII => (C0 OOII, IOOI) | OIOO => (C0 OIOO, IIOO) | OIOI => (C0 OIIO, OOIO) | OIIO => (C0 OIII, OIOI) | OIII => (C0 IOOO, IOOO) | IOOO => (C0 IOOI, IOII) | IOOI => (C0 IOII, OOOI) | IOIO => (C0 IIOO, OIOO) | IOII => (C0 IIOI, OIII) | IIOO => (C0 IIIO, IOIO) | IIOI => (C1 OOOO, OOOO) | IIIO => (C1 OOOI, OOII) | IIII => (C1 OOIO, OIIO)   end
 | IIIO => match x with OOOO => (C0 OOOO, OOOO) | OOOI => (C0 OOOI, OOIO) | OOIO => (C0 OOIO, OIOO) | OOII => (C0 OOII, OIIO) | OIOO => (C0 OIOO, IOOO) | OIOI => (C0 OIOI, IOIO) | OIIO => (C0 OIIO, IIOO) | OIII => (C0 IOOO, OOOO) | IOOO => (C0 IOOI, OOIO) | IOOI => (C0 IOIO, OIOO) | IOIO => (C0 IOII, OIIO) | IOII => (C0 IIOO, IOOO) | IIOO => (C0 IIOI, IOIO) | IIOI => (C0 IIIO, IIOO) | IIIO => (C1 OOOO, OOOO) | IIII => (C1 OOOI, OOIO)   end
 | IIII => match x with OOOO => (C0 OOOO, OOOO) | OOOI => (C0 OOOI, OOOI) | OOIO => (C0 OOIO, OOIO) | OOII => (C0 OOII, OOII) | OIOO => (C0 OIOO, OIOO) | OIOI => (C0 OIOI, OIOI) | OIIO => (C0 OIIO, OIIO) | OIII => (C0 OIII, OIII) | IOOO => (C0 IOOO, IOOO) | IOOI => (C0 IOOI, IOOI) | IOIO => (C0 IOIO, IOIO) | IOII => (C0 IOII, IOII) | IIOO => (C0 IIOO, IIOO) | IIOI => (C0 IIOI, IIOI) | IIIO => (C0 IIIO, IIIO) | IIII => (C1 OOOO, OOOO)   end
 end.

Definition w4_div21 a1 a2 b :=
 let (q,s) := w4_div_wB a1 b in
 match w4_add_c s a2 with
 | C0 r =>
   match w4_compare r b with
   | Lt => (q, r)
   | _ =>
     let q := w4_carry_succ_c q in
     let r := w4_sub r b in
     match w4_compare r b with
     | Lt => (q, r)
     | _ => (w4_carry_succ_c q, w4_sub r b)
     end
   end
 | C1 r =>
   let q := w4_carry_succ_c q in
   match w4_sub_c r b with
   | C0 r => (w4_carry_succ_c q, w4_sub r b)
   | C1 r =>
     match w4_compare r b with
     | Lt => (q, r)
     | _ => (w4_carry_succ_c q, w4_sub r b)
     end
   end
 end.


(* ** Lift operations ** *)

Definition w4_lsl1 x :=
 match x with
 | OOOO => OOOO
 | OOOI => OOIO
 | OOIO => OIOO
 | OOII => OIIO
 | OIOO => IOOO
 | OIOI => IOIO
 | OIIO => IIOO
 | OIII => IIIO
 | IOOO => OOOO
 | IOOI => OOIO
 | IOIO => OIOO
 | IOII => OIIO
 | IIOO => IOOO
 | IIOI => IOIO
 | IIIO => IIOO
 | IIII => IIIO
 end.

Definition w4_lsl2 x :=
 match x with
 | OOOO => OOOO
 | OOOI => OIOO
 | OOIO => IOOO
 | OOII => IIOO
 | OIOO => OOOO
 | OIOI => OIOO
 | OIIO => IOOO
 | OIII => IIOO
 | IOOO => OOOO
 | IOOI => OIOO
 | IOIO => IOOO
 | IOII => IIOO
 | IIOO => OOOO
 | IIOI => OIOO
 | IIIO => IOOO
 | IIII => IIOO
 end.

Definition w4_lsl3 x :=
 match x with
 | OOOO => OOOO
 | OOOI => IOOO
 | OOIO => OOOO
 | OOII => IOOO
 | OIOO => OOOO
 | OIOI => IOOO
 | OIIO => OOOO
 | OIII => IOOO
 | IOOO => OOOO
 | IOOI => IOOO
 | IOIO => OOOO
 | IOII => IOOO
 | IIOO => OOOO
 | IIOI => IOOO
 | IIIO => OOOO
 | IIII => IOOO
 end.


Definition w4_lsr1 x :=
 match x with
 | OOOO => OOOO
 | OOOI => OOOO
 | OOIO => OOOI
 | OOII => OOOI
 | OIOO => OOIO
 | OIOI => OOIO
 | OIIO => OOII
 | OIII => OOII
 | IOOO => OIOO
 | IOOI => OIOO
 | IOIO => OIOI
 | IOII => OIOI
 | IIOO => OIIO
 | IIOI => OIIO
 | IIIO => OIII
 | IIII => OIII
 end.

Definition w4_lsr2 x :=
 match x with
 | OOOO => OOOO
 | OOOI => OOOO
 | OOIO => OOOO
 | OOII => OOOO
 | OIOO => OOOI
 | OIOI => OOOI
 | OIIO => OOOI
 | OIII => OOOI
 | IOOO => OOIO
 | IOOI => OOIO
 | IOIO => OOIO
 | IOII => OOIO
 | IIOO => OOII
 | IIOI => OOII
 | IIIO => OOII
 | IIII => OOII
 end.

Definition w4_lsr3 x :=
 match x with
 | OOOO => OOOO
 | OOOI => OOOO
 | OOIO => OOOO
 | OOII => OOOO
 | OIOO => OOOO
 | OIOI => OOOO
 | OIIO => OOOO
 | OIII => OOOO
 | IOOO => OOOI
 | IOOI => OOOI
 | IOIO => OOOI
 | IOII => OOOI
 | IIOO => OOOI
 | IIOI => OOOI
 | IIIO => OOOI
 | IIII => OOOI
 end.


Definition w4_add_mul_div x y p :=
 match p with
 | xH => w4_add (w4_lsl1 x) (w4_lsr3 y)
 | (xO xH) => w4_add (w4_lsl2 x) (w4_lsr2 y)
 | (xI xH) => w4_add (w4_lsl3 x) (w4_lsr1 y)
 | _ => OOOO
 end.

(* ** Record of basic operators for base 16 ** *)

Definition w4_op  :=
 mk_znz_op 4
       w4_to_Z w4_of_pos w4_head0
       OOOO OOOI IIII
       w4_WW w4_CW
       w4_compare
       w4_opp_c w4_opp_carry
       w4_succ_c
       w4_add_c w4_add_carry_c w4_add
       w4_pred_c
       w4_sub_c w4_sub_carry_c w4_sub
       w4_mul_c w4_mul w4_square_c
       w4_div21 w4_add_mul_div.

