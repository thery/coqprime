Require Import ZArith.
Require Import ZnZ.

(*
Unset Boxed Definitions.
*)

Open Local Scope Z_scope.

Inductive w2 : Set :=
 | OO : w2
 | OI : w2
 | IO : w2
 | II : w2.


(* ** Conversion functions with Z, N and positive ** *)

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

Definition w2_head0 x :=
 match x with
 | OO => Npos (xO xH)
 | OI => Npos xH
 | IO => N0
 | II => N0
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

Definition w2_CW ch xl :=
 match ch with
 | C0 xh => C0 (w2_WW xh xl)
 | C1 xh => C1 (w2_WW xh xl)
 end.


(* ** Comparison ** *)

Definition w2_compare x y :=
 match x with
 | OO => match y with  | OO => Eq | _ => Lt end
 | OI => match y with  | OO => Gt | OI => Eq | _ => Lt end
 | IO => match y with  | OO => Gt | OI => Gt | IO => Eq | _ => Lt end
 | II => match y with  | OO => Gt | OI => Gt | IO => Gt | II => Eq end
 end.


(* ** Opposites ** *)

Definition w2_opp_c x :=
 match x with
 | OO => C0 OO
 | OI => C1 II
 | IO => C1 IO
 | II => C1 OI
 end.

Definition w2_opp_carry x :=
 match x with
 | OO => II
 | OI => IO
 | IO => OI
 | II => OO
 end.


(* ** Additions ** *)

Definition w2_succ_c x :=
 match x with
 | OO => C0 OI
 | OI => C0 IO
 | IO => C0 II
 | II => C1 OO
 end.

Definition w2_carry_succ_c cx :=
 match cx with
 | C0 x => w2_succ_c x
 | C1 x => C1 (without_c (w2_succ_c x))
 end.

Definition w2_add_c x y :=
 match x with
 | OO => C0 y
 | OI => match y with OO => C0 OI | OI => C0 IO | IO => C0 II | II => C1 OO end
 | IO => match y with OO => C0 IO | OI => C0 II | IO => C1 OO | II => C1 OI end
 | II => match y with OO => C0 II | OI => C1 OO | IO => C1 OI | II => C1 IO end
 end.

Definition w2_add_carry_c x y :=
 match x with
 | OO => match y with OO => C0 OI | OI => C0 IO | IO => C0 II | II => C1 OO end
 | OI => match y with OO => C0 IO | OI => C0 II | IO => C1 OO | II => C1 OI end
 | IO => match y with OO => C0 II | OI => C1 OO | IO => C1 OI | II => C1 IO end
 | II => C1 y
 end.

Definition w2_add x y :=
 without_c (w2_add_c x y).


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
 | OI => match x with OO => C1 II | OI => C0 OO | IO => C0 OI | II => C0 IO end
 | IO => match x with OO => C1 IO | OI => C1 II | IO => C0 OO | II => C0 OI end
 | II => match x with OO => C1 OI | OI => C1 IO | IO => C1 II | II => C0 OO end
 end.

Definition w2_sub_carry_c x y :=
 match y with
 | OO => match x with OO => C1 II | OI => C0 OO | IO => C0 OI | II => C0 IO end
 | OI => match x with OO => C1 IO | OI => C1 II | IO => C0 OO | II => C0 OI end
 | IO => match x with OO => C1 OI | OI => C1 IO | IO => C1 II | II => C0 OO end
 | II => C1 x
 end.

Definition w2_sub x y :=
 without_c (w2_sub_c x y).


(* ** Multiplcations ** *)

Definition w2_mul_c x y :=
 match x with
 | OO => W0
 | OI => WW OO y
 | IO => match y with OO => W0 | OI => WW OO x | IO => WW OI OO | II => WW OI IO end
 | II => match y with OO => W0 | OI => WW OO x | IO => WW OI IO | II => WW IO OI end
 end.

Definition w2_mul x y :=
 match w2_mul_c x y with
 | W0 => OO
 | WW _ l => l
 end.

Definition w2_square_c x :=
 match x with
 | OO => WW OO OO
 | OI => WW OO OI
 | IO => WW OI OO
 | II => WW IO OI
 end.


(* ** Division ** *)

Definition w2_div_wB x y :=
 match y with
 | OO => (C0 OO, OO)
 | OI => (C0 OO, OO)
 | IO => match x with OO => (C0 OO, OO) | OI => (C0 IO, OO) | IO => (C1 OO, OO) | II => (C1 IO, OO)   end
 | II => match x with OO => (C0 OO, OO) | OI => (C0 OI, OI) | IO => (C0 IO, IO) | II => (C1 OO, OO)   end
 end.

Definition w2_div21 a1 a2 b :=
 let (q,s) := w2_div_wB a1 b in
 match w2_add_c s a2 with
 | C0 r =>
   match w2_compare r b with
   | Lt => (q, r)
   | _ =>
     let q := w2_carry_succ_c q in
     let r := w2_sub r b in
     match w2_compare r b with
     | Lt => (q, r)
     | _ => (w2_carry_succ_c q, w2_sub r b)
     end
   end
 | C1 r =>
   let q := w2_carry_succ_c q in
   match w2_sub_c r b with
   | C0 r => (w2_carry_succ_c q, w2_sub r b)
   | C1 r =>
     match w2_compare r b with
     | Lt => (q, r)
     | _ => (w2_carry_succ_c q, w2_sub r b)
     end
   end
 end.


(* ** Lift operations ** *)

Definition w2_lsl1 x :=
 match x with
 | OO => OO
 | OI => IO
 | IO => OO
 | II => IO
 end.


Definition w2_lsr1 x :=
 match x with
 | OO => OO
 | OI => OO
 | IO => OI
 | II => OI
 end.


Definition w2_add_mul_div x y p :=
 match p with
 | xH => w2_add (w2_lsl1 x) (w2_lsr1 y)
 | _ => OO
 end.

(* ** Record of basic operators for base 4 ** *)

Definition w2_op  :=
 mk_znz_op 2
       w2_to_Z w2_of_pos w2_head0
       OO OI II
       w2_WW w2_CW
       w2_compare
       w2_opp_c w2_opp_carry
       w2_succ_c
       w2_add_c w2_add_carry_c w2_add
       w2_pred_c
       w2_sub_c w2_sub_carry_c w2_sub
       w2_mul_c w2_mul w2_square_c
       w2_div21 w2_add_mul_div.

