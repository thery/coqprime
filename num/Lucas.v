(*
Unset Boxed Definitions.
*)
Set Implicit Arguments.

Require Import ZArith.
Require Import ZnZ.
Require Import Zn2Z.
Require Import Mod_op.
Require Import W8.
Require Import W.

Definition znz_of_Z (w:Set) (op:znz_op w) z :=
 match z with
 | Zpos p => snd (op.(znz_of_pos) p)
 | _ => op.(znz_0)
 end.

Definition lucastest (w:Set) (op:znz_op w) p :=
 let b := znz_of_Z op (Zpower 2 (Zpos p) - 1) in
 let mod_op := make_mod_op op b in
 let w2 := op.(znz_add) op.(znz_1) op.(znz_1) in
 let w4 := op.(znz_add) w2 w2 in
 let square_m2 :=
   let square := mod_op.(square_mod) in
   let sub := mod_op.(sub_mod) in
   fun x => sub (square x) w2   
 in
 op.(znz_to_Z) (iter_pos (Pminus p 2) _ square_m2 w4).


  

Time Eval compute in lucastest w1024_op 521.
(*

Time Eval vm_compute in lucastest w1024_op 521.
(* sans square : Finished transaction in 8. secs (7.66u,0.01s) *)
(* Finished transaction in 6. secs (5.74u,0.01s) *)

;
Time Eval vm_compute in lucastest w1024_op 607.
(* sans square : Finished transaction in 11. secs (11.09u,0.01s) *)
(* Finished transaction in 9. secs (8.98u,0.02s) *)

Time Eval vm_compute in lucastest w2048_op 1279.
(* sans square : Finished transaction in 71. secs (71.u,0.07s) *)
(* Finished transaction in 58. secs (58.41u,0.06s) *)

Time Eval vm_compute in lucastest w4096_op 2203.
(* sans square : Finished transaction in 324. secs (323.43u,0.01s) *)
(* Finished transaction in 251. secs (250.2u,0.04s) *)

Time Eval vm_compute in lucastest w4096_op 2281.
(* sans square : Finished transaction in 348. secs (346.96u,0.04s) *)
(*  *)

Time Eval vm_compute in lucastest w4096_op 3217.
(* sans square : Finished transaction in 743. secs (739.61u,0.11s) *)
(*  *)

Time Eval vm_compute in lucastest w8192_op 4253.
(* sans square : Finished transaction in 1831. secs (1828.36u,0.06s)*)
(*  *)

Time Eval vm_compute in lucastest w8192_op 4423.
(* sans square : Finished transaction in 2062. secs (2033.38u,4.11s)  *)
(*  *)

Time Eval vm_compute in lucastest w16384_op 9689.
(* sans square : Finished transaction in 15458. secs (15401.47u,14.59s) *)
(* Finished transaction in 12702. secs (12641.09u,13.19s) *)

Time Eval vm_compute in lucastest w16384_op 9941.
(* sans square : Finished transaction in 16252. secs (16168.4u,6.86s) *)
(*  *)

Time Eval vm_compute in lucastest w16384_op 11213.
(*  *)

(* Test power *)

Definition powertest (w:Set) (op:znz_op w) x p b :=
  let wb := znz_of_Z op b in  
  let wx := znz_of_Z op x in 
  let mod_op := make_mod_op op wb in
  mod_op.(power_mod) wx p.

Eval compute in ((Zpower 2 521) - 1)%Z.

Time Eval vm_compute in powertest w1024_op 3 
6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057150
6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151.


*)
