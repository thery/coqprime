open BinInt
open BinPos
open Datatypes
open Mod_op
open Zmisc
open ZnZ
open Zpower

(** val znz_of_Z : 'a1 znz_op -> coq_Z -> 'a1 **)

let znz_of_Z op = function
  | Z0 -> op.znz_0
  | Zpos p -> snd (op.znz_of_pos p)
  | Zneg p -> op.znz_0

(** val lucastest : 'a1 znz_op -> positive -> coq_Z **)

let lucastest op p =
  let b =
    znz_of_Z op
      (coq_Zminus (coq_Zpower (Zpos (Coq_xO Coq_xH)) (Zpos p)) (Zpos Coq_xH))
  in
  let mod_op = make_mod_op op b in
  let w2 = op.znz_add op.znz_1 op.znz_1 in
  let w4 = op.znz_add w2 w2 in
  let square_m2 =
    let square = fun x -> mod_op.square_mod x in
    let sub = fun x x0 -> mod_op.sub_mod x x0 in (fun x -> sub (square x) w2)
  in
  op.znz_to_Z (iter_pos (coq_Pminus p (Coq_xO Coq_xH)) square_m2 w4)

