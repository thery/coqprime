open Datatypes
open BinPos
open BinNat
open BinInt
open Zpower
open Zmisc
open Basic_type
open ZnZ
open Zn2Z
open Mod_op
open W31C
open W64C

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
    let square =  mod_op.square_mod in
    let sub = mod_op.sub_mod in 
    fun x -> sub (square x) w2
  in 
  let t = Sys.time () in
  let res =
    iter_pos (coq_Pminus p (Coq_xO Coq_xH)) square_m2 w4 in
  let time  = Sys.time () -. t in
  Format.print_string "Finished in ";
  Format.print_float time;
  (match op.znz_compare op.znz_0 res with
  | Eq -> Format.print_string "s, result is 0\n"
  | _ -> Format.print_string "s, result is not 0\n");
  Format.print_flush()
 
let mlucastest op p =
  let b =
    znz_of_Z op
      (coq_Zminus (coq_Zpower (Zpos (Coq_xO Coq_xH)) (Zpos p)) (Zpos Coq_xH))
  in
  let mod_op = mmake_mod_op op b p (coq_Pminus (Coq_xO op.znz_digits) p) in
  let w2 = op.znz_add op.znz_1 op.znz_1 in
  let w4 = op.znz_add w2 w2 in
  let square_m2 =
    let square =  mod_op.square_mod in
    let sub = mod_op.sub_mod in 
    fun x -> sub (square x) w2
  in 
  let t = Sys.time () in
  let res =
    iter_pos (coq_Pminus p (Coq_xO Coq_xH)) square_m2 w4 in
  let time  = Sys.time () -. t in
  Format.print_string "Finished in ";
  Format.print_float time;
  (match op.znz_compare op.znz_0 res with
  | Eq -> Format.print_string "s, result is 0\n"
  | _ -> Format.print_string "s, result is not 0\n");
  Format.print_flush()
      
let bi_lucastest p =
  let b = Big_int.pred_big_int (Big_int.power_int_positive_int 2 p) in
  let square_m2 x =  
    Big_int.mod_big_int 
      (Big_int.sub_big_int(Big_int.square_big_int x)(Big_int.big_int_of_int 2))
      b in
  let t = Sys.time () in
  let res =
    iter_pos (coq_Pminus (uint_to_pos p) (Coq_xO Coq_xH)) square_m2 
      (Big_int.big_int_of_int 4)
  in
  let time  = Sys.time () -. t in
  Format.print_string "Finished in ";
  Format.print_float time;
  if Big_int.eq_big_int res Big_int.zero_big_int then
    Format.print_string "s, result is 0\n"
  else Format.print_string "s, result is not 0\n";
  Format.print_flush()


let _ = mlucastest w31_7_op (uint_to_pos 3217)

let mk_test op31 op64 n = 
  Format.printf "test mersenne %i\n" n;
  print_string "w31C : ";
  mlucastest op31 (uint_to_pos n);
  print_string "w64C : ";
  mlucastest op64 (uint_to_pos n);
  print_string "Big_int : ";
  bi_lucastest n; 
  print_string "\n\n"

let _ = mk_test w31_3_op w64_1_op 127
let _ = mk_test w31_5_op w64_4_op 521
let _ = mk_test w31_5_op w64_4_op 607
let _ = mk_test w31_6_op w64_5_op 1279
let _ = mk_test w31_7_op w64_6_op 2203
let _ = mk_test w31_7_op w64_6_op 2281
let _ = mk_test w31_7_op w64_6_op 3217
let _ = mk_test w31_8_op w64_7_op 4253
let _ = mk_test w31_8_op w64_7_op 4423
let _ = mk_test w31_9_op w64_8_op 9689
let _ = mk_test w31_9_op w64_8_op 9941
let _ = mk_test w31_9_op w64_8_op 11213
let _ = mk_test w31_10_op w64_9_op 19937
let _ = mk_test w31_10_op w64_9_op 21701
let _ = mk_test w31_10_op w64_9_op 23209
let _ = mk_test w31_11_op w64_10_op 44497
