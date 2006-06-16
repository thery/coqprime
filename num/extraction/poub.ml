
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
  Format.print_float time;Format.print_string "\n";
  (match op.znz_compare op.znz_0 res with
  | Eq -> Format.print_string " result is 0\n"
  | _ -> Format.print_string " result is not 0\n");
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
  Format.print_string "Big finished in ";
  Format.print_float time;Format.print_string "\n"; 
  if Big_int.eq_big_int res Big_int.zero_big_int then
    Format.print_string " result is 0\n"
  else Format.print_string " result is not 0\n";
  Format.print_flush()


 

let _ = lucastest w3968_op (uint_to_pos 3217) 
(* let _ = bi_lucastest 3217 *)

(*

let _ = lucastest w15872_op (Uint.uint_to_pos 11213) 
let _ = bi_lucastest 11213

let _ = lucastest w31744_op (Uint.uint_to_pos 23209) 
let _ = bi_lucastest 23209


*)
