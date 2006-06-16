open Datatypes
open BinPos
open BinNat
open BinInt
open Zpower
open Zmisc
open Basic_type
open ZnZ
open GenWord
open Mod_op
 
type uint = int

external uint_lt : uint -> uint -> Datatypes.bool = "uint_lt"

external uint_le : uint -> uint -> Datatypes.bool = "uint_le"

external uint_compare : uint -> uint -> comparison = "uint_compare"

external uint_mul_c : uint -> uint -> (uint,uint) prod = "uint_mul_c"

external uint_div21 : 
  uint -> uint -> uint -> (uint,uint) prod = "uint_div21"

external uint_div_eucl : uint -> uint -> (uint,uint) prod = "uint_div_eucl" 

external uint_mod : uint -> uint -> uint = "uint_mod" 

module Uint = 
  struct 
    
    type uint = int
	  
    let zero = 0
	
    let one = 1

    let coq_Bm1 = -1

    let opp x = -x

    let add x y = x + y
	
    let sub x y = x - y

    let mul x y = x * y

    let mul_c x y = uint_mul_c x y
	
    let square_c x = uint_mul_c x x

    let div21 x y z = uint_div21 x y z

    let div_eucl x y = uint_div_eucl x y

    let uint_mod x y = uint_mod x y

    let rec uint_to_pos x =
      let y = x/2 in
      if y = 0 then Coq_xH
      else if x mod 2 = 0 then Coq_xO (uint_to_pos y)
      else Coq_xI (uint_to_pos y)

    let rec pow2_to_pos x =
      if x <= 0 then Coq_xH
      else Coq_xO (pow2_to_pos (x-1))

    let pow_2_30 = pow2_to_pos 30

    let digits = uint_to_pos 31

    let to_Z x =
      match x with
      | x when x > 0 -> Zpos (uint_to_pos x)
      | x when x = 0 -> Z0
      | x -> Zpos (coq_Pplus pow_2_30 (uint_to_pos (0x40000000 lxor x)))

    let of_pos p =
      let rec aux p n = 
	if n = 0 then Coq_pair(Npos p, 1)
	else
	  match p with
	  | Coq_xH -> Coq_pair(N0, 1)
	  | Coq_xO p -> 
	    begin match aux p (n-1) with
            | Coq_pair(n,w) -> Coq_pair(n, w lsl 1)
	    end
	  | Coq_xI p -> 
	    begin match aux p (n-1) with
	    | Coq_pair(n,w) -> Coq_pair(n, (w lsl 1) lor 1)
	    end
      in aux p 31 
	   
    let to_N x = 
      if x = 0 then N0
      else Npos (uint_to_pos x)
	
    let head0 x =
      let rec aux x p =
	if p >= 31 then 31 
	else if x land 0x40000000 = 0 then aux (x lsl 1) (p+1)
	else p in
      to_N (aux x 0)
	
    let coq_lsl x p =
      match of_pos p with
      | Coq_pair(_,_p) -> x lsl _p
	  
    let coq_lsr x p = 
      match of_pos p with
      | Coq_pair(_,_p) -> x lsr _p
	  
    let eqb x y = if x == y then Coq_true else Coq_false
      
    let ltb x y = uint_lt x y
		    
    let leb x y = uint_le x y
		    
    let compare x y = uint_compare x y

  end

module UintZnZ = MakeUintZnZ(Uint)

let w62_op = UintZnZ.w1_op
let w124_op = UintZnZ.w2_op
let w248_op = UintZnZ.w3_op
let w496_op = UintZnZ.w4_op
let w992_op = UintZnZ.w5_op
let w1984_op = UintZnZ.w6_op
let w3968_op = UintZnZ.w7_op
let w7936_op = UintZnZ.w8_op
let w15872_op = UintZnZ.w9_op
let w31744_op = UintZnZ.w10_op
let w63488_op = UintZnZ.w11_op
let w126976_op = UintZnZ.w12_op
let w253952_op = UintZnZ.w13_op
let w507904_op = UintZnZ.w14_op

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
    iter_pos (coq_Pminus (Uint.uint_to_pos p) (Coq_xO Coq_xH)) square_m2 
      (Big_int.big_int_of_int 4)
  in
  let time  = Sys.time () -. t in
  Format.print_string "Big finished in ";
  Format.print_float time;Format.print_string "\n";
  Format.print_flush()


 
      
let _ = lucastest w3968_op (Uint.uint_to_pos 3217) 
(*let _ = bi_lucastest 3217



let _ = lucastest w15872_op (Uint.uint_to_pos 11213) 
let _ = bi_lucastest 11213

let _ = lucastest w31744_op (Uint.uint_to_pos 23209) 
let _ = bi_lucastest 23209


*)
