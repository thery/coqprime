open Datatypes
open BinPos
open BinNat
open BinInt
open Zpower
open Zmisc
open Basic_type
open ZnZ
open Zn2Z
open GenWord
open Mod_op
 
type uint64 = int64

external uint64_lt : uint64 -> uint64 -> Datatypes.bool = "uint64_lt"

external uint64_le : uint64 -> uint64 -> Datatypes.bool = "uint64_le"

external uint64_compare : uint64 -> uint64 -> comparison = "uint64_compare"

external uint64_mul_c : uint64 -> uint64 -> (uint64,uint64) prod 
 = "uint64_mul_c"

external uint64_div21 : 
  uint64 -> uint64 -> uint64 -> (uint64,uint64) prod = "uint64_div21"

external uint64_div_eucl : 
  uint64 -> uint64 -> (uint64,uint64) prod = "uint64_div_eucl" 

external uint64_mod : uint64 -> uint64 -> uint64 = "uint64_mod" 

module Uint = 
  struct 
    
    type uint = uint64
	  
    let zero = Int64.zero
	
    let one = Int64.one

    let coq_Bm1 = Int64.minus_one

    let opp = Int64.neg

    let add = Int64.add
	
    let sub = Int64.sub

    let mul = Int64.mul

    let mul_c = uint64_mul_c 
	
    let square_c x = uint64_mul_c x x

    let div21 = uint64_div21 

    let div_eucl = uint64_div_eucl

    let uint_mod = uint64_mod 

    let rec uint64_to_pos x =
      let y = Int64.shift_right_logical x 1 in
      if y = Int64.zero then Coq_xH
      else 
	let r = Int64.sub x (Int64.shift_left y 1) in
	if r = Int64.zero then Coq_xO (uint64_to_pos y)
	else Coq_xI (uint64_to_pos y)

    let rec pow2_to_pos x =
      if x <= 0 then Coq_xH
      else Coq_xO (pow2_to_pos (x-1))

    let pow_2_63 = pow2_to_pos 63

    let digits = uint64_to_pos (Int64.of_int 64)

    let to_Z x =
      match Int64.compare x Int64.zero with
      | s when s > 0 -> Zpos (uint64_to_pos x)
      | s when s = 0 -> Z0
      | _ ->
	  let xl = Int64.logxor (Int64.shift_left Int64.one 63) x in
	  Zpos (coq_Pplus pow_2_63 (uint64_to_pos xl))

    let of_pos p =
      let rec aux p count = 
	if count = 0 then Coq_pair(Npos p, Int64.one)
	else
	  match p with
	  | Coq_xH -> Coq_pair(N0, Int64.one)
	  | Coq_xO p -> 
	      begin match aux p (count-1) with
              | Coq_pair(n,w) -> Coq_pair(n, Int64.shift_left w 1)
	      end
	  | Coq_xI p -> 
	      begin match aux p (count-1) with
	      | Coq_pair(n,w) -> 
		  let w' =Int64.shift_left w 1 in 
		  Coq_pair(n, Int64.logor w' Int64.one)
	      end
      in aux p 64 

    let int_of_pos p =
      let rec aux p count = 
	if count = 0 then Coq_pair(Npos p, 1)
	else
	  match p with
	  | Coq_xH -> Coq_pair(N0, 1)
	  | Coq_xO p -> 
	      begin match aux p (count-1) with
              | Coq_pair(n,w) -> Coq_pair(n, w lsl 1)
	      end
	  | Coq_xI p -> 
	      begin match aux p (count-1) with
	      | Coq_pair(n,w) -> 
		  let w' = w lsl 1 in 
		  Coq_pair(n, w' lor 1)
	      end
      in aux p 31 

    let to_N x = 
      if x = Int64.zero then N0
      else Npos (uint64_to_pos x)

    let rec uint_to_pos x =
      let y = x/2 in
      if y = 0 then Coq_xH
      else if x mod 2 = 0 then Coq_xO (uint_to_pos y)
      else Coq_xI (uint_to_pos y)

    let int_to_N x = 
      if x = 0 then N0
      else Npos (uint_to_pos x)


    let head0 x =
      let pow63 = Int64.shift_left Int64.one 63 in
      let rec aux x p =
	if p >= 64 then 64 
	else if Int64.logand x pow63 = Int64.zero then
	  aux (Int64.shift_left x 1) (p+1)
	else p in
      int_to_N (aux x 0)

    let coq_lsl x p =
      match int_of_pos p with
      | Coq_pair(_,_p) -> Int64.shift_left x _p

    let coq_lsr x p = 
      match int_of_pos p with
      | Coq_pair(_,_p) -> Int64.shift_right_logical x _p

    let eqb x y = if x = y then Coq_true else Coq_false

    let ltb = uint64_lt 

    let leb = uint64_le 
	
    let compare = uint64_compare

    let pos_mod p x = 
      let Coq_pair(_,n) = int_of_pos p in
      let diff = 64 - n in
      Int64.shift_right_logical (Int64.shift_left x diff) diff

    let sqrt2 x y = raise Not_found
    
    let sqrt x = raise Not_found

    let is_even x = raise Not_found
  
  end

module UintZnZ = MakeUintZnZ(Uint)


let w64_0_op = UintZnZ.uint_op
let w64_1_op  = mk_zn2z_op w64_0_op           
let w64_2_op  = mk_zn2z_op w64_1_op
let w64_3_op  = mk_zn2z_op w64_2_op
let w64_4_op  = mk_zn2z_op_karatsuba w64_3_op
let w64_5_op  = mk_zn2z_op_karatsuba w64_4_op
let w64_6_op  = mk_zn2z_op_karatsuba w64_5_op
let w64_7_op  = mk_zn2z_op_karatsuba w64_6_op
let w64_8_op  = mk_zn2z_op_karatsuba w64_7_op
let w64_9_op  = mk_zn2z_op_karatsuba w64_8_op
let w64_10_op = mk_zn2z_op_karatsuba w64_9_op
let w64_11_op = mk_zn2z_op_karatsuba w64_10_op
let w64_12_op = mk_zn2z_op_karatsuba w64_11_op
let w64_13_op = mk_zn2z_op_karatsuba w64_12_op
let w64_14_op = mk_zn2z_op_karatsuba w64_13_op



(*
1 128
2 256
3 512
4 1024
5 2048
6 4096
7 8192
8 16384
9 32768
10 65536
11 131072
12 262144
13 524288
14 1048576
*)

