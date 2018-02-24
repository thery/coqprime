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
 
type uint64 = int64

external uint64_compare : uint64 -> uint64 -> comparison = "uint64_compare"

external uint64_add_c : uint64 -> uint64 -> uint64 carry = "uint64_add_c"
external uint64_add_carry_c : uint64 -> uint64 -> uint64 carry = 
     "uint64_add_carry_c"

external uint64_sub_c : uint64 -> uint64 -> uint64 carry = "uint64_sub_c"
external uint64_sub_carry_c : uint64 -> uint64 -> uint64 carry =
     "uint64_sub_carry_c"

external uint64_mul_c : uint64 -> uint64 -> uint64 zn2z = "uint64_mul_c"

external uint64_div21 : 
  uint64 -> uint64 -> uint64 -> (uint64,uint64) prod = "uint64_div21"

external uint64_div_eucl : 
  uint64 -> uint64 -> (uint64,uint64) prod = "uint64_div_eucl" 

external uint64_mod : uint64 -> uint64 -> uint64 = "uint64_mod" 

let uint64_eq0 x = x == Int64.zero || x = Int64.zero 

let rec uint64_gcd a b = 
  if uint64_eq0 b then a 
  else uint64_gcd b (uint64_mod a b)

let rec uint64_to_pos x =
  let y = Int64.shift_right_logical x 1 in
  if uint64_eq0 y then Coq_xH
  else 
    let r = Int64.sub x (Int64.shift_left y 1) in
    if uint64_eq0 r then Coq_xO (uint64_to_pos y)
    else Coq_xI (uint64_to_pos y)

let rec pow2_to_pos x =
  if x <= 0 then Coq_xH
  else Coq_xO (pow2_to_pos (x-1))

let pow_2_63 = pow2_to_pos 63
    
let digits = uint64_to_pos (Int64.of_int 64)

let ui64_pow2_63 = Int64.shift_left Int64.one 63

let to_Z x =
  match Int64.compare x Int64.zero with
  | s when s > 0 -> Zpos (uint64_to_pos x)
  | s when s = 0 -> Z0
  | _ ->
      let xl = Int64.logxor ui64_pow2_63 x in
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
  if uint64_eq0 x then N0
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
  let rec aux x p =
    if p >= 64 then 64 
    else if uint64_eq0 (Int64.logand x ui64_pow2_63) then
      aux (Int64.shift_left x 1) (p+1)
    else p in
  int_to_N (aux x 0)

let uint64_add_mul_div p x y = 
  match int_of_pos p with
  | Coq_pair(_,_p) -> 
     Int64.logor 
	(Int64.shift_left x _p) 
	(Int64.shift_right_logical y (64 -_p))


let uint64_WW h l = 
  if uint64_eq0 h && uint64_eq0 l then W0 else WW(h,l)

let uint64_W0 h = if uint64_eq0 h then W0 else WW(h, Int64.zero)

let uint64_0W l = if uint64_eq0 l then W0 else WW(Int64.zero,l)
 
let uint64_pos_mod p x = 
  let Coq_pair(_,n) = int_of_pos p in
  let diff = 64 - n in
  Int64.shift_right_logical (Int64.shift_left x diff) diff

let uint64_sqrt2 x y = raise Not_found
    
let uint64_sqrt x = raise Not_found

let uint64_is_even x = raise Not_found
 
let w64_0_op = {
  znz_digits = digits;
  znz_to_Z = to_Z;
  znz_of_pos = of_pos;
  znz_head0 = head0;
  znz_0 = Int64.zero;
  znz_1 = Int64.one;
  znz_Bm1 = Int64.minus_one;
  znz_WW = uint64_WW;
  znz_W0 = uint64_W0;
  znz_0W = uint64_0W;
  znz_compare = uint64_compare;
  znz_eq0 = (fun x -> if uint64_eq0 x then Coq_true else Coq_false);
  znz_opp_c = 
  (fun x -> 
    if uint64_eq0 x then C0 Int64.zero 
    else C1 (Int64.neg x));
  znz_opp = Int64.neg;
  znz_opp_carry = (fun x -> Int64.pred (Int64.neg x));
  znz_succ_c = 
      (fun x -> 
	if x = Int64.minus_one then C1 Int64.zero 
	else C0 (Int64.add x Int64.one));
  znz_add_c = uint64_add_c;
  znz_add_carry_c = uint64_add_carry_c;
  znz_succ = Int64.succ;
  znz_add = Int64.add;
  znz_add_carry = (fun x y -> Int64.succ (Int64.add x y));
  znz_pred_c = 
      (fun x -> 
	if uint64_eq0 x then C1 (Int64.minus_one) 
	else C0 (Int64.pred x));
  znz_sub_c = uint64_sub_c;
  znz_sub_carry_c = uint64_sub_carry_c;
  znz_pred = Int64.pred;
  znz_sub = Int64.sub;
  znz_sub_carry = (fun x y -> Int64.pred (Int64.sub x y));
  znz_mul_c = uint64_mul_c;
  znz_mul = Int64.mul;
  znz_square_c = (fun x -> uint64_mul_c x x);
  znz_div21 = uint64_div21;
  znz_div_gt = uint64_div_eucl;
  znz_div = uint64_div_eucl;
  znz_mod_gt = uint64_mod;
  znz_mod = uint64_mod;
  znz_gcd_gt = uint64_gcd;
  znz_gcd = uint64_gcd;
  znz_add_mul_div = uint64_add_mul_div;
  znz_pos_mod = uint64_pos_mod;
  znz_is_even = uint64_is_even;
  znz_sqrt2 = uint64_sqrt2;
  znz_sqrt = uint64_sqrt
}

let w64_1_op  = mk_zn2z_op w64_0_op           
let w64_2_op  = mk_zn2z_op w64_1_op
let w64_3_op  = mk_zn2z_op_karatsuba w64_2_op
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

let ww_of_BI w_WW w_of_BI x =
  if Big_int.eq_big_int x Big_int.zero_big_int then x, W0
  else
    let ql, l = w_of_BI x in 
    let qh, h = w_of_BI ql in
    qh, w_WW h l 

let two64 = Big_int.power_int_positive_int 2 64 
let two16 = Big_int.power_int_positive_int 2 16 

let uint64_of_4 r4 r3 r2 r1 = 
  let x4 = Int64.of_int r4 in
  let x3 = Int64.add (Int64.shift_left x4 16) (Int64.of_int r3) in
  let x2 = Int64.add (Int64.shift_left x3 16) (Int64.of_int r2) in
  Int64.add (Int64.shift_left x2 16) (Int64.of_int r1) 

let w64_0_of_BI x = 
  let q1, r1 = Big_int.quomod_big_int x two16 in
  let q2, r2 = Big_int.quomod_big_int q1 two16 in
  let q3, r3 = Big_int.quomod_big_int q2 two16 in
  let q4, r4 = Big_int.quomod_big_int q3 two16 in
  q4, uint64_of_4 (Big_int.int_of_big_int r4) (Big_int.int_of_big_int r3) 
                  (Big_int.int_of_big_int r2) (Big_int.int_of_big_int r1)

  
let w64_1_of_BI = ww_of_BI w64_0_op.znz_WW w64_0_of_BI
let w64_2_of_BI = ww_of_BI w64_1_op.znz_WW w64_1_of_BI
let w64_3_of_BI = ww_of_BI w64_2_op.znz_WW w64_2_of_BI
let w64_4_of_BI = ww_of_BI w64_3_op.znz_WW w64_3_of_BI
let w64_5_of_BI = ww_of_BI w64_4_op.znz_WW w64_4_of_BI
let w64_6_of_BI = ww_of_BI w64_5_op.znz_WW w64_5_of_BI
let w64_7_of_BI = ww_of_BI w64_6_op.znz_WW w64_6_of_BI
let w64_8_of_BI = ww_of_BI w64_7_op.znz_WW w64_7_of_BI
let w64_9_of_BI = ww_of_BI w64_8_op.znz_WW w64_8_of_BI
let w64_10_of_BI = ww_of_BI w64_9_op.znz_WW w64_9_of_BI
let w64_11_of_BI = ww_of_BI w64_10_op.znz_WW w64_10_of_BI
let w64_12_of_BI = ww_of_BI w64_11_op.znz_WW w64_11_of_BI
let w64_13_of_BI = ww_of_BI w64_12_op.znz_WW w64_12_of_BI
let w64_14_of_BI = ww_of_BI w64_13_op.znz_WW w64_13_of_BI

