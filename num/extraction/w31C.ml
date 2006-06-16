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
 
type uint = int

external uint_compare : uint -> uint -> comparison = "uint_compare"

external uint_add_c : uint -> uint -> uint carry = "uint_add_c"
external uint_add_carry_c : uint -> uint -> uint carry = "uint_add_carry_c"

external uint_sub_c : uint -> uint -> uint carry = "uint_sub_c"
external uint_sub_carry_c : uint -> uint -> uint carry = "uint_sub_carry_c"

external uint_mul_c : uint -> uint -> uint zn2z = "uint_mul_c"

external uint_div21 : 
  uint -> uint -> uint -> (uint,uint) prod = "uint_div21"

external uint_div_eucl : uint -> uint -> (uint,uint) prod = "uint_div_eucl" 

external uint_mod : uint -> uint -> uint = "uint_mod" 

let rec uint_gcd a b = 
  if b == 0 then a 
  else uint_gcd b (uint_mod a b)

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

let uint_WW h l = 
  if h == 0 && l == 0 then W0 else WW(h,l)

let uint_W0 h = if h == 0 then W0 else WW(h,0)

let uint_0W l = if l == 0 then W0 else WW(0,l)

let uint_add_mul_div p x y =
  let Coq_pair(_,_p) = of_pos p in
  (x lsl _p) + (y lsr (31 - _p))

let uint_pos_mod p x =  
  let Coq_pair(_, _p) = of_pos p in
  let q = 31 - _p in
  (x lsl q) lsr q

let two30 = Big_int.power_int_positive_int 2 30
let two31 = Big_int.power_int_positive_int 2 31
let two32 = Big_int.power_int_positive_int 2 32

let big_int_of_uint x = 
  if x < 0 then
    Big_int.add_big_int two30 (Big_int.big_int_of_int (x lxor 0x40000000))
  else Big_int.big_int_of_int x

let uint_of_big_int x =
  if Big_int.lt_big_int x two30 then Big_int.int_of_big_int x
  else Big_int.int_of_big_int (Big_int.sub_big_int x two31) 

let uint_sqrt2 x y = 
  let n = 
    Big_int.add_big_int
      (Big_int.mult_big_int (big_int_of_uint x) two31)
      (big_int_of_uint y) in
  let sqrt = Big_int.sqrt_big_int n in
  let r = Big_int.sub_big_int n (Big_int.square_big_int sqrt) in
  let cr = 
    if Big_int.lt_big_int r two31 then  C0(uint_of_big_int r)
    else C1(uint_of_big_int (Big_int.sub_big_int r two32)) in
  Coq_pair(uint_of_big_int sqrt, cr)

let uint_sqrt x = 
  let _x = big_int_of_uint x in
  let sqrt = Big_int.sqrt_big_int _x in
  uint_of_big_int sqrt

let uint_is_even x = 
  if x lsl 30 = 0 then Coq_true else Coq_false
  
let w31_0_op = {
  znz_digits = digits;
  znz_to_Z = to_Z;
  znz_of_pos = of_pos;
  znz_head0 = head0;
  znz_0 = 0;
  znz_1 = 1;
  znz_Bm1 = -1;
  znz_WW = uint_WW;
  znz_W0 = uint_W0;
  znz_0W = uint_0W;
  znz_compare = uint_compare;
  znz_eq0 = (fun x -> if x == 0 then Coq_true else Coq_false);
  znz_opp_c = (fun x -> if x == 0 then C0 0 else C1 (-x));
  znz_opp = (fun x -> -x);
  znz_opp_carry = (fun x -> -x - 1);
  znz_succ_c = (fun x -> if x == -1 then C1 0 else C0 (x+1));
  znz_add_c = uint_add_c;
  znz_add_carry_c = uint_add_carry_c;
  znz_succ = (fun x -> x + 1);
  znz_add = (fun x y-> x + y);
  znz_add_carry = (fun x y -> x + y + 1);
  znz_pred_c = (fun x -> if x == 0 then C1 (-1) else C0 (x-1));
  znz_sub_c = uint_sub_c;
  znz_sub_carry_c = uint_sub_carry_c;
  znz_pred = (fun x -> x - 1);
  znz_sub = (fun x y-> x - y);
  znz_sub_carry = (fun x y -> x - y - 1);
  znz_mul_c = uint_mul_c;
  znz_mul = (fun x y -> x * y);
  znz_square_c = (fun x -> uint_mul_c x x);
  znz_div21 = uint_div21;
  znz_div_gt = uint_div_eucl;
  znz_div = uint_div_eucl;
  znz_mod_gt = uint_mod;
  znz_mod = uint_mod;
  znz_gcd_gt = uint_gcd;
  znz_gcd = uint_gcd;
  znz_add_mul_div = uint_add_mul_div;
  znz_pos_mod = uint_pos_mod;
  znz_is_even = uint_is_even;
  znz_sqrt2 = uint_sqrt2;
  znz_sqrt = uint_sqrt
}

let w31_1_op  = mk_zn2z_op w31_0_op           
let w31_2_op  = mk_zn2z_op w31_1_op
let w31_3_op  = mk_zn2z_op_karatsuba w31_2_op
let w31_4_op  = mk_zn2z_op_karatsuba w31_3_op
let w31_5_op  = mk_zn2z_op_karatsuba w31_4_op
let w31_6_op  = mk_zn2z_op_karatsuba w31_5_op
let w31_7_op  = mk_zn2z_op_karatsuba w31_6_op
let w31_8_op  = mk_zn2z_op_karatsuba w31_7_op
let w31_9_op  = mk_zn2z_op_karatsuba w31_8_op
let w31_10_op = mk_zn2z_op_karatsuba w31_9_op
let w31_11_op = mk_zn2z_op_karatsuba w31_10_op
let w31_12_op = mk_zn2z_op_karatsuba w31_11_op
let w31_13_op = mk_zn2z_op_karatsuba w31_12_op
let w31_14_op = mk_zn2z_op_karatsuba w31_13_op

(*
1 62
2 124
3 248
4 496
5 992
6 1984
7 3968
8 7936
9 15872
10 31744
11 63488
12 126976
13 253952
14 507904
*)

let ww_of_BI w_WW w_of_BI x =
  if Big_int.eq_big_int x Big_int.zero_big_int then x, W0
  else
    let ql, l = w_of_BI x in 
    let qh, h = w_of_BI ql in
    qh, w_WW h l 

let w31_0_of_BI x = 
  let q, r = Big_int.quomod_big_int x two31 in
  q, uint_of_big_int r 
  
let w31_1_of_BI = ww_of_BI w31_0_op.znz_WW w31_0_of_BI
let w31_2_of_BI = ww_of_BI w31_1_op.znz_WW w31_1_of_BI
let w31_3_of_BI = ww_of_BI w31_2_op.znz_WW w31_2_of_BI
let w31_4_of_BI = ww_of_BI w31_3_op.znz_WW w31_3_of_BI
let w31_5_of_BI = ww_of_BI w31_4_op.znz_WW w31_4_of_BI
let w31_6_of_BI = ww_of_BI w31_5_op.znz_WW w31_5_of_BI
let w31_7_of_BI = ww_of_BI w31_6_op.znz_WW w31_6_of_BI
let w31_8_of_BI = ww_of_BI w31_7_op.znz_WW w31_7_of_BI
let w31_9_of_BI = ww_of_BI w31_8_op.znz_WW w31_8_of_BI
let w31_10_of_BI = ww_of_BI w31_9_op.znz_WW w31_9_of_BI
let w31_11_of_BI = ww_of_BI w31_10_op.znz_WW w31_10_of_BI
let w31_12_of_BI = ww_of_BI w31_11_op.znz_WW w31_11_of_BI
let w31_13_of_BI = ww_of_BI w31_12_op.znz_WW w31_12_of_BI
let w31_14_of_BI = ww_of_BI w31_13_op.znz_WW w31_13_of_BI


  
  
  
  



