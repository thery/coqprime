Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import ZnZ.
Require Import ZnZDivn1.

Open Local Scope Z_scope.


Section Zn2Z.
 
 Variable w : Set.
 Variable w_op : znz_op w.

 Let w_digits      := w_op.(znz_digits).
 Let w_to_Z        := w_op.(znz_to_Z).
 Let w_of_pos      := w_op.(znz_of_pos).
 Let w_head0       := w_op.(znz_head0).

 Let w0            := w_op.(znz_0).
 Let w1            := w_op.(znz_1).
 Let wBm1          := w_op.(znz_Bm1).

 Let wWW           := w_op.(znz_WW).
 Let wCW           := w_op.(znz_CW).

 Let w_compare     := w_op.(znz_compare).
 Let w_opp_c       := w_op.(znz_opp_c).
 Let w_opp         := w_op.(znz_opp).
 Let w_opp_carry   := w_op.(znz_opp_carry).

 Let w_succ_c      := w_op.(znz_succ_c).
 Let w_add_c       := w_op.(znz_add_c).
 Let w_add_carry_c := w_op.(znz_add_carry_c).
 Let w_succ        := w_op.(znz_succ).
 Let w_add         := w_op.(znz_add).
 Let w_add_carry   := w_op.(znz_add_carry).

 Let w_pred_c      := w_op.(znz_pred_c).
 Let w_sub_c       := w_op.(znz_sub_c).
 Let w_sub_carry_c := w_op.(znz_sub_carry_c).
 Let w_pred        := w_op.(znz_pred).
 Let w_sub         := w_op.(znz_sub).
 Let w_sub_carry   := w_op.(znz_sub_carry).


 Let w_mul_c       := w_op.(znz_mul_c).
 Let w_mul         := w_op.(znz_mul).
 Let w_square_c    := w_op.(znz_square_c).

 Let w_div21       := w_op.(znz_div21).
 Let w_divn1       := w_op.(znz_divn1).
 Let w_div_gt      := w_op.(znz_div_gt).
 Let w_div         := w_op.(znz_div).

 Let w_modn1       := w_op.(znz_modn1).
 Let w_mod_gt      := w_op.(znz_mod_gt).
 Let w_mod         := w_op.(znz_mod).

 Let w_gcd_gt      := w_op.(znz_gcd_gt).
 Let w_gcd         := w_op.(znz_gcd).

 Let w_add_mul_div := w_op.(znz_add_mul_div). 

 Let w_pos_mod := w_op.(znz_pos_mod).

 Let _zn2z := zn2z w.

 Let wB := base w_digits.

 Let wBm2 := w_pred wBm1.

 Let ww_digits := xO w_digits.

 Let ww_to_Z := zn2z_to_Z wB w_to_Z.

 Let ww_of_pos p :=
  match w_of_pos p with
  | (N0, l) => (N0, WW w0 l)
  | (Npos ph,l) => 
    let (n,h) := w_of_pos ph in (n, wWW h l)
  end.

 Let head0 x :=
  match x with
  | W0 => Npos ww_digits
  | WW xh xl =>
    match w_compare xh w0 with
    | Eq => Nplus (Npos w_digits) (w_head0 xl)
    | _ => w_head0 xh
    end
  end.

 Let ww_1 :=  WW w0 w1.

 Let ww_Bm1 := WW wBm1 wBm1.

 Let ww_WW xh xl : zn2z _zn2z :=
  match xh, xl with
  | W0, W0 => W0
  | _, _ => WW xh xl
  end.
 
 Let ww_CW ch l : carry (zn2z _zn2z) :=
  match ch with
  | C0 h => C0 (ww_WW h l)
  | C1 h => C1 (ww_WW h l)
  end.

 (* ** Comparison ** *)
 Let compare x y :=
  match x, y with
  | W0, W0 => Eq
  | W0, WW yh yl =>
    match w_compare w0 yh with
    | Eq => w_compare w0 yl 
    | cmp => cmp
    end
  | WW xh xl, W0 =>
    match w_compare xh w0 with
    | Eq => w_compare xl w0
    | cmp => cmp
    end
  | WW xh xl, WW yh yl =>
    match w_compare xh yh with
    | Eq => w_compare xl yl
    | cmp => cmp
    end
  end.

 (* ** Opposites ** *)
 Let ww_opp_c x :=
  match x with
  | W0 => C0 W0
  | WW xh xl => 
    match w_opp_c xl with
    | C0 _ => wCW (w_opp_c xh) w0
    | C1 l => C1 (wWW (w_opp_carry xh) l)
    end
  end.

 Let ww_opp x :=
  match x with
  | W0 => W0
  | WW xh xl => 
    match w_opp_c xl with
    | C0 _ => WW (w_opp xh) w0
    | C1 l => WW (w_opp_carry xh) l
    end
  end.

 Let ww_opp_carry x :=
  match x with
  | W0 => ww_Bm1
  | WW xh xl => wWW (w_opp_carry xh) (w_opp_carry xl)
  end.
  
 (* ** Additions ** *)

 Let ww_succ_c x :=
  match x with
  | W0 => C0 ww_1
  | WW xh xl => 
    match w_succ_c xl with
    | C0 l => C0 (WW xh l)
    | C1 l => wCW (w_succ_c xh) l
    end
  end.

 Let ww_succ x := 
  match x with
  | W0 => ww_1
  | WW xh xl =>
    match w_succ_c xl with
    | C0 l => WW xh l
    | C1 l => WW (w_succ xh) l
    end
  end.

 Let add_c x y :=
  match x, y with
  | W0, _ => C0 y
  | _, W0 => C0 x
  | WW xh xl, WW yh yl =>
    match w_add_c xl yl with
    | C0 l => wCW (w_add_c xh yh) l
    | C1 l => wCW (w_add_carry_c xh yh) l
    end
  end.

 Let add x y :=
  match x, y with
  | W0, _ => y
  | _, W0 => x
  | WW xh xl, WW yh yl =>
    match w_add_c xl yl with
    | C0 l => wWW (w_add xh yh) l
    | C1 l => wWW (w_add_carry xh yh) l
    end
  end.

 Let add_carry_c x y :=
  match x, y with
  | W0, W0 => C0 ww_1
  | W0, WW yh yl =>
    match w_succ_c yl with
    | C0 l => C0 (WW yh l)
    | C1 l => wCW (w_succ_c yh) l
    end
  | WW xh xl, W0 =>
    match w_succ_c xl with
    | C0 l => C0 (WW xh l)
    | C1 l => wCW (w_succ_c xh) l
    end
  | WW xh xl, WW yh yl =>
    match w_add_carry_c xl yl with
    | C0 l => wCW (w_add_c xh yh) l
    | C1 l => wCW (w_add_carry_c xh yh) l
    end
  end.

 Let add_carry x y := 
  match x, y with
  | W0, W0 => ww_1
  | W0, WW yh yl =>
    match w_succ_c yl with
    | C0 l => WW yh l
    | C1 l => WW (w_succ yh) l
    end
  | WW xh xl, W0 =>
    match w_succ_c xl with
    | C0 l => WW xh l
    | C1 l => WW (w_succ xh) l
    end
  | WW xh xl, WW yh yl =>
    match w_add_carry_c xl yl with
    | C0 l => WW (w_add xh yh) l
    | C1 l => WW (w_add_carry xh yh) l
    end
  end.

 (* ** Subtractions ** *)

 Let ww_pred_c x :=
  match x with
  | W0 => C1 ww_Bm1
  | WW xh xl =>
    match w_pred_c xl with
    | C0 l => C0 (wWW xh l)
    | C1 l => wCW (w_pred_c xh) l
    end
  end.
 
 Let ww_pred x :=
  match x with
  | W0 => ww_Bm1
  | WW xh xl =>
    match w_pred_c xl with
    | C0 l => wWW xh l
    | C1 l => wWW (w_pred xh) l
    end
  end.
     
 Let sub_c x y :=
  match y, x with
  | W0, _ => C0 x
  | WW yh yl, W0 => 
    match w_opp_c yl with
    | C0 _ => wCW (w_opp_c yh) w0
    | C1 l => C1 (wWW (w_opp_carry yh) l)
    end
  | WW yh yl, WW xh xl =>
    match w_sub_c xl yl with
    | C0 l => wCW (w_sub_c xh yh) l
    | C1 l => wCW (w_sub_carry_c xh yh) l
    end
  end.

 Let sub x y := 
  match y, x with
  | W0, _ => x
  | WW yh yl, W0 => 
    match w_opp_c yl with
    | C0 _ => WW (w_opp yh) w0
    | C1 l => WW (w_opp_carry yh) l
    end
  | WW yh yl, WW xh xl =>
    match w_sub_c xl yl with
    | C0 l => wWW (w_sub xh yh) l
    | C1 l => wWW (w_sub_carry xh yh) l
    end
  end.

 Let ww_sub_carry_c x y :=
  match y, x with
  | W0, W0 => C1 ww_Bm1
  | W0, WW xh xl => 
    match w_pred_c xl with
    | C0 l => C0 (wWW xh l)
    | C1 l => wCW (w_pred_c xh) l
    end  
  | WW yh yl, W0 => C1 (wWW (w_opp_carry yh) (w_opp_carry yl))
  | WW yh yl, WW xh xl =>
    match w_sub_carry_c xl yl with
    | C0 l => wCW (w_sub_c xh yh) l
    | C1 l => wCW (w_sub_carry_c xh yh) l
    end
  end.

 Let ww_sub_carry x y :=
  match y, x with
  | W0, W0 => ww_Bm1
  | W0, WW xh xl => 
    match w_pred_c xl with
    | C0 l => wWW xh l
    | C1 l => wWW (w_pred xh) l
    end  
  | WW yh yl, W0 => wWW (w_opp_carry yh) (w_opp_carry yl)
  | WW yh yl, WW xh xl =>
    match w_sub_carry_c xl yl with
    | C0 l => wWW (w_sub xh yh) l
    | C1 l => wWW (w_sub_carry xh yh) l
    end
  end.

 (* ** Multiplication ** *)

 (*   (xh*B+xl) (yh*B + yl)
   xh*yh         = hh  = |hhh|hhl|B2
   xh*yl +xl*yh  = cc  =     |cch|ccl|B
   xl*yl         = ll  =         |llh|lll 
 *)

 Let ww_mul_c x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0
  | WW xh xl, WW yh yl =>
    let hh := w_mul_c xh yh in
    let ll := w_mul_c xl yl in
    let cc_c := add_c (w_mul_c xh yl) (w_mul_c xl yh) in 
    let (wc,cc) :=
      match cc_c with
      | C0 cc => (w0, cc)
      | C1 cc => (w1, cc)
      end
    in match cc with
    | W0 => WW (add hh (WW wc w0)) ll
    | WW cch ccl =>
      match add_c (WW ccl w0) ll with
      | C0 l => WW (add hh (WW wc cch)) l
      | C1 l => WW (add_carry hh (WW wc cch)) l
      end
    end
  end.

 Definition kara_prod cxhl cyhl hh ll :=
  match cxhl, cyhl with
  | C0 xhl, C0 yhl => (w0, sub (sub (w_mul_c xhl yhl) hh) ll)
  | C0 xhl, C1 yhl => 
    match add_c (w_mul_c xhl yhl) (WW xhl w0) with
    | C0 m => (w0, sub (sub m hh) ll)
    | C1 m => (* carry = 1 *)
      match sub_c m hh with
      | C0 mhh =>
	match sub_c mhh ll with
        | C0 mhhll => (w1, mhhll)
        | C1 mhhll => (w0, mhhll)
        end
      | C1 mhh =>  (w0, sub mhh ll)
      end
    end
  | C1 xhl, C0 yhl => 
    match add_c (w_mul_c xhl yhl) (WW yhl w0) with
    | C0 m => (w0, sub (sub m hh) ll)
    | C1 m => (* carry = 1 *)
      match sub_c m hh with
      | C0 mhh =>
	match sub_c mhh ll with
        | C0 mhhll => (w1, mhhll)
        | C1 mhhll => (w0, mhhll)
        end
      | C1 mhh =>  (w0, sub mhh ll)
      end
    end
  | C1 xhl, C1 yhl => (* carry = 1 *)
    match w_add_c xhl yhl with
    | C0 suml =>      (* carry = 1 *)
      match add_c (w_mul_c xhl yhl) (WW suml w0) with
      | C0 m =>       (* carry = 1 *)
	match sub_c m hh with
	| C0 mhh =>
	  match sub_c mhh ll with
          | C0 mhhll => (w1, mhhll)
          | C1 mhhll => (w0, mhhll)
          end
        | C1 mhh =>  (w0, sub mhh ll)
        end
      | C1 m =>       (* carry = 2 *)  
	match sub_c m hh with
	| C0 mhh =>   (* carry = 2 => -ll a yn carry de 1 *)
          (w1,sub mhh ll)
        | C1 mhh =>  (* carry = 1 *)
          match sub_c mhh ll with
          | C0 mhhll => (w1, mhhll)
          | C1 mhhll => (w0, mhhll)
          end
        end
      end
    | C1 suml =>      (* carry = 2 *)
      match add_c (w_mul_c xhl yhl) (WW suml w0) with
      | C0 m =>       (* carry = 2 *) 
	match sub_c m hh with
	| C0 mhh =>  (* carry = 2 => -ll a yn carry de 1 *)
	  (w1,  sub mhh ll)
        | C1 mhh => (* carry = 1 *)
          match sub_c mhh ll with
          | C0 mhhll => (w1, mhhll)
          | C1 mhhll => (w0, mhhll)
          end  
        end
      | C1 m =>       (* carry = 3 => les deux soutraction on une carry *)
        (w1, sub (sub m hh) ll)
      end
    end
  end.

 Let ww_karatsuba_c x y :=
  Eval lazy beta delta [kara_prod] in
  match x, y with
  | W0, _ => W0
  | _, W0 => W0
  | WW xh xl, WW yh yl =>
    let hh := w_mul_c xh yh in
    let ll := w_mul_c xl yl in
    let (wc,cc) := kara_prod (w_add_c xh xl) (w_add_c yh yl) hh ll in
    match cc with
    | W0 => WW (add hh (WW wc w0)) ll
    | WW cch ccl =>
      match add_c (WW ccl w0) ll with
      | C0 l => WW (add hh (WW wc cch)) l
      | C1 l => WW (add_carry hh (WW wc cch)) l
      end
    end
  end.
 
 Let ww_mul x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0  
  | WW xh xl, WW yh yl => 
    let ccl := w_add (w_mul xh yl) (w_mul xl yh) in
    add (WW ccl w0) (w_mul_c xl yl)
  end.

 (*   (xh*B+xl) (yh*B + yl)
   xh*yh         = hh  = |hhh|hhl|B2
   xh*yl +xl*yh  = cc  =     |cch|ccl|B
   xl*yl         = ll  =         |llh|lll 
 *)

 Let ww_square_c x  :=
  match x with
  | W0 => W0
  | WW xh xl =>
    let hh := w_square_c xh in
    let ll := w_square_c xl in
    let xhxl := w_mul_c xh xl in
    let (wc,cc) :=
      match add_c xhxl xhxl with
      | C0 cc => (w0, cc)
      | C1 cc => (w1, cc)
      end in
    match cc with
    | W0 => WW (add hh (WW wc w0)) ll
    | WW cch ccl =>
      match add_c (WW ccl w0) ll with
      | C0 l => WW (add hh (WW wc cch)) l
      | C1 l => WW (add_carry hh (WW wc cch)) l
      end
    end
  end.


 (* Division operation *)

 Let div32 a1 a2 a3 b1 b2 :=
  match w_compare a1 b1 with
  | Lt =>
    let (q,r) := w_div21 a1 a2 b1 in
    match sub_c (wWW r a3) (w_mul_c q b2) with 
    | C0 r1 => (q,r1)
    | C1 r1 =>
      let b := WW b1 b2 in
      let q := w_pred q in
      match add_c r1 b with
      | C0 r2 => (w_pred q, add r2 b)
      | C1 r2 => (q, r2)
      end
    end
  | Eq =>
    let b := WW b1 b2 in
    match add_c (WW (w_sub a2 b2) a3) b with
    | C0 r => (wBm2, add r b)
    | C1 r => (wBm1,r)
    end
  | Gt => (w0, W0) (* cas absurde *)
  end.

 Let split x :=
  match x with
  | W0 => (w0,w0)
  | WW h l => (h, l)
  end.

 Let div21:=
  fun a b c =>
   match a with
   | W0 =>  
     match b with
     | W0 => (W0, W0)
     | _  =>
       match compare b c with
       | Gt => (ww_1, sub b c)
       | Eq => (ww_1, W0)
       | Lt => (W0, b)
       end
     end
   | WW a1 a2 =>
     let (a3, a4) := split b in
     let (b1, b2) := split c in
     let (q1, r) :=  div32 a1 a2 a3 b1 b2 in
     let (r1, r2) := split r in
     let (q2, s) := div32 r1 r2 a4 b1 b2 in
     (wWW q1 q2, s)
  end.

 (* 0 < p < ww_digits *)
 Let add_mul_div p x y := 
  match x, y with
  | W0, W0 => W0
  | W0, WW yh yl =>
    match Pcompare p w_digits Eq with
    | Eq => wWW w0 yh 
    | Lt => wWW w0 (w_add_mul_div p w0 yh)
    | Gt =>
      let n := Pminus p w_digits in
      wWW (w_add_mul_div n w0 yh) (w_add_mul_div n yh yl)
    end
  | WW xh xl, W0 =>
   match Pcompare p w_digits Eq with
    | Eq => wWW xl w0 
    | Lt => wWW (w_add_mul_div p xh xl) (w_add_mul_div p xl w0)
    | Gt =>
      let n := Pminus p w_digits in
      wWW (w_add_mul_div n xl w0) w0
    end
  | WW xh xl, WW yh yl =>
    match Pcompare p w_digits Eq with
    | Eq => wWW xl yh 
    | Lt => wWW (w_add_mul_div p xh xl) (w_add_mul_div p xl yh)
    | Gt =>
      let n := Pminus p w_digits in
      wWW (w_add_mul_div n xl yh) (w_add_mul_div n yh yl)
    end
  end.

 (* 0 < p < ww_digits *)
 Definition pos_mod p x := 
  match x with
  | W0 => W0
  | WW xh xl =>
    match Pcompare p w_digits Eq with
    | Eq => wWW w0 xl 
    | Lt => wWW w0 (w_pos_mod p xl)
    | Gt =>
      let n := Pminus p w_digits in
      wWW (w_pos_mod n xh) xl
    end
  end.


 Let _gen_divn1 := 
    gen_divn1 ww_digits W0 ww_WW head0 add_mul_div div21.

 Let ww_divn1 n (a:word_tr (zn2z w) n) (b:zn2z w):= 
   let (b1,b2) := split b in
   match w_compare b1 w0 with
   | Eq => let (q,r) := w_divn1 (S n) a b2 in 
    (match zn2z_word_comm w n in (_ = y) return y with
     | refl_equal => q 
     end, wWW w0 r)
   | _ => 
     _gen_divn1 n 
      (match word_tr_word (zn2z w) n in (_ = y) return y with
      | refl_equal => a
      end) b
   end.
 
 Definition ww_div_gt_aux a b bh bl :=
  let nb0 := w_head0 bh in
    match nb0 with
    | N0 => (ww_1, sub a b)
    | Npos p => 
      let (ah,al) := split a in
      let b1 := w_add_mul_div p bh bl in
      let b2 := w_add_mul_div p bl w0 in
      let a1 := w_add_mul_div p w0 ah in
      let a2 := w_add_mul_div p ah al in
      let a3 := w_add_mul_div p al w0 in
      let (q,r) := div32 a1 a2 a3 b1 b2 in
      (wWW w0 q, add_mul_div (Pminus ww_digits p) W0 r)
    end.

 Let ww_div_gt a b :=
  Eval lazy beta delta [ww_div_gt_aux] in
  let (bh,bl) := split b in
  match w_compare w0 bh with
  | Eq =>
    let (ah,al) := split a in
    match w_compare w0 ah with
    | Eq => let (q,r) := w_div_gt al bl in (wWW w0 q, wWW w0 r)
    | _ => let (q,r) := w_divn1 1 a bl in (q, wWW w0 r)
    end
  | _ => ww_div_gt_aux a b bh bl
  end.

 Let ww_div a b :=
  match compare a b with 
  | Gt => ww_div_gt a b 
  | Eq => (ww_1, W0)
  | Lt => (W0, a)
  end.
 
 Let _gen_modn1 := 
    gen_modn1 ww_digits W0 head0 add_mul_div div21.

 Let ww_modn1 n (a:word_tr (zn2z w) n) (b:zn2z w):= 
   let (b1,b2) := split b in
   match w_compare b1 w0 with
   | Eq => wWW w0 (w_modn1 (S n) a b2)
   | _ => 
     _gen_modn1 n 
      (match word_tr_word (zn2z w) n in (_ = y) return y with
      | refl_equal => a
      end) b
   end.
 
 Definition ww_mod_gt_aux a ah al b bh bl := 
  let nb0 := w_head0 bh in
  match nb0 with
  | N0 => sub a b
  | Npos p => 
    let b1 := w_add_mul_div p bh bl in
    let b2 := w_add_mul_div p bl w0 in
    let a1 := w_add_mul_div p w0 ah in
    let a2 := w_add_mul_div p ah al in
    let a3 := w_add_mul_div p al w0 in
    let (q,r) := div32 a1 a2 a3 b1 b2 in
    add_mul_div (Pminus ww_digits p) W0 r
  end.

 Definition ww_mod_gt a b :=
  Eval lazy beta delta [ww_mod_gt_aux] in
  let (bh,bl) := split b in
  let (ah,al) := split a in	
  match w_compare w0 bh with
  | Eq =>
    match w_compare w0 ah with
    | Eq => wWW w0 (w_mod_gt al bl)
    | _ => wWW w0 (w_modn1 1 a bl)
    end
  | _ => ww_mod_gt_aux a ah al b bh bl
  end.
 
 Let ww_mod a b :=
  Eval lazy beta delta [ww_mod_gt] in
  match compare a b with 
  | Gt => ww_mod_gt a b 
  | Eq => W0
  | Lt => a
  end.

 Fixpoint ww_gcd_gt_aux 
  (p:positive) (cont: zn2z w -> zn2z w -> zn2z w) (a b : zn2z w) 
        {struct p} : zn2z w :=
  let (bh,bl) := split b in
  match w_compare w0 bh with
  | Eq =>
    match w_compare w0 bl with
    | Eq => a
    | _  => WW w0 (w_gcd_gt bl (w_modn1 1 a bl))
    end
  | _ =>
    let (ah,al) := split a in
    let m := ww_mod_gt_aux a ah al b bh bl in
    let (mh,ml) := split m in
    match w_compare w0 mh with
    | Eq =>
      match w_compare w0 ml with
      | Eq => b
      | _  => WW w0 (w_gcd_gt ml (w_modn1 1 b ml))
      end
    | _ =>
      let r := ww_mod_gt_aux b bh bl m mh ml in
      match p with
      | xH => cont m r 
      | xO p => ww_gcd_gt_aux p (ww_gcd_gt_aux p cont) m r 
      | xI p => ww_gcd_gt_aux p (ww_gcd_gt_aux p cont) m r
      end
    end
  end. 

 Let _ww_gcd_gt_aux := 
  Eval cbv beta delta[ww_gcd_gt_aux ww_mod_gt_aux] in ww_gcd_gt_aux.

 Let ww_gcd_gt a b := 
  let (ah,al) := split a in
  match w_compare w0 ah with
  | Eq => let (bh,bl) := split b in WW w0 (w_gcd_gt al bl)
  | _  => _ww_gcd_gt_aux ww_digits 
    (fun x y => match compare ww_1 y with
                | Eq => ww_1 
                | _ => x
                end) a b
  end.

 Definition ww_gcd a b :=
  Eval lazy beta delta [ww_gcd_gt] in 
  match compare a b with
  | Gt => ww_gcd_gt a b
  | Eq => a
  | Lt => ww_gcd_gt b a
  end.

 (* ** Record of operators on 2 words *)
   
 Definition mk_zn2z_op := 
  mk_znz_op ww_digits
    ww_to_Z ww_of_pos head0
    W0 ww_1 ww_Bm1
    ww_WW ww_CW 
    compare
    ww_opp_c ww_opp ww_opp_carry
    ww_succ_c add_c add_carry_c 
    ww_succ add add_carry 
    ww_pred_c sub_c ww_sub_carry_c 
    ww_pred sub ww_sub_carry
    ww_mul_c ww_mul ww_square_c   
    div21 ww_divn1 ww_div_gt ww_div
    ww_modn1 ww_mod_gt ww_mod
    ww_gcd_gt ww_gcd
    add_mul_div
    pos_mod.

 Definition mk_zn2z_op_karatsuba := 
  mk_znz_op ww_digits
    ww_to_Z ww_of_pos head0
    W0 ww_1 ww_Bm1
    ww_WW ww_CW 
    compare
    ww_opp_c ww_opp ww_opp_carry
    ww_succ_c add_c add_carry_c 
    ww_succ add add_carry 
    ww_pred_c sub_c ww_sub_carry_c 
    ww_pred sub ww_sub_carry
    ww_karatsuba_c ww_mul ww_square_c   
    div21 ww_divn1 ww_div_gt ww_div
    ww_modn1 ww_mod_gt ww_mod
    ww_gcd_gt ww_gcd
    add_mul_div
    pos_mod.

End Zn2Z. 
 
