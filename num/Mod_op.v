(* 
Unset Boxed Definitions.
*)
Set Implicit Arguments.

Require Import ZArith.
Require Import ZnZ.
Require Import Zn2Z.

Section Mod_op.

 Variable w : Set.
 
 Record mod_op : Set := mk_mod_op {
   w0_mod    : w;
   w1_mod    : w;
   succ_mod  : w -> w;
   add_mod   : w -> w -> w;
   pred_mod  : w -> w;
   sub_mod   : w -> w -> w;
   mul_mod   : w -> w -> w;
   square_mod : w -> w;
   power_mod : w -> positive -> w
 }.
 
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
 Let w_opp_carry   := w_op.(znz_opp_carry).

 Let w_succ_c      := w_op.(znz_succ_c).
 Let w_add_c       := w_op.(znz_add_c).
 Let w_add_carry_c := w_op.(znz_add_carry_c).
 Let w_add         := w_op.(znz_add).

 Let w_pred_c      := w_op.(znz_pred_c).
 Let w_sub_c       := w_op.(znz_sub_c).
 Let w_sub_carry_c := w_op.(znz_sub_carry_c).
 Let w_sub         := w_op.(znz_sub).

 Let w_mul_c       := w_op.(znz_mul_c).
 Let w_mul         := w_op.(znz_mul).
 Let w_square_c    := w_op.(znz_square_c).

 Let w_div21       := w_op.(znz_div21).
 Let w_add_mul_div := w_op.(znz_add_mul_div).

 Variable b : w.
    (* b should be > 1 *)
 Let n := w_head0 b.

 Let b2n := 
   match n with
   | N0 => b
   | Npos p => w_add_mul_div b w0 p 
   end.

 Let bm1 := w_sub b w1.

 Let mb := without_c (w_opp_c b).

 Let wwb := WW w0 b.

 Let ww_lsl_n :=
   match n with 
   | N0 => fun ww => ww
   | Npos p => 
     let add_mul_div := ww_add_mul_div w_op in 
     fun ww => add_mul_div ww W0 p
   end.

 Let w_lsr_n :=
   match n with
   | N0 => fun w => w
   | Npos p =>
     let k := Pminus w_digits p in
     fun w => w_add_mul_div w0 w k
   end.

 Let _w0_mod := w0.

 Let _w1_mod := w1.

 Let _succ_mod x :=
  match w_compare x bm1 with 
  | Lt => without_c (w_succ_c x)
  | _ => w0
  end.

 Let split := ww_split w_op.

 Let _add_mod x y :=
  match w_add_c x y with
  | C0 z =>
    match w_compare z b with
    | Lt => z
    | Eq => w0
    | Gt => w_sub z b
    end
  | C1 z => w_add mb z
  end.

 Let _pred_mod x :=
  match w_compare w0 x with
  | Eq => bm1
  | _ => without_c (w_pred_c x)
  end.

 Let _sub_mod x y :=
  match w_sub_c x y with
  | C0 z => z
  | C1 z => w_add z b
  end.

 Let _mul_mod x y :=
  let xy := w_mul_c x y in
  match ww_compare w_op xy wwb with
  | Lt => snd (split xy)
  | Eq => w0
  | Gt => 
    let xy2n := ww_lsl_n xy in
    let (h,l) := split xy2n in
    let (q,r) := w_div21 h l b2n in
    w_lsr_n r 
  end.

 Let _square_mod x :=
  let x2 := w_square_c x in
  match _ww_compare x2 wwb with
  | Lt => snd (split x2)
  | Eq => w0
  | Gt =>
    let x2_2n := ww_lsl_n x2 in
    let (h,l) := split x2_2n in
    let (q,r) := w_div21 h l b2n in
    w_lsr_n r
  end.

  Let _power_mod :=
   fix pow_mod (x:w) (p:positive) {struct p} : w :=
     match p with
     | xH => x
     | xO p' =>
       let pow := pow_mod x p' in
       _square_mod pow
     | xI p' =>
       let pow := pow_mod x p' in
       _mul_mod (_square_mod pow) x
     end.

 Definition make_mod_op := 
   mk_mod_op
     _w0_mod _w1_mod 
     _succ_mod _add_mod 
     _pred_mod _sub_mod
     _mul_mod _square_mod _power_mod.

End Mod_op.
    
