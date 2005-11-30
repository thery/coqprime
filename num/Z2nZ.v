Unset Boxed Definitions.

Require Import ZArith.
Require Import ZnZ.

Open Local Scope Z_scope.


Section Signed_Z2nZ.
  
 Variable znz : Set.
 Variable znz_op : znz_op znz.

 Let wB := znz_op.(znz_B).
 Let w_to_Z := znz_op.(znz_to_Z).
 Let w_of_pos := znz_op.(znz_of_pos).

 Let w0 := znz_op.(znz_0).
 Let w1 := znz_op.(znz_1).
 Let wBm1 := znz_op.(znz_Bm1).

 Let wWW := znz_op.(znz_WW).
 Let wCW := znz_op.(znz_CW).

 Let w_opp := znz_op.(znz_opp).
 Let w_opp_carry := znz_op.(znz_opp_carry).

 Let w_succ_c := znz_op.(znz_succ_c).
 Let w_add_c := znz_op.(znz_add_c).
 Let w_add_carry_c := znz_op.(znz_add_carry_c).

 Let w_pred_c := znz_op.(znz_pred_c).
 Let w_sub_c := znz_op.(znz_sub_c).
 Let w_sub_carry_c := znz_op.(znz_sub_carry_c).

 Let w_mul_c := znz_op.(znz_mul_c).

 Let sz2nz_B := 2 *wB.

 Let sz2nz_to_Z x :=
  match x with
  | Wpos w => w_to_Z w
  | Wneg w => w_to_Z w - wB
  end.

 Let sz2nz_of_Z z := 
  match z with
  | Z0 => Wpos w0
  | Zpos p => Wpos (snd (w_of_pos p))
  | Zneg p => Wneg (w_opp (snd (w_of_pos p)))
  end.
 
 Let sz2nz_0 := Wpos w0.
 Let sz2nz_1 := Wpos w1.

 Let sz2nz_opp x :=
  match x with
  | Wpos w => Wneg (w_opp w)
  | Wneg w => Wpos (w_opp w)
  end.

 Let carry_neg (c:carry znz) :=
  match c with
  | C0 w => Wpos w
  | C1 w => Wneg w
  end.
 
 Let carry_pos (c:carry znz) :=
  match c with
  | C0 w => Wneg w
  | C1 w => Wpos w
  end.

 Let sz2nz_succ x := 
  match x with
  | Wpos w => carry_neg (w_succ_c w)
  | Wneg w => carry_pos (w_succ_c w)
  end.

 Let sz2nz_add x y := 
  match x, y with
  | Wpos wx, Wpos wy => carry_neg (w_add_c wx wy)
  | Wneg wx, Wneg wy => carry_neg (w_add_c wx wy)
  | Wpos wx, Wneg wy => carry_pos (w_add_c wx wy)
  | Wneg wx, Wpos wy => carry_pos (w_add_c wx wy)
  end.

 Let sz2nz_pred x :=
  match x with
  | Wpos w => carry_neg (w_pred_c w)
  | Wneg w => carry_pos (w_pred_c w)
  end.

 Let sz2nz_sub x y := 
  match x, y with
  | Wpos wx, Wneg wy => carry_pos (w_sub_c wx wy)
  | Wneg wx, Wpos wy => carry_pos (w_sub_c wx wy)
  | Wpos wx, Wpos wy => carry_neg (w_sub_c wx wy)
  | Wneg wx, Wneg wy => carry_neg (w_sub_c wx wy)
  end.

 (*Let sz2nz_mul x y :=
  match x, y with
  | Wpos wx, Wneg wy => carry_pos (w_sub_c wx wy)
  | Wneg wx, Wpos wy => carry_pos (w_sub_c wx wy)
  | Wpos wx, Wpos wy =>
    let (h, l) := w_mul_c wx wy in
     
  | Wneg wx, Wneg wy => carry_neg (w_sub_c wx wy)
  end.
 *)

 Definition z2nz_op := 
   mk_signed_op 
    sz2nz_B 
    sz2nz_to_Z sz2nz_of_Z 
    sz2nz_0 sz2nz_1 
    sz2nz_opp 
    sz2nz_succ sz2nz_add 
    sz2nz_pred sz2nz_sub.

End Signed_Z2nZ.
