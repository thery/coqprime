Set Implicit Arguments.

Require Import ZArith.

Open Local Scope Z_scope.

Section Carry.

 Variable A : Set.

 Inductive carry : Set :=
  | C0 : A -> carry
  | C1 : A -> carry.

 Definition without_c c :=
  match c with
  | C0 a => a
  | C1 a => a
  end.

End Carry.

Section Data.

 Variable znz : Set.

 Inductive zn2z : Set :=
  | W0 : zn2z
  | WW : znz -> znz -> zn2z.

  Definition zn2z_to_Z (wB:Z) (w_to_Z:znz->Z) (x:zn2z) :=
  match x with
  | W0 => 0
  | WW xh xl => wB * w_to_Z xh + w_to_Z xl
  end.

 Definition base digits := Zpower 2 (Zpos digits).

 Definition interp_carry sign B (interp:znz -> Z) c :=
  match c with
  | C0 x => interp x
  | C1 x => sign*B + interp x
  end.

 Record znz_op : Set := mk_znz_op {
    (* Conversion functions with Z *)
    znz_digits : positive;
    znz_to_Z   : znz -> Z;
    znz_of_pos : positive -> N * znz;
    znz_head0  : znz -> N;
    (* Basic constructors *)
    znz_0   : znz;
    znz_1   : znz;
    znz_Bm1 : znz;
    znz_WW  : znz -> znz -> zn2z;
    znz_CW  : carry znz -> znz -> carry zn2z;
    
    (* Comparison *)
    znz_compare     : znz -> znz -> comparison;
 
    (* Basic arithmetic operations *)
    znz_opp_c       : znz -> carry znz;
    znz_opp_carry   : znz -> znz; (* the carry is know to be -1 *)

    znz_succ_c      : znz -> carry znz;
    znz_add_c       : znz -> znz -> carry znz;
    znz_add_carry_c : znz -> znz -> carry znz;
    znz_add         : znz -> znz -> znz;

    znz_pred_c      : znz -> carry znz;
    znz_sub_c       : znz -> znz -> carry znz;
    znz_sub_carry_c : znz -> znz -> carry znz;
    znz_sub         : znz -> znz -> znz;
  
    znz_mul_c       : znz -> znz -> zn2z;
    znz_mul         : znz -> znz -> znz;
    znz_square_c    : znz -> zn2z;

    (* Special divisions operations *)
    znz_div21       : znz -> znz -> znz -> (carry znz)*znz;
    znz_add_mul_div : znz -> znz -> positive -> znz   
				    
  }.

 Inductive z2nz : Set :=
  | Wpos : znz -> z2nz
  | Wneg : znz -> z2nz.

 Record signed_z2nz_op : Set := mk_signed_op {
    z2nz_B : Z;
    z2nz_to_Z : z2nz -> Z;
    z2nz_of_Z : Z -> z2nz;
    z2nz_0 : z2nz;
    z2nz_1 : z2nz;
    z2nz_opp : z2nz -> z2nz;
    z2nz_succ : z2nz -> z2nz;
    z2nz_add : z2nz -> z2nz -> z2nz;
    z2nz_pred : z2nz -> z2nz;
    z2nz_sub : z2nz -> z2nz -> z2nz
  }.

End Data.

Implicit Arguments W0 [znz].

Section W.

 Variable w : Set.

 Fixpoint word (s:nat) : Set :=
  match s with
  | O => w
  | S s' => zn2z (word s')
  end.

End W.

Section Spec.
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

 Let w_square_c       := w_op.(znz_square_c).
 
 Let w_div21       := w_op.(znz_div21).
 Let w_add_mul_div := w_op.(znz_add_mul_div).

 Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).

 Let wB := base w_digits.

 Notation "[+| c |]" :=
   (interp_carry 1 wB w_to_Z c)  (at level 0, x at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wB w_to_Z c)  (at level 0, x at level 99).

 Notation "[|| x ||]" :=
   (zn2z_to_Z wB w_to_Z x)  (at level 0, x at level 99).
 
Record znz_spec : Set := mk_znz_spec {
    (* Conversion functions with Z *)
    spec_to_Z   : forall x, 0 <= [| x |] < base w_digits;
    spec_of_pos : forall p,
           Zpos p = (Z_of_N (fst (w_of_pos p)))*wB + [|(snd (w_of_pos p))|];
(*    spec_head0  : ; *)
    (* Basic constructors *)
    spec_0   : [|w0|] = 0;
    spec_1   : [|w1|] = 1;
    spec_Bm1 : [|wBm1|] = wB - 1;
    spec_WW  : forall h l, [||wWW h l||] = [|h|] * wB + [|l|];
    spec_CW  :
     forall sign c l,
       interp_carry sign (wB*wB) (zn2z_to_Z wB w_to_Z) (wCW c l) =
       (interp_carry sign wB w_to_Z c)*wB + [|l|];

    (* Comparison *)
    spec_compare :
     forall x y,
       match w_compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end;

    (* Basic arithmetic operations *)
    spec_opp_c : forall x, [-|w_opp_c x|] = -[|x|];
    spec_opp_carry : forall x, [|w_opp_carry x|] = wB - [|x|] - 1;

    spec_succ_c : forall x, [+|w_succ_c x|] = [|x|] + 1;
    spec_add_c  : forall x y, [+|w_add_c x y|] = [|x|] + [|y|];
    spec_add_carry_c : forall x y, [+|w_add_carry_c x y|] = [|x|] + [|y|] + 1;
    spec_add : forall x y, [|w_add x y|] = ([|x|] + [|y|]) mod wB;

    spec_pred_c : forall x, [-|w_pred_c x|] = [|x|] - 1;
    spec_sub_c : forall x y, [-|w_sub_c x y|] = [|x|] - [|y|];
    spec_sub_carry_c : forall x y, [-|w_sub_carry_c x y|] = [|x|] - [|y|] - 1;
    spec_sub : forall x y, [|w_sub x y|] = ([|x|] - [|y|]) mod wB;

    spec_mul_c : forall x y, [|| w_mul_c x y ||] = [|x|] * [|y|];
    spec_mul : forall x y, [|w_mul x y|] = ([|x|] * [|y|]) mod wB;

   spec_square_c : forall x, [|| w_square_c x||] = [|x|] * [|x|];

    (* Special divisions operations *)
    spec_div21 : forall a1 a2 b,
     let (q,r) := w_div21 a1 a2 b in
     wB/2 <= [|b|] ->
     [|a1|] *wB+ [|a2|] = [+|q|] *  [|b|] + [|r|] /\ 0 <= [|r|] < [|b|];
    spec_add_mul_div : forall x y p,
       0 < Zpos p < Zpos w_digits ->
       [| w_add_mul_div x y p|] =
         ([|x|] * (Zpower 2 (Zpos p)) +
          [|y|] / (Zpower 2 ((Zpos w_digits) - (Zpos p)))) mod wB
  }.

End Spec.
