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

