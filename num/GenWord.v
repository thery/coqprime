
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import GenBase.
Require Import GenAdd.
Require Import GenSub.
Require Import GenMul.
Require Import GenLift.
Require Import GenDivn1.
Require Import GenDiv. 
Require Import ZnZ.
Require Import Zn2Z.

Open Local Scope Z_scope.

Module Type Uint.
 Parameter uint : Set.

 Parameter digits : positive.

 Parameter zero one Bm1 : uint.  

 Parameter opp : uint -> uint.
 Parameter add : uint -> uint -> uint.
 Parameter sub : uint -> uint -> uint.
 Parameter mul : uint -> uint -> uint.
 Parameter mul_c : uint -> uint -> uint * uint.
 Parameter square_c : uint -> uint * uint.

 Parameter div21 : uint -> uint -> uint -> uint * uint.

 Parameter div_eucl : uint -> uint -> uint * uint.
 Parameter uint_mod : uint -> uint -> uint.

 Parameter head0 : uint -> N.
 Parameter lsl : uint -> positive -> uint.
 Parameter lsr : uint -> positive -> uint.

 Parameter eqb ltb leb: uint -> uint -> bool.
 Parameter compare : uint -> uint -> comparison.

 Parameter to_Z : uint -> Z. 
 Notation "[| x |]" := (to_Z x) (at level 0, x at level 99).

 Parameter of_pos : positive -> N * uint.

 Notation wB := (base digits).

 Parameter O_to_Z : [|zero|] = 0.
 Parameter I_to_Z : [|one|] = 1.
 Parameter Bm1_to_Z : [|Bm1|] = wB - 1.

 Parameter to_Z_spec : forall x, 0 <= [|x|] < wB.

 Parameter of_pos_spec : forall p,
           Zpos p = (Z_of_N (fst (of_pos p)))*wB + [|(snd (of_pos p))|].

 Parameter compare_spec :
    forall x y,
       match compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end.

 Parameter eqb_spec : forall x y, 
   if eqb x y then [|x|] = [|y|] else [|x|] <> [|y|].
 Parameter ltb_spec : forall x y, 
  if ltb x y then [|x|] < [|y|] else [|y|] <= [|x|].

 Parameter leb_spec : forall x y, 
  if leb x y then [|x|] <= [|y|] else [|y|] < [|x|].
 
 Parameter opp_spec : forall x, [|opp x|] = (-[|x|]) mod wB.
 Parameter add_spec : forall x y, [|add x y|] = ([|x|] + [|y|]) mod wB.
 Parameter sub_spec : forall x y, [|sub x y|] = ([|x|] - [|y|]) mod wB.
  
 Parameter mul_c_spec : forall x y, 
  let (h,l) := mul_c x y in
  [|h|]*wB+[|l|] = [|x|] * [|y|].

 Parameter mul_spec : forall x y, [|mul x y|] = ([|x|] * [|y|]) mod wB.
 Parameter square_c_spec : forall x, 
   let (h,l) := square_c x in [|h|]*wB+[|l|] = [|x|] * [|x|].

 Parameter div21_spec : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := div21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].

 Parameter div_eucl_spec : forall a b, 0 < [|b|] ->
      let (q,r) := div_eucl a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
   
 Parameter mod_spec :  forall a b, 0 < [|b|] ->
  [|uint_mod a b|] = [|a|] mod [|b|].
      
 Parameter head0_spec  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ (Z_of_N (head0 x)) * [|x|] < wB. 

 Parameter lsl_spec : forall x p, Zpos p < Zpos digits ->
	[|lsl x p|] = [|x|]*2^Zpos p.
 Parameter lsr_spec : forall x p, Zpos p < Zpos digits ->
        [|lsr x p|] = [|x|]/(2^Zpos p).
 
End Uint.

Module MakeUintZnZ (U:Uint).

 Definition uint_WW h l :=
  if U.eqb h U.zero then 
   if U.eqb l U.zero then W0
   else WW h l
  else WW h l.

 Definition uint_W0 h := 
  if U.eqb h U.zero then W0
  else WW h U.zero. 

 Definition uint_0W l :=
  if U.eqb l U.zero then W0
  else WW U.zero l.
	
 Definition uint_opp_c x :=
  if U.eqb x U.zero then C0 U.zero
  else C1 (U.opp x).

 Definition uint_opp_carry x := U.sub (U.opp x) U.one.

 Definition uint_succ_c x := 
  if U.eqb x U.Bm1 then C1 U.zero
  else C0 (U.add x U.one).

 Definition uint_add_c x y :=
  let r := U.add x y in
  if U.ltb r x then C1 r else C0 r.

 Definition uint_add_carry_c x y :=
  let r := U.add (U.add x y) U.one in
  if U.leb r x then C1 r else C0 r.	

 Definition uint_succ x := U.add x U.one.

 Definition uint_add_carry x y := U.add (U.add x y) U.one.

 Definition uint_pred_c x :=
  if U.eqb x U.zero then C1 U.Bm1 else C0 (U.sub x U.one).

 Definition uint_sub_c x y :=
  let r := U.sub x y in
  if U.ltb x r then C1 r else C0 r.

 Definition uint_sub_carry_c x y :=
  let r := U.sub (U.sub x y) U.one in
  if U.leb x r then C1 r else C0 r.

 Definition uint_pred x := U.sub x U.one.
 
 Definition uint_sub_carry x y := U.sub (U.sub x y) U.one.

 Definition uint_mul_c x y := 
  let (h,l) := U.mul_c x y in
  uint_WW h l.

 Definition uint_square_c x :=
  if U.eqb x U.zero then W0
  else let (h,l) := U.square_c x in WW h l.

 Definition uint_gcd_gt_body (cont : U.uint -> U.uint -> U.uint) a b :=
  if U.eqb b U.zero then a
  else	
   let m := U.uint_mod a b in
   if U.eqb m U.zero then b
   else	cont m (U.uint_mod b m).

 Fixpoint uint_gcd_gt_aux (n:nat) : U.uint -> U.uint -> U.uint :=
  let cont := 
   match n with 
   | O => fun x y => if U.eqb y U.one then U.one else x
   | S n => uint_gcd_gt_aux n
   end in
  uint_gcd_gt_body cont.

 Definition uint_gcd_gt := uint_gcd_gt_aux (nat_of_P U.digits).

 Definition uint_gcd a b := 
  match U.compare a b with
  | Eq => a
  | Lt => uint_gcd_gt b a
  | Gt => uint_gcd_gt a b
  end.

 Definition uint_add_mul_div p x y :=
   U.add (U.lsl x p) (U.lsr y (Pminus U.digits p)).
  
 Definition uint_op := 
  mk_znz_op
   U.digits U.to_Z U.of_pos U.head0
   U.zero U.one U.Bm1 uint_WW uint_W0 uint_0W
   U.compare (U.eqb U.zero) uint_opp_c U.opp uint_opp_carry
   uint_succ_c uint_add_c uint_add_carry_c 
   uint_succ U.add uint_add_carry
   uint_pred_c uint_sub_c uint_sub_carry_c 
   uint_pred U.sub uint_sub_carry
   uint_mul_c U.mul uint_square_c
   U.div21 U.div_eucl U.div_eucl
   U.uint_mod U.uint_mod  
   uint_gcd_gt uint_gcd
   uint_add_mul_div.

 Notation "[| x |]" := (U.to_Z x) (at level 0, x at level 99).
 Notation wB := (base U.digits).

 Notation "[+| c |]" :=
   (interp_carry 1 U.wB U.to_Z c)  (at level 0, x at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) U.wB U.to_Z c)  (at level 0, x at level 99).

 Notation "[[ x ]]" := (zn2z_to_Z U.wB U.to_Z x)  (at level 0, x at level 99).

 Lemma WW_spec  : forall h l, [[ uint_WW h l ]] = [|h|] * wB + [|l|].
 Proof.
  unfold uint_WW;intros h l.
  generalize (U.eqb_spec h U.zero);rewrite U.O_to_Z;
  destruct (U.eqb h U.zero);intros. rewrite H;simpl.
  generalize (U.eqb_spec l U.zero);rewrite U.O_to_Z;
  destruct (U.eqb l U.zero);intros. rewrite H0;trivial.
  simpl;rewrite H;trivial.  trivial.
 Qed.

 Lemma OW_spec  : forall l, [[uint_0W l]] = [|l|].
 Proof.
  unfold uint_0W;intros l.
  generalize (U.eqb_spec l U.zero);rewrite U.O_to_Z;
  destruct (U.eqb l U.zero);intros. rewrite H;trivial.
  simpl;rewrite U.O_to_Z;trivial.
 Qed.

 Lemma W0_spec : forall h, [[uint_W0 h]] = [|h|]*wB.
 Proof.
  unfold uint_W0;intros h.
  generalize (U.eqb_spec h U.zero);rewrite U.O_to_Z;
  destruct (U.eqb h U.zero);intros. rewrite H;simpl;trivial. 
  simpl;rewrite U.O_to_Z;ring.
 Qed.

 Lemma eq0_spec : forall x, U.eqb U.zero x = true -> [|x|] = 0.
 Proof.
  intros x;generalize (U.eqb_spec U.zero x); rewrite U.O_to_Z.
  destruct (U.eqb U.zero x);auto. intros H H0;discriminate H0.
 Qed.

 Lemma uint_opp_c_spec : forall x, [-|uint_opp_c x|] = -[|x|].
 Proof.
  unfold uint_opp_c;intros x.
  generalize (U.eqb_spec x U.zero);rewrite U.O_to_Z;destruct(U.eqb x U.zero);
  intros. rewrite H;simpl;rewrite U.O_to_Z;trivial.
  unfold interp_carry. replace (-1*wB) with (-wB). 2:ring.
  rewrite U.opp_spec. assert (H0:= U.to_Z_spec x).
  rewrite <- Zmod_unique with(q := -1)(r:= wB-[|x|]);auto with zarith.
 Qed.

 Lemma uint_opp_carry_spec : forall x, [|uint_opp_carry x|] = wB - [|x|] - 1.
 Proof.
  intros x;unfold uint_opp_carry.
  rewrite U.sub_spec;rewrite U.I_to_Z;rewrite U.opp_spec.
  generalize (U.eqb_spec x U.zero);rewrite U.O_to_Z;destruct(U.eqb x U.zero);
  intros. rewrite H. simpl. assert (H0:= U.to_Z_spec x).
  rewrite <- Zmod_unique with(q := -1) (r:= wB-1);auto with zarith.
  assert (H0:= U.to_Z_spec x).
  rewrite <- (Zmod_unique (-[|x|]) wB (-1)(wB-[|x|]));auto with zarith.
  rewrite Zmod_def_small;auto with zarith.
 Qed.

 Lemma uint_succ_c_spec :  forall x, [+|uint_succ_c x|] = [|x|] + 1.
 Proof.
  intros x;unfold uint_succ_c.
  generalize (U.eqb_spec x U.Bm1);rewrite U.Bm1_to_Z;destruct (U.eqb x U.Bm1);
  intros. unfold interp_carry;rewrite H;rewrite U.O_to_Z;ring.
  simpl;rewrite U.add_spec;assert (H0 := U.to_Z_spec x);rewrite U.I_to_Z.
  rewrite Zmod_def_small;auto with zarith.
 Qed.

 Lemma uint_add_c_spec : forall x y, [+|uint_add_c x y|] = [|x|] + [|y|].
 Proof.
  intros x y;unfold uint_add_c.
  assert (Hx:= U.to_Z_spec x);assert (Hy:= U.to_Z_spec y).
  generalize (@U.ltb_spec (U.add x y) x);destruct (U.ltb (U.add x y) x);intros;
  unfold interp_carry;rewrite U.add_spec in H;rewrite U.add_spec.
  rewrite <- Zmod_unique with (q:= 1) (r:= ([|x|]+[|y|])-wB);auto with zarith.
  split;auto with zarith.
  destruct (Z_le_gt_dec 0 ([|x|] + [|y|] - wB)). trivial.
  rewrite Zmod_def_small in H;auto with zarith.
  rewrite Zmod_def_small;trivial.
  split;auto with zarith.
  destruct (Z_le_gt_dec wB ([|x|] + [|y|])); auto with zarith.
  rewrite <- Zmod_unique with (q:=1)(r:= ([|x|] + [|y|]) -wB) in H;auto
   with zarith.
 Qed.

 Lemma uint_add_carry_c_spec : forall x y, 
  [+|uint_add_carry_c x y|] = [|x|] + [|y|] + 1.
 Proof.
  unfold uint_add_carry_c; intros x y.
  assert (Hx:= U.to_Z_spec x);assert (Hy:= U.to_Z_spec y).
  generalize (@U.leb_spec (U.add (U.add x y) U.one) x);
  destruct (U.leb (U.add (U.add x y) U.one) x);unfold interp_carry;
  repeat rewrite U.add_spec;try rewrite U.I_to_Z;intros.
  destruct (Z_le_gt_dec wB ([|x|] + [|y|])).
  assert (([|x|] + [|y|]) mod wB = ([|x|] + [|y|]) - wB).
   rewrite <- Zmod_unique with (q:= 1) (r:=[|x|]+[|y|]-wB);auto with zarith.
  rewrite H0;rewrite H0 in H.
  destruct (Z_le_gt_dec wB ([|x|] + [|y|] -wB + 1)).
  assert (([|x|] + [|y|] - wB + 1) mod wB = ([|x|] + [|y|] -wB +1) - wB).
   rewrite <- Zmod_unique with(q:= 1)(r:=[|x|]+[|y|]-wB+1-wB);auto with zarith.
  rewrite H1;rewrite H1 in H. auto with zarith.
  rewrite Zmod_def_small;auto with zarith.
  rewrite (Zmod_def_small([|x|] + [|y|]));auto with zarith.
  destruct (Z_le_gt_dec wB ([|x|] + [|y|] + 1)).
  assert (([|x|] + [|y|] + 1) mod wB = ([|x|] + [|y|] +1) - wB).
   rewrite <- Zmod_unique with(q:= 1)(r:=[|x|]+[|y|]+1-wB);auto with zarith.
  rewrite H0;auto with zarith.
  rewrite (Zmod_def_small ([|x|] + [|y|])) in H ;auto with zarith.
  rewrite (Zmod_def_small ([|x|] + [|y|]+1)) in H ;auto with zarith.

  destruct (Z_le_gt_dec wB ([|x|] + [|y|])).
  assert (([|x|] + [|y|]) mod wB = ([|x|] + [|y|]) - wB).
   rewrite <- Zmod_unique with (q:= 1) (r:=[|x|]+[|y|]-wB);auto with zarith.
  rewrite H0;rewrite H0 in H.
  destruct (Z_le_gt_dec wB ([|x|] + [|y|] -wB + 1)).
  assert (([|x|] + [|y|] - wB + 1) mod wB = ([|x|] + [|y|] -wB +1) - wB).
   rewrite <- Zmod_unique with(q:= 1)(r:=[|x|]+[|y|]-wB+1-wB);auto with zarith.
  rewrite H1;rewrite H1 in H. auto with zarith.
  rewrite Zmod_def_small in H;auto with zarith.
  rewrite (Zmod_def_small ([|x|] + [|y|])) in H ;auto with zarith.
  rewrite (Zmod_def_small ([|x|] + [|y|]));auto with zarith.
  destruct (Z_le_gt_dec wB ([|x|] + [|y|] + 1)).
  assert (([|x|] + [|y|] + 1) mod wB = ([|x|] + [|y|] +1) - wB).
   rewrite <- Zmod_unique with(q:= 1)(r:=[|x|]+[|y|]+1-wB);auto with zarith.
  rewrite H0 in H;auto with zarith.
  rewrite (Zmod_def_small ([|x|] + [|y|]+1));auto with zarith.
 Qed.

 Lemma uint_succ_spec : forall x, [|uint_succ x|] = ([|x|] + 1) mod wB.
 Proof. 
  intros;unfold uint_succ;rewrite U.add_spec;rewrite U.I_to_Z;trivial. 
 Qed.

 Lemma uint_add_carry_spec :
	 forall x y, [|uint_add_carry x y|] = ([|x|] + [|y|] + 1) mod wB.
 Proof.
  intros x y;unfold uint_add_carry;repeat rewrite U.add_spec.
  assert (HH:=wB_pos U.digits).
  rewrite U.I_to_Z;rewrite (Zmod_plus ([|x|] + [|y|]));auto with zarith.
  rewrite (Zmod_def_small 1);auto with zarith.
 Qed.

 Lemma uint_pred_c_spec : forall x, [-|uint_pred_c x|] = [|x|] - 1.
 Proof.
  intros x;unfold uint_pred_c. assert (H:=U.to_Z_spec x).
  generalize (U.eqb_spec x U.zero);rewrite U.O_to_Z;destruct (U.eqb x U.zero);
  intros;unfold interp_carry. rewrite H0;rewrite U.Bm1_to_Z;ring.
  rewrite U.sub_spec;rewrite U.I_to_Z;rewrite Zmod_def_small;auto with zarith.
 Qed.

 Lemma uint_sub_c_spec : forall x y, [-|uint_sub_c x y|] = [|x|] - [|y|].
 Proof.
  unfold uint_sub_c;intros.
  assert (Hx:= U.to_Z_spec x);assert (Hy:= U.to_Z_spec y).
  generalize (U.ltb_spec x (U.sub x y));destruct (U.ltb x (U.sub x y));
  unfold interp_carry;rewrite U.sub_spec;intros.
  destruct (Z_le_gt_dec 0 ([|x|] - [|y|])).
  rewrite Zmod_def_small in H;auto with zarith.
  rewrite <- Zmod_unique with (q:=-1) (r:=wB+([|x|] - [|y|]));auto with
   zarith.
  destruct (Z_le_gt_dec 0 ([|x|] - [|y|])).
  rewrite Zmod_def_small;auto with zarith.
  rewrite <- Zmod_unique with (q:=-1) (r:=wB+([|x|] - [|y|])) in H;auto with
   zarith.
 Qed.

 Lemma uint_sub_carry_c_spec : 
     forall x y, [-|uint_sub_carry_c x y|] = [|x|] - [|y|] - 1.
 Proof.
  unfold uint_sub_carry_c;intros x y. 
  assert (Hx:= U.to_Z_spec x);assert (Hy:= U.to_Z_spec y).
  generalize (U.leb_spec x (U.sub (U.sub x y) U.one));destruct 
   (U.leb x (U.sub (U.sub x y) U.one));unfold interp_carry;
   repeat rewrite U.sub_spec;rewrite U.I_to_Z;intros.
  destruct (Z_le_gt_dec 0 ([|x|]-[|y|])).
  rewrite (Zmod_def_small([|x|] - [|y|]));auto with zarith.
  rewrite (Zmod_def_small([|x|] - [|y|])) in H;auto with zarith.
  destruct (Z_le_gt_dec 0 ([|x|]-[|y|]-1)).
  rewrite Zmod_def_small in H;auto with zarith.
  rewrite <- Zmod_unique with (q:=-1) (r:=wB+([|x|] - [|y|]-1));auto with
   zarith.
  rewrite <- Zmod_unique with (n:=[|x|] - [|y|])(q:=-1)(r:=wB+([|x|] - [|y|]));
  auto with zarith.
  rewrite <- Zmod_unique with(n:=[|x|]-[|y|])(q:=-1)(r:=wB+([|x|]-[|y|])) in H;
  auto with zarith.
  destruct (Z_le_gt_dec 0 (wB+[|x|]-[|y|]-1)).
  rewrite Zmod_def_small;auto with zarith.
  rewrite <- Zmod_unique with (q:=-1) (r:=wB+wB+([|x|] - [|y|]-1)) in H;
  auto with zarith.
  zarith.  
  destruct (Z_le_gt_dec 0 ([|x|]-[|y|])).
  rewrite (Zmod_def_small([|x|] - [|y|]));auto with zarith.
  rewrite (Zmod_def_small([|x|] - [|y|])) in H;auto with zarith.
  destruct (Z_le_gt_dec 0 ([|x|]-[|y|]-1)).
  rewrite Zmod_def_small;auto with zarith.
  rewrite <- Zmod_unique with (q:=-1) (r:=wB+([|x|] - [|y|]-1)) in H;auto with
   zarith.
  rewrite <- Zmod_unique with (n:=[|x|] - [|y|])(q:=-1)(r:=wB+([|x|] - [|y|]));
  auto with zarith.
  rewrite <- Zmod_unique with(n:=[|x|]-[|y|])(q:=-1)(r:=wB+([|x|]-[|y|])) in H;
  auto with zarith.
  destruct (Z_le_gt_dec 0 (wB+[|x|]-[|y|]-1)).
  rewrite Zmod_def_small in H;auto with zarith.
  rewrite Zmod_def_small;auto with zarith.
 Qed.

 Lemma uint_pred_spec : forall x, [|uint_pred x|] = ([|x|] - 1) mod wB.
 Proof.
  intros x;unfold uint_pred;rewrite U.sub_spec;rewrite U.I_to_Z;trivial.
 Qed.

 Lemma uint_sub_carry_spec :
    forall x y, [|uint_sub_carry x y|] = ([|x|] - [|y|] - 1) mod wB.
 Proof.
  intros x y;unfold uint_sub_carry;repeat rewrite U.sub_spec. rewrite U.I_to_Z.
  assert (Hx:= U.to_Z_spec x);assert (Hy:= U.to_Z_spec y).
  destruct (Z_le_gt_dec 0 ([|x|]-[|y|])).
  rewrite (Zmod_def_small ([|x|] - [|y|]));auto with zarith.
  rewrite <- Zmod_unique with (n:=[|x|] - [|y|])(q:=-1)(r:=wB+([|x|] - [|y|]));
  auto with zarith.
  replace ((wB + ([|x|] - [|y|]) - 1)) with ((([|x|] - [|y|]) - 1) + 1*wB).
  apply Z_mod_plus. auto with zarith. ring.
 Qed.

 Lemma uint_mul_c_spec : forall x y, [[uint_mul_c x y]] = [|x|] * [|y|].
 Proof.
  intros x y;unfold uint_mul_c;generalize (U.mul_c_spec x y).
  destruct (U.mul_c x y) as (h,l);intros H.
  rewrite <- H;apply WW_spec.
 Qed.

 Lemma uint_square_c_spec : forall x, [[uint_square_c x]] = [|x|] * [|x|].
 Proof.
  unfold uint_square_c;intros x;generalize (U.square_c_spec x).
  generalize (U.eqb_spec x U.zero);rewrite U.O_to_Z;destruct (U.eqb x U.zero).
  intros Heq H;rewrite Heq;trivial.
  destruct (U.square_c x)as (h,l);intros H Heq;rewrite <- Heq;trivial.
 Qed.

 Lemma uint_div_gt_spec : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := U.div_eucl a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof. intros;apply U.div_eucl_spec;trivial. Qed.

 Lemma uint_mod_gt_spec : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      [|U.uint_mod a b|] = [|a|] mod [|b|].
 Proof. intros;apply U.mod_spec;trivial. Qed.

 Lemma uint_gcd_gt_body_spec :
   forall a b n cont,
    [|b|] <= Zpower_nat 2 n -> 
    [|a|] > [|b|] ->
    (forall x y, [|x|] > [|y|] -> [|y|] <= Zpower_nat 2 (n-1) -> 
     Zis_gcd [|x|] [|y|] [|cont x y|]) ->
    Zis_gcd [|a|] [|b|] [|uint_gcd_gt_body cont a b|].
 Proof.
  intros a b n cont Hle Hgt Hcont;unfold uint_gcd_gt_body.
  generalize (U.eqb_spec b U.zero);rewrite U.O_to_Z;destruct (U.eqb b U.zero);
  intros. rewrite H;apply Zis_gcd_0.
  assert (Hb:=U.to_Z_spec b);apply Zis_gcd_mod;auto with zarith.
  generalize (U.eqb_spec (U.uint_mod a b) U.zero);rewrite U.O_to_Z;
  destruct (U.eqb (U.uint_mod a b) U.zero);intros.
  rewrite U.mod_spec in H0. rewrite H0;apply Zis_gcd_0. auto with zarith.
  assert (0<= [|U.uint_mod a b|] < [|b|]).
   rewrite U.mod_spec;auto with zarith. 
   rewrite U.mod_spec in H0;auto with zarith.
   apply Z_mod_lt;auto with zarith.
  apply Zis_gcd_mod;auto with zarith.
  rewrite <- U.mod_spec;auto with zarith.
  rewrite <- U.mod_spec;auto with zarith.
  rewrite <- U.mod_spec;auto with zarith.
  apply Hcont;auto with zarith.
  destruct (Z_mod_lt  [|b|] [|U.uint_mod a b|]);auto with zarith.
  rewrite <- (U.mod_spec b) in H3;auto with zarith.
  rewrite U.mod_spec in H0;auto with zarith.
  rewrite U.mod_spec in H1;auto with zarith.
  repeat rewrite U.mod_spec;auto with zarith.

  apply Zle_trans with ((Zpower_nat 2 n)/2). 
  apply Zdiv_le_lower_bound;zarith. 
  apply Zle_trans with ([|b|]);zarith.
  assert (Hxx : [|a|] mod [|b|] > 0);zarith.
  assert (H3' := Z_div_mod_eq [|b|] ([|a|] mod [|b|]) Hxx).
  assert (H4' : 0 <= [|b|]/([|a|] mod [|b|])).
   apply Zge_le;apply Z_div_ge0;zarith. 
  pattern [|b|] at 3;rewrite H3'.
  destruct (Zle_lt_or_eq _ _ H4').
  assert (H6' : [|b|] mod ([|a|] mod [|b|]) = 
                  [|b|] - ([|a|] mod [|b|]) * ([|b|]/([|a|] mod [|b|]))).
  simpl;pattern [|b|] at 3;rewrite H3';ring.
  assert (([|a|] mod [|b|]) <= ([|a|] mod [|b|]) * ([|b|]/([|a|] mod [|b|]))).
  pattern ([|a|] mod [|b|]) at 1;rewrite <- Zmult_1_r;zarith.
  assert (H8 := Z_mod_lt [|b|]  ([|a|] mod [|b|]));zarith.
  rewrite <- H2 in H3';rewrite Zmult_0_r in H3';simpl in H3';zarith.
  assert (H8 := Z_mod_lt [|b|]  ([|a|] mod [|b|]));zarith.
  case n; simpl. unfold Zle; intro. discriminate H2.
  intros n0;replace (n0 - 0)%nat with n0. 2:zarith.
  change (S n0) with (plus (S 0) n0).  
  rewrite Zpower_nat_is_exp. rewrite Zmult_comm. change (2^1) with 2.
  rewrite Z_div_mult;zarith.
 Qed.

 Lemma uint_gcd_gt_spec : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|uint_gcd_gt a b|].
 Proof.
  unfold uint_gcd_gt. intros a b. 
  cut ([|b|] <= Zpower_nat 2 (nat_of_P U.digits)).
  generalize (nat_of_P U.digits) a b;clear a b.
  induction n;simpl.
  intros. apply uint_gcd_gt_body_spec with O;trivial.
  intros. change (Zpower_nat 2 (0 - 1)) with 1 in H2.
  assert (Hy := U.to_Z_spec y). 
  generalize (U.eqb_spec y U.one);rewrite U.I_to_Z;destruct (U.eqb y U.one);
  intros. rewrite H3;rewrite U.I_to_Z.
  apply Zis_gcd_mod. unfold Zlt;trivial.
  assert ([|x|] mod 1= 0).
   destruct (Z_mod_lt [|x|] 1);zarith.
  rewrite H4;apply Zis_gcd_0.
  replace [|y|] with 0;zarith.
  intros. apply uint_gcd_gt_body_spec with (S n);trivial.
  replace (S n - 1)%nat with n;zarith.
  rewrite <- Zpower_pos_nat. change (Zpower_pos 2 U.digits) with wB.
  destruct (U.to_Z_spec b);auto with zarith.
 Qed.

 Lemma uint_gcd_spec :forall a b, Zis_gcd [|a|] [|b|] [|uint_gcd a b|]. 
 Proof.
  intros a b;unfold uint_gcd.
  generalize (U.compare_spec a b);destruct (U.compare a b);intros.
  rewrite H. apply Zis_gcd_for_euclid with 1.
  ring([|b|] - 1 * [|b|]);zarith. 
  apply Zis_gcd_sym. apply uint_gcd_gt_spec;zarith.
  apply uint_gcd_gt_spec;zarith.
 Qed.
 
 Lemma uint_add_mul_div_spec : forall x y p,
       Zpos p < Zpos U.digits ->
       [|uint_add_mul_div p x y |] =
         ([|x|] * (Zpower 2 (Zpos p)) +
          [|y|] / (Zpower 2 ((Zpos U.digits) - (Zpos p)))) mod wB.
 Proof.
  intros. unfold uint_add_mul_div.
  rewrite U.add_spec. rewrite U.lsl_spec;trivial.
  rewrite U.lsr_spec;trivial. rewrite Zpos_minus;zarith.
  rewrite Zpos_minus;zarith.
  assert (0 < Zpos p);zarith. unfold Zlt;trivial.
 Qed.

 Lemma znz_spec : znz_spec uint_op.
 Proof.
  apply mk_znz_spec.
  apply U.to_Z_spec. apply U.of_pos_spec.
  apply U.O_to_Z. apply U.I_to_Z. apply U.Bm1_to_Z.
  exact WW_spec. exact OW_spec. exact W0_spec.
  exact U.compare_spec. exact eq0_spec.
  exact uint_opp_c_spec. exact U.opp_spec. exact uint_opp_carry_spec.
  exact uint_succ_c_spec. exact uint_add_c_spec. exact uint_add_carry_c_spec.
  exact uint_succ_spec. exact U.add_spec. exact uint_add_carry_spec.
  exact uint_pred_c_spec. exact uint_sub_c_spec. exact uint_sub_carry_c_spec.
  exact uint_pred_spec. exact U.sub_spec. exact uint_sub_carry_spec.
  exact uint_mul_c_spec. exact U.mul_spec. exact uint_square_c_spec.
  exact U.div21_spec. exact uint_div_gt_spec. exact U.div_eucl_spec.
  exact uint_mod_gt_spec. exact U.mod_spec.
  exact uint_gcd_gt_spec. exact uint_gcd_spec.
  exact U.head0_spec. exact uint_add_mul_div_spec.
 Qed.

 Definition w1_op := mk_zn2z_op uint_op.           
 Definition w2_op := mk_zn2z_op w1_op.
 Definition w3_op := mk_zn2z_op w2_op.
 Definition w4_op := mk_zn2z_op_karatsuba w3_op.
 Definition w5_op := mk_zn2z_op_karatsuba w4_op.
 Definition w6_op := mk_zn2z_op_karatsuba w5_op.
 Definition w7_op := mk_zn2z_op_karatsuba w6_op.
 Definition w8_op := mk_zn2z_op_karatsuba w7_op.
 Definition w9_op := mk_zn2z_op_karatsuba w8_op.
 Definition w10_op := mk_zn2z_op_karatsuba w9_op.
 Definition w11_op := mk_zn2z_op_karatsuba w10_op.
 Definition w12_op := mk_zn2z_op_karatsuba w11_op.
 Definition w13_op := mk_zn2z_op_karatsuba w12_op.
 Definition w14_op := mk_zn2z_op_karatsuba w13_op.

End MakeUintZnZ.




