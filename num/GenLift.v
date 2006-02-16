Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import ZPowerAux.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import GenBase.

Open Local Scope Z_scope.

Section GenLift.
 Variable w : Set.
 Variable w_0 : w.
 Variable w_WW : w -> w -> zn2z w.
 Variable w_W0 : w ->  zn2z w.
 Variable w_0W : w ->  zn2z w.
 Variable w_compare : w -> w -> comparison.
 Variable w_head0 : w -> N.
 Variable w_add_mul_div : positive -> w -> w -> w.
 Variable w_digits : positive.
 Variable ww_Digits : positive.

 Definition ww_head0 x :=
  match x with
  | W0 => Npos ww_Digits
  | WW xh xl =>
    match w_compare w_0 xh with
    | Eq => Nplus (Npos w_digits) (w_head0 xl)
    | _ => w_head0 xh
    end
  end.

  (* 0 < p < ww_digits *)
 Definition ww_add_mul_div p x y := 
  match x, y with
  | W0, W0 => W0
  | W0, WW yh yl =>
    match Pcompare p w_digits Eq with
    | Eq => w_0W yh 
    | Lt => w_0W (w_add_mul_div p w_0 yh)
    | Gt =>
      let n := Pminus p w_digits in
      w_WW (w_add_mul_div n w_0 yh) (w_add_mul_div n yh yl)
    end
  | WW xh xl, W0 =>
    match Pcompare p w_digits Eq with
    | Eq => w_W0 xl 
    | Lt => w_WW (w_add_mul_div p xh xl) (w_add_mul_div p xl w_0)
    | Gt =>
      let n := Pminus p w_digits in
      w_W0 (w_add_mul_div n xl w_0) 
    end
  | WW xh xl, WW yh yl =>
    match Pcompare p w_digits Eq with
    | Eq => w_WW xl yh 
    | Lt => w_WW (w_add_mul_div p xh xl) (w_add_mul_div p xl yh)
    | Gt =>
      let n := Pminus p w_digits in
      w_WW (w_add_mul_div n xl yh) (w_add_mul_div n yh yl)
    end
  end.

 Section GenProof.
  Variable w_to_Z : w -> Z.
 
  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_w_W0 : forall h, [[w_W0 h]] = [|h|] * wB.
  Variable spec_w_0W : forall l, [[w_0W l]] = [|l|].
  Variable spec_compare : forall x y,
       match w_compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end.
  Variable spec_ww_digits : ww_Digits = xO w_digits.
  Variable spec_w_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ (Z_of_N (w_head0 x)) * [|x|] < wB.
  Variable spec_w_add_mul_div : forall x y p,
       Zpos p < Zpos w_digits ->
       [| w_add_mul_div p x y |] =
         ([|x|] * (Zpower 2 (Zpos p)) +
          [|y|] / (Zpower 2 ((Zpos w_digits) - (Zpos p)))) mod wB.
 

  Hint Resolve div_le_0 div_lt w_to_Z_wwB: lift.
  Ltac zarith := auto with zarith lift.
   
  Lemma spec_ww_head0  : forall x,  0 < [[x]] ->
	 wwB/ 2 <= 2 ^ (Z_of_N (ww_head0 x)) * [[x]] < wwB.
  Proof.
   rewrite wwB_div_2;rewrite Zmult_comm;rewrite wwB_wBwB.
   assert (U:= lt_0_wB w_digits); destruct x as [ |xh xl];simpl;intros H.
   unfold Zlt in H;discriminate H.
   assert (H0 := spec_compare w_0 xh);rewrite spec_w_0 in H0.
   destruct (w_compare w_0 xh).
   rewrite <- H0;simpl. rewrite <- H0 in H;simpl in H.
   generalize (spec_w_head0 H);destruct (w_head0 xl) as [ |q].
   intros H1;simpl Zpower in H1;rewrite Zmult_1_l in H1.
   change (2 ^ Z_of_N (Npos w_digits)) with wB;split;zarith.
   apply Zmult_lt_compat_l;zarith.
   unfold Z_of_N;intros.
   change (Zpos(w_digits + q))with (Zpos w_digits + Zpos q);rewrite Zpower_exp.
   fold wB;rewrite <- Zmult_assoc;split;zarith.
   apply Zmult_lt_compat_l;zarith.
   intro H2;discriminate H2. intro H2;discriminate H2.
   assert (H1 := spec_w_head0 H0).
   split.
   rewrite Zmult_plus_distr_r;rewrite Zmult_assoc.
   apply Zle_trans with (2 ^ Z_of_N (w_head0 xh) * [|xh|] * wB).
   rewrite Zmult_comm;zarith.
   assert (0 <= 2 ^ Z_of_N (w_head0 xh) * [|xl|]);zarith.
   assert (H2:=spec_to_Z xl);apply Zmult_le_0_compat;zarith.
   assert (0<= Z_of_N (w_head0 xh)).
    case (w_head0 xh);intros;simpl;intro H2;discriminate H2.
   generalize (Z_of_N (w_head0 xh)) H1 H2;clear H1 H2;intros p H1 H2.
   assert (Eq1 : 2^p < wB).
     rewrite <- (Zmult_1_r (2^p));apply Zle_lt_trans with (2^p*[|xh|]);zarith.
   assert (Eq2: p < Zpos w_digits).
    destruct (Zle_or_lt (Zpos w_digits) p);trivial;contradict  Eq1.
   apply Zle_not_lt;unfold base;apply Zpower_le_monotone;zarith.
   assert (Zpos w_digits = p + (Zpos w_digits - p)). ring.
   unfold base at 2;rewrite H3;rewrite Zpower_exp;zarith.
   rewrite <- Zmult_assoc; apply Zmult_lt_compat_l; zarith.
   rewrite <- (Zplus_0_r (2^(Zpos w_digits - p)*wB));apply beta_lex_inv;zarith.
   apply Zmult_lt_reg_r with (2 ^ p); zarith.
   rewrite <- Zpower_exp;zarith. 
   rewrite Zmult_comm;ring (Zpos w_digits - p + p);fold wB;zarith.
   assert (H1 := spec_to_Z xh);zarith.
  Qed.

  Hint Rewrite Zdiv_0 Zmult_0_l Zplus_0_l Zmult_0_r Zplus_0_r
    spec_w_W0 spec_w_0W spec_w_WW spec_w_0  
    (wB_div w_digits w_to_Z spec_to_Z) 
    (wB_div_plus w_digits w_to_Z spec_to_Z) : w_rewrite.
  Ltac w_rewrite := autorewrite with w_rewrite;trivial.
 
  Lemma spec_ww_add_mul_div_aux : forall xh xl yh yl p,
     Zpos p < Zpos (xO w_digits) ->
      [[match (p ?= w_digits)%positive Eq with
        | Eq => w_WW xl yh
        | Lt => w_WW (w_add_mul_div p xh xl) (w_add_mul_div p xl yh)
        | Gt =>
            let n := (p - w_digits)%positive in
            w_WW (w_add_mul_div n xl yh) (w_add_mul_div n yh yl)
        end]] =  
      ([[WW xh xl]] * (2^Zpos p) +
       [[WW yh yl]] / (2^(Zpos (xO w_digits) - Zpos p))) mod wwB.
  Proof.
   intros xh xl yh yl p;assert (HwwB := wwB_pos w_digits).
   assert (0 < Zpos p). unfold Zlt;reflexivity.
   replace (Zpos (xO w_digits)) with (Zpos w_digits + Zpos w_digits).
   2 : rewrite Zpos_xO;ring.
   replace (Zpos w_digits + Zpos w_digits - Zpos p) with 
     (Zpos w_digits + (Zpos w_digits - Zpos p)). 2:ring.
   intros Hp; assert (Hxh := spec_to_Z xh);assert (Hxl:=spec_to_Z xl);
   assert (Hx := spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW xh xl));
   simpl in Hx;assert (Hyh := spec_to_Z yh);assert (Hyl:=spec_to_Z yl);
   assert (Hy:=spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW yh yl));simpl in Hy.
   case_eq  ((p ?= w_digits)%positive Eq);intros;w_rewrite;
    match goal with 
    | [H: (p ?= w_digits)%positive Eq = Eq |- _] =>
      let H1:= fresh "H" in
      (assert (H1 : Zpos p = Zpos w_digits);
       [ rewrite Pcompare_Eq_eq with (1:= H);trivial
       | rewrite H1;try rewrite Zminus_diag;try rewrite Zplus_0_r]);
      fold wB
    | [H: (p ?= w_digits)%positive Eq = Lt |- _] =>
      change ((p ?= w_digits)%positive Eq = Lt) with 
      (Zpos p < Zpos w_digits) in H;
      repeat rewrite spec_w_add_mul_div;zarith
    | [H: (p ?= w_digits)%positive Eq = Gt |- _] =>
      change ((p ?= w_digits)%positive Eq=Gt)with(Zpos p > Zpos w_digits) in H;
      let H1 := fresh "H" in
      assert (H1 := Zpos_minus _ _ (Zgt_lt _ _ H));
      replace (Zpos w_digits + (Zpos w_digits - Zpos p)) with
       (Zpos w_digits - Zpos (p - w_digits));
      [ repeat rewrite spec_w_add_mul_div;zarith
      | zarith ] 
    | _ => idtac
    end;simpl ww_to_Z;w_rewrite;zarith.
   rewrite Zmult_plus_distr_l;rewrite <- Zmult_assoc;rewrite <- Zplus_assoc.
   rewrite <- wwB_wBwB;apply Zmod_unique with [|xh|]. apply lt_0_wwB. 
   exact (spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW xl yh)). ring.
   rewrite Zmult_plus_distr_l.
   pattern ([|xl|] * 2 ^ Zpos p) at 2;
   rewrite shift_unshift_mod with (n:= Zpos w_digits);fold wB;zarith.
   replace ([|xh|] * wB * 2^Zpos p) with ([|xh|] * 2^Zpos p * wB). 2:ring. 
   rewrite Zplus_assoc;rewrite <- Zmult_plus_distr_l. rewrite <- Zplus_assoc.
   unfold base at 5;rewrite <- Zmod_shift_r;zarith.
   unfold base;rewrite Zmod_shift_r with (b:= Zpos (ww_digits w_digits));
   fold wB;fold wwB;zarith.
   rewrite wwB_wBwB;rewrite  Zmult_mod_distr_r;zarith.
   unfold ww_digits;rewrite Zpos_xO;zarith. apply Z_mod_lt;zarith.
   split;zarith. apply Zdiv_lt_upper_bound;zarith.
   rewrite <- Zpower_exp;zarith.
   ring (Zpos p + (Zpos w_digits - Zpos p));fold wB;zarith.
   pattern wB at 5;replace wB with 
    (2^(Zpos (p - w_digits) + (Zpos w_digits - Zpos (p - w_digits)))).
   rewrite Zpower_exp;zarith. rewrite Zmult_assoc.
   rewrite Z_div_plus_l;zarith.
   rewrite shift_unshift_mod with (a:= [|yh|]) (p:= Zpos (p - w_digits))
    (n := Zpos w_digits);zarith. fold wB.
   replace (Zpos p) with (Zpos (p - w_digits) + Zpos w_digits);zarith.
   rewrite Zpower_exp;zarith. rewrite Zmult_assoc. fold wB.
   repeat rewrite Zplus_assoc. rewrite <- Zmult_plus_distr_l.
   repeat rewrite <- Zplus_assoc.
   unfold base;rewrite Zmod_shift_r with (b:= Zpos (ww_digits w_digits));
   fold wB;fold wwB;zarith.
   unfold base;rewrite Zmod_shift_r with (a:= Zpos w_digits) 
   (b:= Zpos w_digits);fold wB;fold wwB;zarith.
   rewrite wwB_wBwB;rewrite  Zmult_mod_distr_r;zarith.
   rewrite Zmult_plus_distr_l.
   replace ([|xh|] * wB * 2 ^ Zpos (p - w_digits)) with 
     ([|xh|]*2^Zpos(p - w_digits)*wB). 2:ring.
   repeat rewrite <- Zplus_assoc. 
   rewrite (Zplus_comm ([|xh|] * 2 ^ Zpos (p - w_digits) * wB)).
   rewrite Z_mod_plus;zarith. rewrite Zmod_mult_0;zarith.
   unfold base;rewrite <- Zmod_shift_r;zarith. fold base;apply Z_mod_lt;zarith.
   split;zarith. apply Zdiv_lt_upper_bound;zarith.
   rewrite <- Zpower_exp;zarith. 
   ring (Zpos (p - w_digits) + (Zpos w_digits - Zpos (p - w_digits))); fold 
   wB;zarith. unfold ww_digits;rewrite Zpos_xO;zarith.
   unfold base;rewrite <- Zmod_shift_r;zarith. fold base;apply Z_mod_lt;zarith.
   split;zarith. apply Zdiv_lt_upper_bound;zarith.
   rewrite <- Zpower_exp;zarith. 
   ring (Zpos (p - w_digits) + (Zpos w_digits - Zpos (p - w_digits))); fold 
   wB;zarith. 
   ring (Zpos (p - w_digits) + (Zpos w_digits - Zpos (p - w_digits))); fold 
   wB;trivial.
  Qed.

  Lemma spec_ww_add_mul_div : forall x y p,
       Zpos p < Zpos (xO w_digits) ->
       [[ ww_add_mul_div p x y ]] =
         ([[x]] * (2^Zpos p) +
          [[y]] / (2^(Zpos (xO w_digits) - Zpos p))) mod wwB.
  Proof.
   intros x y p H.
   destruct x as [ |xh xl];
   [assert (H1 := @spec_ww_add_mul_div_aux w_0 w_0)
   |assert (H1 := @spec_ww_add_mul_div_aux xh xl)];
   (destruct y as [ |yh yl];
    [generalize (H1 w_0 w_0 p H) | generalize (H1 yh yl p H)];
    clear H1;w_rewrite);simpl ww_add_mul_div.
   replace [[WW w_0 w_0]] with 0;[w_rewrite|simpl;w_rewrite;trivial].
   intros Heq;rewrite <- Heq;clear Heq.
   case_eq ((p ?= w_digits)%positive Eq);w_rewrite;intros;trivial.
   rewrite (spec_w_add_mul_div w_0 w_0);w_rewrite;zarith.
   replace [[WW w_0 w_0]] with 0;[w_rewrite|simpl;w_rewrite;trivial].
   intros Heq;rewrite <- Heq;clear Heq.
   case_eq ((p ?= w_digits)%positive Eq);w_rewrite;intros;trivial.
   rewrite (spec_w_add_mul_div w_0 w_0);w_rewrite;zarith.
   change ((p ?= w_digits)%positive Eq = Gt)with(Zpos p > Zpos w_digits) in H0.
   rewrite Zpos_minus;zarith. rewrite Zpos_xO in H;zarith.
  Qed.

 End GenProof.

End GenLift.

