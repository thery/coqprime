(*
Unset Boxed Definitions.
*)

Set Implicit Arguments.

Require Import ZArith.
Require Import ZnZ.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Zn2Z.
Require Import ZPowerAux.

Open Local Scope Z_scope.

 (* ********************************************************** *)
 (* **                    The Proofs ...                    ** *)
 (* ********************************************************** *)

Section Proof.
 Variable w:Set.
 Variable w_op : znz_op w.
 Variable op_spec : znz_spec w_op.

 Notation "[| x |]" := (znz_to_Z w_op x)  (at level 0, x at level 99).
 
 Notation wB := (base (znz_digits w_op)).

 Notation "[+| c |]" := 
   (interp_carry 1 wB (znz_to_Z w_op) c)  (at level 0, x at level 99).

 Notation "[-| c |]" := 
   (interp_carry (-1) wB (znz_to_Z w_op) c)  (at level 0, x at level 99).

 Notation "[[ x ]]" := 
   (ww_to_Z w_op x)  (at level 0, x at level 99).

 Notation wwB := (base (xO (znz_digits w_op))).

 Notation "[+[ c ]]" := 
   (interp_carry 1 wwB (ww_to_Z w_op) c)  (at level 0, x at level 99).

 Notation "[-[ c ]]" := 
   (interp_carry (-1) wwB (ww_to_Z w_op) c)  (at level 0, x at level 99).

 Notation "[|| x ||]" := 
   (zn2z_to_Z wwB (ww_to_Z w_op) x)
   (at level 0, x at level 99).

 Hint Rewrite 
    (spec_0 op_spec)
    (spec_1 op_spec)
    (spec_Bm1 op_spec)
    (spec_WW op_spec)
    (spec_CW op_spec)
    (spec_opp_c op_spec)
    (spec_opp_carry op_spec)
    (spec_succ_c op_spec)
    (spec_add_c op_spec)
    (spec_add_carry_c op_spec)
    (spec_add op_spec)
    (spec_pred_c op_spec)
    (spec_sub_c op_spec)
    (spec_sub_carry_c op_spec)
    (spec_sub op_spec)
    (spec_mul_c op_spec)
    (spec_mul op_spec)
    : w_rewrite.

 Ltac zarith := auto with zarith. 
 Ltac w_rewrite := autorewrite with w_rewrite.
 Ltac w_solve := trivial;w_rewrite;trivial;try ring;try omega.

 Lemma wwB_wBwB : wwB = wB * wB.
 Proof.
  unfold base;rewrite (Zpos_xO (znz_digits w_op)).
  replace  (2 * Zpos (znz_digits w_op)) with 
    (Zpos (znz_digits w_op) + Zpos (znz_digits w_op)).
  apply Zpower_exp; unfold Zge;simpl;intros;discriminate.
  ring.
 Qed.

 Hint Rewrite wwB_wBwB : w_rewrite1.

 Ltac w_rewrite1 := autorewrite with w_rewrite w_rewrite1.
 Ltac w_solve1 := trivial;w_rewrite1;trivial;try ring;try omega.

 Lemma spec_ww_to_Z   : forall x, 0 <= [[ x ]] < wwB.
 Proof with w_solve1.
  destruct x;simpl.
  split... 
  destruct (spec_to_Z op_spec (znz_0 w_op)); apply Zmult_lt_O_compat...
  destruct (spec_to_Z op_spec w0);destruct (spec_to_Z op_spec w1)...
  split.
  change 0 with (0+0);apply Zplus_le_compat...
  apply Zmult_le_0_compat ...
  apply Zle_lt_trans with (wB*wB - 1) ...
  replace (wB*wB - 1) with (wB*(wB - 1) + (wB - 1)) ...
  apply Zplus_le_compat...  apply Zmult_le_compat ...
 Qed.
  
 Theorem spec_ww_of_pos : forall p, 
       Zpos p = 
        (Z_of_N (fst (ww_of_pos w_op p)))*wwB + [[(snd (ww_of_pos w_op p))]].
  intros p; simpl.
  unfold ww_of_pos.
  generalize (spec_of_pos op_spec p); case  (znz_of_pos w_op p).
  intros n w0 Hw0; rewrite Hw0; case n; simpl fst; simpl snd; w_rewrite.
  simpl; w_rewrite; rewrite Zmult_0_r; rewrite Zplus_0_l; auto.
  intros p0.
  generalize (spec_of_pos op_spec p0); case  (znz_of_pos w_op p0).
  intros n0 w1; simpl fst; simpl snd; w_rewrite.
  intros H; replace (Z_of_N (Npos p0)) with (Zpos p0).
  2: case p0; simpl; auto.
  unfold ww_to_Z; rewrite spec_WW; auto.
  rewrite H; simpl; w_solve1.
  Qed.

 Lemma spec_ww_0   : [[W0]] = 0.
 Proof. trivial. Qed.

 Lemma spec_ww_1   : [[WW (znz_0 w_op) (znz_1 w_op)]] = 1.
 Proof. simpl;w_solve. Qed.

 Lemma spec_ww_Bm1 : [[WW (znz_Bm1 w_op) (znz_Bm1 w_op)]] = wwB - 1.
 Proof. simpl;w_solve1. Qed.

 Lemma spec_ww_WW  : forall h l, [||ww_WW h l||] = [[h]] * wwB + [[l]].
 Proof with w_solve1.
  intros;simpl;unfold ww_WW.
  destruct h;simpl ... destruct l;simpl ...
 Qed.

 Hint Rewrite spec_ww_0 spec_ww_1 spec_ww_Bm1 spec_ww_WW : w_rewrite.

 Lemma spec_ww_CW  : 
   forall sign c l, 
    interp_carry sign (wwB*wwB) (zn2z_to_Z wwB (ww_to_Z w_op)) (ww_CW c l) =
        (interp_carry sign wwB (ww_to_Z w_op) c)* wwB + [[l]].
 Proof with w_solve.
  intros sign c l;destruct c;simpl ...
 Qed.

 Lemma spec_ww_hl: forall h l, [[WW h l]] = wB * [|h|] + [|l|].
intros; simpl; auto.
Qed.
Hint Rewrite spec_ww_hl: w_rewrite.

    (*    Auxillary lemmas *)

Theorem beta_lex: forall a b c d beta, beta * a + b <= beta * c + d -> 0 <= b < beta -> 0 <= d < beta -> a <= c.
intros a b c d beta H1 (H3, H4) (H5, H6).
assert (a - c < 1); auto with zarith.
apply Zmult_lt_reg_r with beta; auto with zarith.
repeat rewrite (fun x => Zmult_comm x beta).
apply Zle_lt_trans with (d  - b); auto with zarith.
rewrite Zmult_minus_distr_l; auto with zarith.
Qed.

Theorem beta_lex_inv: forall a b c d beta, a < c -> 0 <= b < beta -> 0 <= d < beta -> beta * a + b < beta * c  + d. 
intros a b c d beta H1 (H3, H4) (H5, H6).
case (Zle_or_lt (beta * c + d) (beta * a + b)); auto with zarith.
intros H7; contradict H1; apply Zle_not_lt; apply beta_lex with (1 := H7); auto.
Qed.

Theorem wB_lex: forall a b c d, wB * a + b <= wB * c + d -> 0 <= b < wB -> 0 <= d < wB -> a <= c.
intros a b c d H1 H2 H3; apply beta_lex with (1 := H1); auto.
Qed.

Theorem wB_lex_inv: forall a b c d, a < c -> 0 <= b < wB -> 0 <= d < wB -> wB * a + b < wB * c + d. 
intros a b c d H1 H2 H3; apply beta_lex_inv with (1 := H1); auto.
Qed.

Theorem wBwB_lex: forall a b c d, wB * wB * a + b <= wB * wB * c + d -> 0 <= b < wB * wB -> 0 <= d < wB * wB -> a <= c.
intros a b c d H1 H2 H3; apply beta_lex with (1 := H1); auto.
Qed.

Theorem wBwB_lex_inv: forall a b c d, a < c -> 0 <= b < wB * wB -> 0 <= d < wB * wB -> wB * wB * a + b < wB * wB * c + d. 
intros a b c d H1 H2 H3; apply beta_lex_inv with (1 := H1); auto.
Qed.

    (* Comparison *)

 Lemma spec_ww_compare :
     forall x y, 
       match ww_compare w_op x y with
       | Eq => [[x]] = [[y]]
       | Lt => [[x]] < [[y]]
       | Gt => [[x]] > [[y]]
       end.
 Proof with w_solve.
  destruct x as [ |xh xl].

  destruct y as [ | yh yl];simpl ...
  destruct (spec_to_Z op_spec yl);destruct (spec_to_Z op_spec yh).
  assert (Hyh := spec_compare op_spec (znz_0 w_op) yh);
    destruct (znz_compare w_op (znz_0 w_op) yh).
  rewrite <-Hyh ...
  repeat rewrite Zmult_0_r. 
  pattern 0 at 1 3 5;rewrite <- (spec_0 op_spec).
  exact (spec_compare op_spec (znz_0 w_op) yl).
  change 0 with (0+0);apply Zplus_lt_le_compat ...
  apply Zmult_lt_O_compat...
  rewrite (spec_0 op_spec) in Hyh ...
  rewrite (spec_0 op_spec) in Hyh ...

  destruct (spec_to_Z op_spec xl);destruct (spec_to_Z op_spec xh).
  destruct y as [ | yh yl];simpl ...
  assert (Hxh := spec_compare op_spec xh (znz_0 w_op));
    destruct (znz_compare w_op xh (znz_0 w_op)).
  rewrite Hxh. rewrite (spec_0 op_spec).
  repeat rewrite Zmult_0_r. 
  pattern 0 at 2 4 6;rewrite <- (spec_0 op_spec).
  exact (spec_compare op_spec xl (znz_0 w_op)).
  rewrite (spec_0 op_spec) in Hxh ...
  rewrite (spec_0 op_spec) in Hxh; apply Zlt_gt.
  change 0 with (0+0);apply Zplus_lt_le_compat ...
  apply Zmult_lt_0_compat...

  destruct (spec_to_Z op_spec yl);destruct (spec_to_Z op_spec yh).
  assert (Hh := spec_compare op_spec xh yh);destruct (znz_compare w_op xh yh).
  rewrite Hh.   
  assert (Hl := spec_compare op_spec xl yl);
    destruct (znz_compare w_op xl yl)...
  apply wB_lex_inv; auto.
  apply Zlt_gt; apply wB_lex_inv; auto with zarith.
 Qed.

    (* Basic arithmetic operations *)
 Lemma spec_ww_opp_c : forall x, [-[ww_opp_c w_op x]] = -[[x]].
 Proof with w_solve1.
  destruct x;simpl ...
  assert (H1:=spec_opp_c op_spec w1);destruct (znz_opp_c w_op w1).
  simpl in H1.
  assert (znz_to_Z w_op w1 = 0). 
   destruct (spec_to_Z op_spec w2);destruct (spec_to_Z op_spec w1)...
  rewrite H...
  unfold interp_carry, ww_to_Z in * ...
 Qed.

 Lemma spec_ww_opp_carry : forall x, [[ww_opp_carry w_op x]] = wwB - [[x]] - 1.
 Proof. unfold ww_to_Z;destruct x;simpl; w_solve1. Qed.

 Lemma spec_ww_succ_c : forall x, [+[ww_succ_c w_op x]] = [[x]] + 1.
 Proof with w_solve.
  destruct x;simpl. w_solve.
  assert (H1:=spec_succ_c op_spec w1);destruct (znz_succ_c w_op w1).
  unfold interp_carry in * ...
  rewrite Zplus_assoc. rewrite (Zplus_comm 1);rewrite <- H1.
  unfold ww_to_Z;simpl...
  assert (H2:=spec_succ_c op_spec w0);destruct (znz_succ_c w_op w0);
   simpl;w_rewrite1.
  rewrite H2; unfold interp_carry in * ...
  rewrite H2; unfold interp_carry in * ... 
 Qed.

 Hint Rewrite spec_ww_opp_c spec_ww_opp_carry spec_ww_succ_c : w_rewrite.

 Lemma spec_ww_add_c  : forall x y, [+[ww_add_c w_op x y]] = [[x]] + [[y]].
 Proof with w_solve1.
  destruct x;simpl ...
  destruct y;simpl ...
  assert (H1:=spec_add_c op_spec w1 w3);destruct (znz_add_c w_op w1 w3);
   unfold interp_carry in H1 ...
 Qed.

 Lemma spec_ww_add_carry_c : 
   forall x y, [+[ww_add_carry_c w_op x y]] = [[x]] + [[y]] + 1.
 Proof with w_solve1.
  destruct x;simpl;intros y.
  fold (ww_succ_c w_op y)...
  destruct y;simpl.
  fold (ww_succ_c w_op (WW w0 w1)) ... simpl ...
  assert (H1:=spec_add_carry_c op_spec w1 w3);
    destruct (znz_add_carry_c w_op w1 w3);unfold interp_carry in H1 ...
 Qed.

 Hint Rewrite spec_ww_add_c spec_ww_add_carry_c : w_rewrite.


 Lemma spec_without_c : 
  forall (w:Set) B (interp:w->Z), (forall w, 0 <= interp w < B) ->
   forall sign c,
   interp (without_c c) = (interp_carry sign B interp c) mod B.
 Proof.
  intros;destruct c;simpl.
  rewrite Zmod_def_small;trivial.
  rewrite Zplus_comm;rewrite Z_mod_plus.
  rewrite Zmod_def_small;trivial.
  assert (H1 := H w1);omega.
 Qed.

 Lemma spec_ww_add : 
  forall x y, [[ww_add w_op x y]] = ([[x]] + [[y]]) mod wwB.
 Proof.
  intros x y;unfold ww_add.
  rewrite <- (spec_ww_add_c x y).
  apply (spec_without_c (ww_to_Z w_op) spec_ww_to_Z 1).
 Qed.
 Hint Rewrite spec_ww_add : w_rewrite.

 Opaque Zmult.
 
 Lemma spec_ww_pred_c : forall x, [-[ww_pred_c w_op x]] = [[x]] - 1.
 Proof with w_solve1.
  destruct x;simpl...
  assert (H:= spec_pred_c op_spec w1);destruct (znz_pred_c w_op w1).
  unfold interp_carry,ww_to_Z in * ...
  unfold interp_carry in H;w_solve1.
 Qed.

 Hint Rewrite spec_ww_pred_c : w_rewrite.

 Lemma spec_ww_sub_c : forall x y, [-[ww_sub_c w_op x y]] = [[x]] - [[y]].
 Proof with w_solve.
  destruct y;simpl ...
  destruct x.
  fold (ww_opp_c w_op (WW w0 w1)) ... simpl ...
  assert (H:= spec_sub_c op_spec w3 w1);destruct (znz_sub_c w_op w3 w1);
  unfold interp_carry in H;simpl;w_solve1.
 Qed.

 Lemma spec_ww_sub_carry_c : 
   forall x y, [-[ww_sub_carry_c w_op x y]] = [[x]] - [[y]] - 1.
 Proof with w_solve.
  destruct y;simpl.
  fold (ww_pred_c w_op x) ...
  destruct x;unfold ww_to_Z;simpl;w_solve1.
  assert (H1:=spec_sub_carry_c op_spec w3 w1);
    destruct (znz_sub_carry_c w_op w3 w1);unfold interp_carry in H1 ...
 Qed.

 Hint Rewrite spec_ww_sub_c spec_ww_sub_carry_c : w_rewrite.
 
 Lemma spec_ww_sub : 
  forall x y, [[ww_sub w_op x y]] = ([[x]] - [[y]]) mod wwB.
 Proof.
  intros x y;unfold ww_sub.
  rewrite <- (spec_ww_sub_c x y).
  apply (spec_without_c (ww_to_Z w_op) spec_ww_to_Z (-1)).
 Qed.
 Hint Rewrite spec_ww_sub: w_rewrite.

Theorem mult_wwB: forall x y, [|x|] * [|y|] < wwB.
  intros x y; rewrite wwB_wBwB.
  generalize (spec_to_Z op_spec x); intros U.
  generalize (spec_to_Z op_spec y); intros U1.
  apply Zle_lt_trans with ((wB -1 ) * (wB - 1)); auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_r || rewrite Zmult_minus_distr_l); auto with zarith.
Qed.
Hint Resolve mult_wwB.

 Lemma Zmult_lt_b : 
   forall b x y, 0 <= x < b -> 0 <= y < b -> 0 <= x * y <= b*b - 2*b + 1.
 Proof with zarith.
  intros b x y (Hx1,Hx2) (Hy1,Hy2);split...
  apply Zle_trans with ((b-1)*(b-1)).
  apply Zmult_le_compat...
  apply Zeq_le;ring.
 Qed.

 Ltac zmult_lt_b x y := 
   let H := fresh "H" in
   assert (H := Zmult_lt_b (spec_to_Z op_spec x)  (spec_to_Z op_spec y)).
 Ltac spec_to_Z x := 
   let H := fresh "H" in
   assert (H := spec_to_Z op_spec x).

  Theorem spec_znz_mul_c:
  forall x y, [[znz_mul_c w_op x y]] = [|x|] * [|y|].
  intros x y; unfold ww_to_Z; apply spec_mul_c; auto.
  Qed.
  Hint Rewrite spec_znz_mul_c: w_rewrite.

  Theorem  wB_pos: 1 < wB.
   unfold base. 
   apply Zlt_le_trans with 2; auto with zarith.
   pattern 2 at 1; rewrite <- (Zpower_exp_1).    
   apply Zpower_le_monotone; auto with zarith.
   split; auto with zarith. 
   case (znz_digits w_op); compute; intros; try discriminate.
  Qed.
  Hint Resolve wB_pos.

  Theorem wwB_pos: 1 < wwB. 
  rewrite wwB_wBwB.
  rewrite <- (Zmult_1_r 1).
  apply Zmult_lt_compat; auto with zarith.
  generalize wB_pos; auto with zarith.
  Qed.
  Hint Resolve wwB_pos.

 Lemma sum_mul_carry : forall xh xl yh yl wc cc,
   [|wc|]*wB*wB + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] -> 
   0 <= [|wc|] <= 1.
 Proof.
  intros. zmult_lt_b xh yl;zmult_lt_b xl yh;spec_to_Z wc.
  assert (H3 := spec_ww_to_Z cc). split;zarith.
  apply wBwB_lex with (b := [[cc]]) (d := wB * wB - 2); auto with zarith.
  rewrite (Zmult_comm (wB * wB)); rewrite Zmult_assoc; auto with zarith.
  rewrite <- wwB_wBwB; auto with zarith.
  generalize wB_pos; auto with zarith.
 Qed.

  Theorem mult_add_ineq: forall xH yH crossH, 0 <= [|xH|] * [|yH|] + [|crossH|] < wwB.
  intros xH yH crossH.
  generalize (spec_to_Z op_spec xH); intros HH.
  generalize (spec_to_Z op_spec yH); intros HH1.
  generalize (spec_to_Z op_spec crossH); intros HH2.
  split; auto with zarith.
  rewrite wwB_wBwB.
  apply Zle_lt_trans with  ((wB - 1) * (wB - 1) + (wB -1)); auto with zarith.
  apply Zplus_le_compat; auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); auto with zarith.
  Qed.
  Hint Resolve mult_add_ineq.

  Theorem C1_plus_wwB: forall z,  [+[C1 z]] = wwB + [[z]].
  intros zz; simpl; case wwB; auto with zarith.
  Qed.

  Theorem C1_plus_wB: forall z,  [+|C1 z|] = wB + [|z|].
  intros zz; simpl; case wB; auto with zarith.
  Qed.

  Theorem C1_minus_wwB: forall z, [-[C1 z]]  =  [[z]] - wwB.
  intro zz; simpl; generalize (wwB_pos); case wwB.
  intros; ring.
  intros; ring.
  intros p Hp; discriminate Hp.
  Qed.

  Theorem C1_minus_wB: forall z, [-|C1 z|]  =  [|z|] - wB.
  intro zz; simpl; generalize (wB_pos); case wB.
  intros; ring.
  intros; ring.
  intros p Hp; discriminate Hp.
  Qed.

  Hint Rewrite C1_plus_wwB C1_plus_wB C1_minus_wwB C1_minus_wB: w_rewrite.

  Theorem spec_ww_add_carry: forall x y, [[ww_add_carry w_op x y]] = ([[x]] + [[y]] + 1) mod wwB.
  intros x y.
  unfold ww_add_carry, without_c; simpl.
  generalize (spec_ww_add_carry_c x y); case (ww_add_carry_c w_op x y); intro z;
  generalize (spec_ww_to_Z z); intros HH;
  autorewrite with w_rewrite; simpl; intros Hz; rewrite <- Hz.
  rewrite Zmod_def_small ; auto with zarith.
  pattern wwB at 1; rewrite <- Zmult_1_l; rewrite Zplus_comm; rewrite Z_mod_plus; 
     try rewrite Zmod_def_small; auto with zarith.
  Qed.

   Lemma spec_mul_aux : forall xh xl yh yl wc (cc:zn2z w) hh ll,
   [[hh]] = [|xh|] * [|yh|] ->
   [[ll]] = [|xl|] * [|yl|] ->
   [|wc|]*wB*wB + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] ->
   [|| 
     match cc with
     | W0 => WW (ww_add w_op hh (WW wc (znz_0 w_op))) ll
     | WW cch ccl =>
     match ww_add_c w_op (WW ccl (znz_0 w_op)) ll with
       | C0 l => WW (ww_add w_op hh (WW wc cch)) l
       | C1 l => WW (ww_add_carry w_op hh (WW wc cch)) l
       end
     end ||] = [[WW xh xl]]*[[WW yh yl]].
  Proof with w_solve1.
  intros. 
  generalize (spec_to_Z op_spec xh); intros HH.
  generalize (spec_to_Z op_spec yh); intros HH1.
  generalize (spec_to_Z op_spec xl); intros HH2.
  generalize (spec_to_Z op_spec yl); intros HH3.
  generalize (spec_ww_to_Z hh); intros HH4.
  generalize (spec_ww_to_Z ll); intros HH5.
  generalize (sum_mul_carry _ _ _ _ _ _ H1); intros HH6.
   apply trans_equal with 
     ([|xh|]*[|yh|]*wB*wB + ([|xh|]*[|yl|]+[|xl|]*[|yh|])*wB +[|xl|]*[|yl|]).
  2:simpl...
  rewrite <- H;rewrite <- H0;rewrite <- H1.
  assert (H3 := Zmult_lt_b (spec_to_Z op_spec xh)  (spec_to_Z op_spec yh)).
  rewrite <- H in H3;destruct H3.
  assert (H5 := Zmult_lt_b (spec_to_Z op_spec xl)  (spec_to_Z op_spec yl)).
  rewrite <- H0 in H5;destruct H5.
  assert (H7 := Zmult_lt_b (spec_to_Z op_spec xh)  (spec_to_Z op_spec yl)).
  destruct H7.
  assert (HH8: 0 <= [[hh]] + wB * [|wc|] < wB * wB).
  split; auto with zarith.
  replace (wB * wB) with ((wB * wB - wB)  + wB); auto with zarith.
  apply Zplus_lt_le_compat; auto with zarith.
  rewrite H.
  apply Zle_lt_trans with ((wB -1) * (wB - 1)); auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); auto with zarith.
  generalize (wB_pos); auto with zarith.
  pattern wB at 2; rewrite <- Zmult_1_r; auto with zarith.
  destruct cc.
  simpl; autorewrite with w_rewrite.
  rewrite wwB_wBwB; rewrite Zmod_def_small; auto with zarith.
  ring.
  generalize (spec_to_Z op_spec w0); intros HH9.
  generalize (spec_to_Z op_spec w1); intros HH10.
  assert (U: 0 <= [[hh]] + (wB * [|wc|] + [|w0|]) < wB * wB).
  split; auto with zarith.
  generalize H1; autorewrite with w_rewrite; clear H1; intros H1.
  assert (wB * [|wc|] + [|w0|] < 2 * wB - 1); auto with zarith.
  apply Zmult_lt_reg_r with wB; auto with zarith.
  rewrite (Zmult_comm wB); rewrite Zmult_plus_distr_l; rewrite (Zmult_comm [|w0|]).
  apply Zplus_lt_reg_r with [|w1|].
  rewrite <- Zplus_assoc; rewrite H1.
  apply Zle_lt_trans with ((wB - 1) * (wB - 1) + (wB - 1) * (wB - 1)); auto with zarith.
  apply Zplus_le_compat; apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); auto with zarith.
  repeat (rewrite Zmult_1_l || rewrite Zmult_1_r); auto with zarith.
  rewrite <- Zmult_assoc; auto with zarith.
  generalize (spec_ww_add_c  (WW w1 (znz_0 w_op)) ll); 
  case  (ww_add_c w_op (WW w1 (znz_0 w_op)) ll).
  simpl; autorewrite with w_rewrite.
  intros z Hz; rewrite Hz.
  rewrite wwB_wBwB; rewrite Zmod_def_small; auto with zarith.
  ring.
  autorewrite with w_rewrite.
  intros z Hz;  rewrite wwB_wBwB;  simpl.
  rewrite C1_plus_wwB in Hz; rewrite wwB_wBwB in Hz.
  rewrite spec_ww_add_carry; rewrite Zmod_def_small; auto with zarith;
    autorewrite with w_rewrite.
  match goal with |- ?X = _ =>
    match type of Hz with ?Y = _ => apply trans_equal with (Y - Y + X);
         [idtac | pattern Y at 1; rewrite Hz]; ring
   end end.
  autorewrite with w_rewrite; split; auto with zarith.
  apply Zmult_lt_reg_r with wwB; auto with zarith.
  generalize (spec_ww_to_Z z); intros HH11.
  match goal with |- ?X  < _ =>
    apply Zle_lt_trans with (X + [[z]])
   end; auto with zarith.
  generalize (spec_ww_to_Z (WW xh xl)); intros HH12.
  generalize (spec_ww_to_Z (WW yh yl)); intros HH13.
  match goal with |- ?X  < _ =>
    replace X with ((wB * [|xh|] + [|xl|]) * (wB * [|yh|] + [|yl|]))
  end; auto with zarith.
  apply Zle_lt_trans with ((wwB - 1) * (wwB - 1)); auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  simpl in HH12; auto with zarith.
  simpl in HH13; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); auto with zarith.
  rewrite wwB_wBwB.
  match goal with |-  _ = ?X =>
    match type of Hz with ?Y = _ => apply trans_equal with (Y - Y + X);
         [pattern Y at 1; rewrite Hz | ring]
   end end.
  rewrite H; rewrite H0.
  match goal with |-  ?X = _  =>
    match type of H1 with _ = ?Y => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite <- H1]
   end end.
  autorewrite with w_rewrite; ring.
Qed.

Theorem spec_ww_mul_c : forall x y, [|| ww_mul_c w_op x y ||] = [[x]] * [[y]].
  intros x y; case x; auto; intros xh xl.
  case y; auto; try ring; intros yh yl.
  match goal with |- _ = ?X => set (tmp:= X); simpl; unfold tmp end.
  set (hh :=  (znz_mul_c w_op xh yh)).
  set (ll  :=  (znz_mul_c w_op xl yl)).
  generalize (spec_ww_add_c (znz_mul_c w_op xh yl) (znz_mul_c w_op xl yh)).
  case (ww_add_c w_op (znz_mul_c w_op xh yl) (znz_mul_c w_op xl yh)).
  intros wc Hwc.
  apply  spec_mul_aux with (cc := wc) (wc := w_op.(znz_0)) (hh := hh) (ll := ll).
  unfold hh; unfold ww_to_Z; apply spec_mul_c; auto.
  unfold ll; unfold ww_to_Z; apply spec_mul_c; auto.
  simpl in Hwc; rewrite Hwc; autorewrite with w_rewrite.
  unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  intros z; case z.
  autorewrite with w_rewrite; simpl.
  autorewrite with w_rewrite; simpl.
  intros H.
  rewrite Zmod_def_small.
  rewrite wwB_wBwB in H; rewrite wwB_wBwB.
  unfold hh, ll; unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  match goal with |-  _ = ?X =>
    match type of H with _ = ?Y => apply trans_equal with (wB * (Y - Y) + X);
         [pattern Y at 1; rewrite <- H | idtac]; ring
   end end.
  generalize (spec_to_Z op_spec xh); intros HH.
  generalize (spec_ww_to_Z hh); intros HH1.
  rewrite Zmult_1_r; split; auto with zarith.
  apply Zle_lt_trans with ((wwB - 2 * wB + 1) + (wB + 0)); auto with zarith.
  apply Zplus_le_compat_r.
  unfold hh, ww_to_Z; repeat rewrite spec_mul_c; auto with arith.
  match goal with |- ?X <= ? Y => assert (0 <= X <= Y) end; auto with zarith.
  rewrite wwB_wBwB; apply Zmult_lt_b; w_solve1.
  apply spec_to_Z; auto.
  assert (1 < wB); auto with zarith.
  intros cc1 cc2 Hwc.
  apply  spec_mul_aux with (cc := (WW cc1 cc2)) (wc := w_op.(znz_1)) (hh := hh) (ll := ll).
  unfold hh; unfold ww_to_Z; apply spec_mul_c; auto.
  unfold ll; unfold ww_to_Z; apply spec_mul_c; auto.
  generalize Hwc; w_rewrite.
  unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  rewrite wwB_wBwB; clear Hwc; intros Hwc; rewrite <- Hwc; ring.
Qed.

Theorem spec_ww_mul: forall x y, [[ww_mul w_op x y]] = ([[x]] * [[y]]) mod wwB.
  assert (U: 0 < wB).
  apply Zlt_trans with 1; auto with zarith.
  assert (U1: 0 < wwB).
  apply Zlt_trans with 1; auto with zarith.
  intros x y; case x; auto; intros xh xl.
  case y; auto.
 simpl; rewrite Zmult_0_r; rewrite Zmod_def_small; auto with zarith.
 intros yh yl.
 simpl; w_rewrite.
 rewrite <- Zmod_plus; auto with zarith.
 repeat (rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r).
 rewrite <- Zmult_mod_distr_l; auto with zarith.
 rewrite <- wwB_wBwB; auto with zarith.
 rewrite Zplus_0_r; rewrite Zmod_plus; auto with zarith.
 rewrite Zmod_mod; auto with zarith.
 rewrite <- Zmod_plus; auto with zarith.
  match goal with |- ?X mod _ = _ =>
    rewrite <- Z_mod_plus with (a := X) (b := [|xh|] * [|yh|])
  end; auto with zarith.
  eq_tac; auto; rewrite wwB_wBwB; ring.
Qed.

Theorem spec_ww_square_c : forall x, [||ww_square_c w_op x||] = [[x]] * [[x]].
  intros x; case x; auto; intros xh xl.
  match goal with |- _ = ?X => set (tmp:= X); simpl; unfold tmp end.
  set (hh :=  (znz_square_c w_op xh)).
  set (ll  :=  (znz_square_c w_op xl)).
  generalize (spec_ww_add_c (znz_mul_c w_op xh xl) (znz_mul_c w_op xh xl)).
  case (ww_add_c w_op (znz_mul_c w_op xh xl) (znz_mul_c w_op xh xl)).
  intros wc Hwc.
  apply  spec_mul_aux with (cc := wc) (wc := w_op.(znz_0)) (hh := hh) (ll := ll).
  unfold hh; unfold ww_to_Z; apply spec_square_c; auto.
  unfold ll; unfold ww_to_Z; apply spec_square_c; auto.
  simpl in Hwc; rewrite Hwc; autorewrite with w_rewrite.
  unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  ring.
  intros z; case z.
  autorewrite with w_rewrite; simpl.
  autorewrite with w_rewrite; simpl.
  intros H.
  rewrite Zmod_def_small.
  rewrite wwB_wBwB in H; rewrite wwB_wBwB.
  unfold hh, ll; unfold ww_to_Z; repeat rewrite spec_square_c; auto.
  match goal with |-  _ = ?X =>
    match type of H with _ = ?Y => apply trans_equal with (wB * (Y - Y) + X);
         [pattern Y at 1; rewrite <- H | idtac]; ring
   end end.
  generalize (spec_to_Z op_spec xh); intros HH.
  generalize (spec_ww_to_Z hh); intros HH1.
  rewrite Zmult_1_r; split; auto with zarith.
  apply Zle_lt_trans with ((wwB - 2 * wB + 1) + (wB + 0)); auto with zarith.
  apply Zplus_le_compat_r.
  unfold hh, ww_to_Z; repeat rewrite spec_square_c; auto with arith.
  match goal with |- ?X <= ? Y => assert (0 <= X <= Y) end; auto with zarith.
  rewrite wwB_wBwB; apply Zmult_lt_b; w_solve1.
  assert (1 < wB); auto with zarith.
  intros cc1 cc2 Hwc.
  apply  spec_mul_aux with (cc := (WW cc1 cc2)) (wc := w_op.(znz_1)) (hh := hh) (ll := ll).
  unfold hh; unfold ww_to_Z; apply spec_square_c; auto.
  unfold ll; unfold ww_to_Z; apply spec_square_c; auto.
  generalize Hwc; w_rewrite.
  unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  rewrite (Zmult_comm [|xl|]).
  rewrite wwB_wBwB; clear Hwc; intros Hwc; rewrite <- Hwc; ring.
Qed.

Lemma spec_kara_prod: forall xh xl yh yl hh ll,
   [[hh]] = [|xh|] * [|yh|] ->
   [[ll]] = [|xl|] * [|yl|] ->
   let (wc,cc) :=   match (znz_add_c w_op xh xl)  with
  | C0 xhl =>
      match (znz_add_c w_op yh yl)  with
      | C0 yhl => 
          (znz_0 w_op, ww_sub w_op (ww_sub w_op (znz_mul_c w_op xhl yhl) hh) ll)
      | C1 yhl =>
          match ww_add_c w_op (znz_mul_c w_op xhl yhl) (WW xhl (znz_0 w_op)) with
          | C0 m => (znz_0 w_op, ww_sub w_op (ww_sub w_op m hh) ll)
          | C1 m =>
              match ww_sub_c w_op m hh with
              | C0 mhh =>
                  match ww_sub_c w_op mhh ll with
                  | C0 mhhll => (znz_1 w_op, mhhll)
                  | C1 mhhll => (znz_0 w_op, mhhll)
                  end
              | C1 mhh => (znz_0 w_op, ww_sub w_op mhh ll)
              end
          end
      end
  | C1 xhl =>
      match (znz_add_c w_op yh yl)  with
      | C0 yhl =>
          match ww_add_c w_op (znz_mul_c  w_op xhl yhl) (WW yhl (znz_0 w_op)) with
          | C0 m => (znz_0 w_op, ww_sub w_op (ww_sub w_op m hh) ll)
          | C1 m =>
              match ww_sub_c w_op m hh with
              | C0 mhh =>
                  match ww_sub_c w_op mhh ll with
                  | C0 mhhll => (znz_1 w_op, mhhll)
                  | C1 mhhll => (znz_0 w_op, mhhll)
                  end
              | C1 mhh => (znz_0 w_op, ww_sub w_op mhh ll)
              end
          end
      | C1 yhl =>
          match znz_add_c w_op xhl yhl with
          | C0 suml =>
              match ww_add_c w_op (znz_mul_c w_op xhl yhl) (WW suml (znz_0 w_op)) with
              | C0 m =>
                  match ww_sub_c w_op m hh with
                  | C0 mhh =>
                      match ww_sub_c w_op mhh ll with
                      | C0 mhhll => (znz_1 w_op, mhhll)
                      | C1 mhhll => (znz_0 w_op, mhhll)
                      end
                  | C1 mhh => (znz_0 w_op, ww_sub w_op mhh ll)
                  end
              | C1 m =>
                  match ww_sub_c w_op m hh with
                  | C0 mhh => (znz_1 w_op, ww_sub w_op mhh ll)
                  | C1 mhh =>
                      match ww_sub_c w_op mhh ll with
                      | C0 mhhll => (znz_1 w_op, mhhll)
                      | C1 mhhll => (znz_0 w_op, mhhll)
                      end
                  end
              end
          | C1 suml =>
              match ww_add_c w_op (znz_mul_c w_op xhl yhl) (WW suml (znz_0 w_op)) with
              | C0 m =>
                  match ww_sub_c w_op m hh with
                  | C0 mhh => (znz_1 w_op, ww_sub w_op mhh ll)
                  | C1 mhh =>
                      match ww_sub_c w_op mhh ll with
                      | C0 mhhll => (znz_1 w_op, mhhll)
                      | C1 mhhll => (znz_0 w_op, mhhll)
                      end
                  end
              | C1 m => (znz_1 w_op, ww_sub w_op (ww_sub w_op m hh) ll)
              end
          end
      end
  end in
     [|wc|]*wB*wB + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|].
  intros xh xl yh yl hh ll Hhh Hll.
  assert (U: 0 < wB).
  apply Zlt_trans with 1; auto with zarith.
  assert (U1: 0 < wwB).
  apply Zlt_trans with 1; auto with zarith.
  generalize (spec_to_Z op_spec xh); intros HH.
  generalize (spec_to_Z op_spec yh); intros HH1.
  generalize (spec_to_Z op_spec xl); intros HH2.
  generalize (spec_to_Z op_spec yl); intros HH3.
  generalize (spec_ww_to_Z hh); intros HH4.
  generalize (spec_ww_to_Z ll); intros HH5.
  generalize (spec_add_c op_spec xh xl).
  case (znz_add_c w_op xh xl).
  intros w0 Hw0; simpl in Hw0.
  generalize (spec_add_c op_spec yh yl).
  case (znz_add_c w_op yh yl).
  intros w1 Hw1; simpl in Hw1.
  w_rewrite.
  w_rewrite1.
  rewrite Hw0; rewrite Hw1.
  rewrite (Zmult_0_l); rewrite Zplus_0_l.
  rewrite <- wwB_wBwB; rewrite Zmod_minus; auto with zarith.
  rewrite Zmod_mod; auto with zarith.
  rewrite <- Zmod_minus; auto with zarith.
  rewrite Hhh; rewrite Hll.
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); [ring | rewrite Eq] end.
  apply Zmod_def_small; auto with zarith.
  split; auto with zarith.
  rewrite <- Eq.
  rewrite <- Hw0; rewrite <- Hw1.
   generalize (mult_wwB w0 w1); auto with zarith.
   intro w1; rewrite C1_plus_wB; intros Hw1.
   match goal with |- context [ww_add_c ?X ?Y ?T] =>
      generalize (spec_ww_add_c Y T); case (ww_add_c X Y T)
   end.
  intros z; w_rewrite.
  generalize (spec_ww_to_Z z); intros HH6.
  intro Hz; w_rewrite1; simpl in Hz.
  rewrite <- wwB_wBwB.
  rewrite (Zmult_0_l); rewrite Zplus_0_l.
  rewrite Zmod_minus; auto with zarith.
  rewrite Zmod_mod; auto with zarith.
  rewrite <- Zmod_minus; auto with zarith.
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); [idtac | rewrite Eq] end.
  rewrite Hhh; rewrite Hll.
  rewrite Hz; rewrite Hw0; rewrite Zplus_0_r.
  rewrite (Zmult_comm wB); rewrite <- Zmult_plus_distr_r.
  rewrite (Zplus_comm [|w1|]); rewrite Hw1; ring.
  apply Zmod_def_small; auto with zarith.
  intro z; rewrite C1_plus_wwB; w_rewrite1; intro Hz.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z0 Hz0; simpl in Hz0.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z1 Hz1; simpl in Hz1.
  w_rewrite.
  rewrite Hz1; rewrite Hz0.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  rewrite Hw0; rewrite Hll; rewrite Hhh.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [idtac | pattern Y at 1; rewrite  Hw1]; ring
   end end.
  intro z1; w_rewrite; intro Hz1.
  match goal with |-  ?X = _  =>
    match type of Hz1 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz1]
   end end.
  rewrite Hz0.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  rewrite Hw0.
  rewrite Hll; rewrite Hhh; rewrite wwB_wBwB.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [idtac | pattern Y at 1; rewrite  Hw1]; ring
   end end.
  intro z0; w_rewrite; intros Hz0.
  rewrite Zmult_0_l; rewrite Zplus_0_l.
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); [idtac | rewrite Eq] end.
  match goal with |-  ?X = _  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with ([|w0|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  rewrite Hw0; rewrite Hll; rewrite Hhh; rewrite wwB_wBwB; ring.
  apply Zmod_def_small; auto with zarith.
  split; auto with zarith.
  rewrite <- Eq; auto with zarith.
  generalize (spec_ww_to_Z z0); auto with zarith.
  intro w0; w_rewrite; intro Hw0.
   match goal with |- context [znz_add_c ?X ?Y ?T] =>
      generalize (spec_add_c op_spec Y T);  case (znz_add_c X Y T)
   end.
  intros w1 Hw1; simpl in Hw1.
   match goal with |- context [ww_add_c ?X ?Y ?T] =>
      generalize (spec_ww_add_c Y T); case (ww_add_c X Y T)
   end.
  intro z; w_rewrite; intros Hz; simpl in Hz.
  rewrite Zmult_0_l; rewrite Zplus_0_l.
  rewrite Zmod_minus; auto with zarith.
  rewrite Zmod_mod; auto with zarith.
  rewrite <- Zmod_minus; auto with zarith.
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); [idtac | rewrite Eq] end.
  rewrite Hhh; rewrite Hll; rewrite Hz.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  rewrite Hw1; ring.
  apply Zmod_def_small; auto with zarith.
  split; auto with zarith.
  rewrite <- Eq; generalize (spec_ww_to_Z z); auto with zarith.
  intro z; w_rewrite; intro Hz.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z0 Hz0; simpl in Hz0.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z1 Hz1; simpl in Hz1.
  w_rewrite.
  rewrite Hz1; rewrite Hz0.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  rewrite Hw1; rewrite Hll; rewrite Hhh.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (([|yh|] + [|yl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  rewrite wwB_wBwB; ring.
  intro z1; w_rewrite; intro Hz1.
  match goal with |-  ?X = _  =>
    match type of Hz1 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz1]
   end end.
  rewrite Hz0.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  rewrite Hw1.
  rewrite Hll; rewrite Hhh; rewrite wwB_wBwB.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (([|yh|] + [|yl|]) * (Y - Y) + X);
         [idtac | pattern Y at 1; rewrite  Hw0]; ring
   end end.
  intro z0; w_rewrite; intros Hz0.
  rewrite Zmult_0_l; rewrite Zplus_0_l.
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); [ring | rewrite Eq] end.
  match goal with |-  ?X = _  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  rewrite Hw1; rewrite Hll; rewrite Hhh.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (([|yh|] + [|yl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  rewrite wwB_wBwB; ring.
  apply Zmod_def_small; auto with zarith.
  split; auto with zarith.
  rewrite <- Eq; generalize (spec_ww_to_Z z0); auto with zarith.
  intro w1; w_rewrite; intro Hw1.
   match goal with |- context [znz_add_c ?X ?Y ?T] =>
      generalize (spec_add_c op_spec Y T);  case (znz_add_c X Y T)
   end.
  intros w2 Hw2; simpl in Hw2.
   match goal with |- context [ww_add_c ?X ?Y ?T] =>
      generalize (spec_ww_add_c Y T); case (ww_add_c X Y T)
   end.
  intro z; w_rewrite; intros Hz; simpl in Hz.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z0 Hz0; simpl in Hz0.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z1 Hz1; simpl in Hz1.
  w_rewrite.
  rewrite Hz1; rewrite Hz0; rewrite Hz; rewrite Hw2; rewrite Hhh; rewrite Hll.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  ring.
  intros z1; w_rewrite; intros Hz1.
  match goal with |-  ?X = _  =>
    match type of Hz1 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz1]
   end end.
  rewrite Hz0; rewrite Hz; rewrite Hw2; rewrite Hll; rewrite Hhh; rewrite wwB_wBwB.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  ring.
  intros z0; w_rewrite; intro Hz0.
  rewrite Zmult_0_l; rewrite Zplus_0_l.
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); [idtac | rewrite Eq] end.
  rewrite Hll.
  match goal with |-  ?X = _  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz0]
   end end.
  rewrite Hz; rewrite Hw2.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  rewrite wwB_wBwB; rewrite Hhh; ring.
  apply Zmod_def_small; auto with zarith.
  split; auto with zarith.
  rewrite <- Eq; generalize (spec_ww_to_Z z0); auto with zarith.
  intro z; w_rewrite; intro Hz.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z0 Hz0; simpl in Hz0.
  generalize (spec_ww_to_Z z0); intro HH6.
  w_rewrite.
  match goal with |- ?X + ?Y mod _ = ?Z => assert (Eq: Y = (Z  - 2 * X )) end.
  rewrite Hz0; rewrite Hll; rewrite Hhh.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  rewrite Hw2.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  rewrite wwB_wBwB; ring.
  rewrite Eq.
  rewrite <- Z_mod_plus with (b := 1); auto with zarith.
  rewrite Zmod_def_small; auto with zarith.
  rewrite wwB_wBwB; ring.
  split.
  rewrite <- Eq; auto with zarith.
  assert ([|xh|] * [|yl|] + [|xl|] * [|yh|] < wwB + wwB); auto with zarith.
  apply Zplus_lt_compat; auto with zarith.
  rewrite <- Zmult_assoc; rewrite <- wwB_wBwB; auto with zarith.
  intro z0; w_rewrite; intros Hz0.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z1 Hz1; simpl in Hz1.
  w_rewrite.
  rewrite Hz1.
  match goal with |-  ?X = _  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  rewrite Hll; rewrite Hhh; rewrite Hw2.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  rewrite wwB_wBwB; ring.
  intro z1; w_rewrite; intro Hz1.
  match goal with |-  ?X = _  =>
    match type of Hz1 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz1]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  rewrite Hw2.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  rewrite wwB_wBwB; rewrite Hll; rewrite Hhh; ring.
  intro w2; w_rewrite; intros Hw2.
   match goal with |- context [ww_add_c ?X ?Y ?T] =>
      generalize (spec_ww_add_c Y T); case (ww_add_c X Y T)
   end.
  intro z; w_rewrite; intros Hz; simpl in Hz.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z0 Hz0; simpl in Hz0.
  generalize (spec_ww_to_Z z0); intro HH6.
  w_rewrite.
  match goal with |- ?X + ?Y mod _ = ?Z => assert (Eq: Y = (Z  - 2 * X )) end.
  rewrite Hz0; rewrite Hll; rewrite Hhh.
  rewrite Hz.
  match goal with |-  ?X = _  =>
    match type of Hw2 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw2]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  ring.
  rewrite Eq.
  rewrite <- Z_mod_plus with (b := 1); auto with zarith.
  rewrite Zmod_def_small; auto with zarith.
  rewrite wwB_wBwB; ring.
  split.
  rewrite <- Eq; auto with zarith.
  assert ([|xh|] * [|yl|] + [|xl|] * [|yh|] < wwB + wwB); auto with zarith.
  apply Zplus_lt_compat; auto with zarith.
  rewrite <- Zmult_assoc; rewrite <- wwB_wBwB; auto with zarith.
  intro z1; w_rewrite; intro Hz1.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  intros z0 Hz0; simpl in Hz0.
  w_rewrite.
  rewrite Hz0.
  match goal with |-  ?X = _  =>
    match type of Hz1 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz1]
   end end.
  rewrite Hz; rewrite Hhh; rewrite Hll.
  match goal with |-  ?X = _  =>
    match type of Hw2 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw2]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  rewrite wwB_wBwB; ring.
  intros z0; w_rewrite; intros Hz0.
  match goal with |-  ?X = _  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hz1 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz1]
   end end.
  rewrite Hz; rewrite Hhh; rewrite Hll; rewrite wwB_wBwB.
  match goal with |-  ?X = _  =>
    match type of Hw2 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw2]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  ring.
  intros z; w_rewrite; intros Hz.
  generalize (spec_ww_to_Z z); intro HH6.
  rewrite Zmod_minus; auto with zarith.
  rewrite Zmod_mod; auto with zarith.
  rewrite <- Zmod_minus; auto with zarith.
  match goal with |- ?Z + ?X mod _ = ? Y => assert (Eq: X = Y - 3 * Z); [idtac | rewrite Eq] end.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw2 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw2]
   end end.
  rewrite Hll; rewrite Hhh; rewrite wwB_wBwB.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [idtac | pattern Y at 1; rewrite  Hw1]; ring
   end end.
  rewrite <- Z_mod_plus with (b := 2); auto with zarith.
  rewrite Zmod_def_small; auto with zarith.
  rewrite wwB_wBwB; ring.
  split.
  rewrite <- Eq; auto with zarith.
  assert ([|xh|] * [|yl|] + [|xl|] * [|yh|] < wwB + wwB); auto with zarith.
  apply Zplus_lt_compat; auto with zarith.
  rewrite <- Zmult_assoc; rewrite <- wwB_wBwB; auto with zarith.
Qed.

Theorem spec_ww_karatsuba_c: forall x y, [||ww_karatsuba_c w_op x y||] = [[x]] * [[y]].
  assert (U: 0 < wB).
  apply Zlt_trans with 1; auto with zarith.
  assert (U1: 0 < wwB).
  apply Zlt_trans with 1; auto with zarith.
  intros x y; case x; auto; intros xh xl.
  case y; auto.
  simpl; ring.
  intros yh yl.
  simpl; w_rewrite.
  generalize (spec_kara_prod xh xl yh yl 
                        (znz_mul_c w_op xh yh) (znz_mul_c w_op xl yl)).
  match goal with |- context [znz_add_c ?X ?Y ?Z] => case (znz_add_c X Y Z) end.
  intro w0.
  match goal with |- context [znz_add_c ?X ?Y ?Z] => case (znz_add_c X Y Z) end.
  intros w1 Hw1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
     (ww_sub w_op (ww_sub w_op (znz_mul_c w_op w0 w1) (znz_mul_c w_op xh yh))
                   (znz_mul_c w_op xl yl))
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  rewrite <- Hw1; w_rewrite; auto.
  intros w1.
  match goal with |- context [ww_add_c ?X ?Y ?Z] => case (ww_add_c X Y Z) end.
  intros z Hz.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           (ww_sub w_op (ww_sub w_op z (znz_mul_c w_op xh yh))
                (znz_mul_c w_op xl yl))
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  rewrite <- Hz; w_rewrite; auto.
  intros z.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intros z0.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_1))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z0; w_rewrite; intro Hz0.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           (ww_sub w_op z0 (znz_mul_c w_op xl yl))
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro w0.
  match goal with |- context [znz_add_c ?X ?Y ?Z] => case (znz_add_c X Y Z) end.
  intro w1.
  match goal with |- context [ww_add_c ?X ?Y ?Z] => case (ww_add_c X Y Z) end.
  intros z Hz.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
          (ww_sub w_op (ww_sub w_op z (znz_mul_c w_op xh yh))
            (znz_mul_c w_op xl yl))
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  rewrite <- Hz; w_rewrite; auto.
  intros z.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intros z0.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_1))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z0; w_rewrite; intro Hz0.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           (ww_sub w_op z0 (znz_mul_c w_op xl yl))
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro w1.
  match goal with |- context [znz_add_c ?X ?Y ?Z] => case (znz_add_c X Y Z) end.
  intro w2.
  match goal with |- context [ww_add_c ?X ?Y ?Z] => case (ww_add_c X Y Z) end.
  intros z.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intros z0.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_1))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z0; w_rewrite; intro Hz0.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           (ww_sub w_op z0 (znz_mul_c w_op xl yl))
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intros z.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intro z0; w_rewrite; intro Hz0.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_1))
           (ww_sub w_op z0 (znz_mul_c w_op xl yl))
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intros z0.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_1))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro w2.
  match goal with |- context [ww_add_c ?X ?Y ?Z] => case (ww_add_c X Y Z) end.
  intros z.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intro z0; w_rewrite; intro Hz0.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_1))
           (ww_sub w_op z0 (znz_mul_c w_op xl yl)) 
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z0.
  match goal with |- context [ww_sub_c ?X ?Y ?Z] => case (ww_sub_c X Y Z) end.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_1))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z1; w_rewrite; intro Hz1.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_0))
           z1
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
  intro z; w_rewrite; intro Hz.
  apply (spec_mul_aux xh xl yh yl
                   (w_op.(znz_1))
           (ww_sub w_op (ww_sub w_op z (znz_mul_c w_op xh yh))
             (znz_mul_c w_op xl yl))
           (znz_mul_c w_op xh yh)
           (znz_mul_c w_op xl yl)
           ); w_rewrite; auto.
Qed.

Lemma without_c_prec_c_pos: forall q1, 0 < [|q1|]  -> [|without_c (znz_pred_c w_op q1)|] = [|q1|] - 1.
  intros q2.
  generalize (spec_pred_c op_spec q2); case (znz_pred_c w_op q2); auto.
  intros w0.
  w_rewrite1.
  intros V1 V2; contradict V2; apply Zle_not_lt.
  replace [|q2|] with (([|q2|] - 1) + 1); auto with zarith.
  rewrite <- V1; generalize (spec_to_Z op_spec w0); auto with zarith.
Qed.

(********************************************************************
   Definition of the support function to adjust the result
 ********************************************************************)

Hint Rewrite Zmult_1_r Zmult_0_r Zmult_1_l Zmult_0_l Zplus_0_l Zplus_0_r Zminus_0_r: rm10.
Hint Rewrite Zmult_plus_distr_r Zmult_plus_distr_l Zmult_minus_distr_r Zmult_minus_distr_l: distr.


Theorem  spec_w_carry_pred_c: forall q, 0< [+|q|] ->
 [+|match q with
  | C0 x => C0 (without_c (znz_pred_c w_op x))
  | C1 x =>
    match znz_pred_c w_op x with
    | C0 p => C1 p
    | C1 p => C0 p
    end
  end|] = [+|q|] - 1.
  intro q; case q; intro q1; w_rewrite1; simpl.
  generalize (spec_pred_c op_spec q1); case (znz_pred_c w_op q1); auto.
  intros w0.
  w_rewrite1.
  intros V1 V2; contradict V2; apply Zle_not_lt.
  replace [|q1|] with (([|q1|] - 1) + 1); auto with zarith.
  rewrite <- V1; generalize (spec_to_Z op_spec w0); auto with zarith.
   match goal with |- context [znz_pred_c ?X ?Y] =>
      generalize (spec_pred_c op_spec Y);  case (znz_pred_c X Y)
   end.
  intro w0; w_rewrite1; simpl; auto with zarith.
  intro w0; w_rewrite1; simpl; auto with zarith.
Qed.

Theorem spec_w_carry:  forall q, 0 <= [+|q|].
  intro q; case q; intros q1;   generalize (spec_to_Z op_spec q1); w_rewrite; simpl; auto with zarith.
Qed.

Theorem spec_ww_adjust: 
forall a n (c: nat) q b r,
 0 <= a -> (if c then [[r]] < [[b]] else True) ->
 a = [+|q|] * [[b]] + ([[r]] - (Z_of_nat c) * wwB) -> (Z_of_nat c) * wwB <= [[r]] + (Z_of_nat n) * [[b]] ->
  let (q1, r1) := w_adjust w_op n c q b r in a = [+|q1|] * [[b]] + [[r1]] /\ 0 <= [[r1]] < [[b]].
  assert (U: 0 < wB); auto with zarith.
  apply Zlt_trans with 1; auto with zarith.
  assert (U1: 0 < wwB); auto with zarith.
  apply Zlt_trans with 1; auto with zarith.
  intros a n c q b r Ha; generalize c q r; elim n; clear n c q r; simpl w_adjust.
  intros c q r.
  generalize (spec_ww_to_Z r); intros HH.
  case c.
  simpl; autorewrite with rm10; auto with zarith.
  intros c1; rewrite inj_S; unfold Zsucc.
  autorewrite with distr.
  intros H1 H2 H3; contradict H3; apply Zlt_not_le; simpl Z_of_nat; autorewrite with rm10; auto with zarith.
  assert (0 <= Z_of_nat c1 * wwB); auto with zarith.
  intros n1 Rec c q r; generalize (spec_ww_to_Z r); case c.
  rewrite inj_S; unfold Zsucc; simpl Z_of_nat; autorewrite with rm10; auto with zarith.
  intros c1 _; repeat rewrite inj_S; unfold Zsucc.
  autorewrite with distr rm10.
  intros H1 H2.
  assert (Eq: 0 < [+|q|]).
  case (Zle_lt_or_eq 0 [+|q|]); auto with zarith.
  apply spec_w_carry.
  intro V; contradict Ha; apply Zlt_not_le; rewrite H2; rewrite <- V.
  assert (0 <= Z_of_nat c1 * wwB); auto with zarith.
  autorewrite with rm10; generalize (spec_ww_to_Z r); intros HH; auto with zarith.
  match goal with |- context [ww_add_c ?X ?Y ?T] =>
      generalize (spec_ww_add_c Y T); case (ww_add_c X Y T)
   end.
  intros z Hz; simpl in Hz.
  match goal with |- context [w_adjust ?A ?X ?Y ?Z ?T ?U] =>
     generalize (Rec  Y  Z U); case (w_adjust A X Y Z T U)
  end.
  rewrite inj_S; unfold Zsucc; simpl Z_of_nat; autorewrite with rm10; auto with zarith.
  intros q0 r0 H H3; apply H; auto.
  rewrite spec_w_carry_pred_c; auto with zarith.
  rewrite Hz; rewrite H2; ring.
  autorewrite with distr; auto with zarith.
  intros z; w_rewrite1; rewrite <- wwB_wBwB; intros Hz H3.
  match goal with |- context [w_adjust ?A ?X ?Y ?Z ?T ?U] =>
     generalize (Rec  Y  Z U); case (w_adjust A X Y Z T U)
  end.
  intros c0 z0 H5; apply H5; clear H5; auto with zarith.
  case c1; auto with zarith.
  generalize (spec_ww_to_Z r); intros HH; auto with zarith.
  rewrite spec_w_carry_pred_c; auto with zarith.
  autorewrite with distr; rewrite H2.
  match goal with |-  _ = ?X   =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [pattern Y at 1; rewrite  Hz| idtac]; ring
   end end.
Qed.


  Theorem spec_znz_WW: forall x y, [[znz_WW w_op x y]] = [|x|] * wB  + [|y|].
  intros x y; unfold ww_to_Z; rewrite spec_WW; auto with zarith.
  Qed.
  Hint Rewrite spec_znz_WW: w_rewrite.

  Theorem wB_div_2:  2 * (wB / 2) = wB.
  unfold base.
  assert (2 ^ (Zpos (znz_digits w_op)) = 2 * (2 ^ (Zpos (znz_digits w_op) - 1) )).
  pattern 2 at 2; rewrite <- Zpower_exp_1.
  rewrite <- Zpower_exp; auto with zarith.
  eq_tac; auto with zarith.
  case (znz_digits w_op); compute; intros; discriminate.
  rewrite H.
  eq_tac; auto with zarith.
  rewrite Zmult_comm; apply Z_div_mult; auto with zarith.
  Qed.

  Theorem wwB_div_2: wwB / 2 = wB / 2 * wB.
  rewrite wwB_wBwB.
  pattern wB at 1; rewrite <- wB_div_2; auto.
  rewrite <- Zmult_assoc.
  repeat (rewrite (Zmult_comm 2); rewrite Z_div_mult); auto with zarith.
  Qed.

  Theorem wB_div2: forall x, wB/2  <= x -> wB <= 2 * x.
  intros x H; rewrite <- wB_div_2; apply Zmult_le_compat_l; auto with zarith.
  Qed.

  Theorem spec_ww_split: forall a, [[a]] = [|fst (ww_split w_op a)|] * wB + [|snd(ww_split w_op a)|].
  intros a; case a; w_rewrite1; simpl; w_rewrite; intros; ring.
  Qed.


Theorem   spec_w_div32 : forall a1 a2 a3 b1 b2,
     wB/2 <= [|b1|] ->
     let (q,r) := w_div32 w_op a1 a2 a3 b1 b2 in
     [|a1|] * wwB + [|a2|] * wB  + [|a3|] = [+|q|] *  ([|b1|] * wB + [|b2|])  + [[r]] /\ 0 <= [[r]] < [|b1|] * wB + [|b2|].
  intros a1 a2 a3 b1 b2 H.
  assert (U: 0 < wB); auto with zarith.
  apply Zlt_trans with 1; auto with zarith.
  assert (U1: 0 < wwB); auto with zarith.
  apply Zlt_trans with 1; auto with zarith.
  generalize (spec_to_Z op_spec a1); intros HH.
  generalize (spec_to_Z op_spec a2); intros HH1.
  generalize (spec_to_Z op_spec a3); intros HH2.
  generalize (spec_to_Z op_spec b1); intros HH3. 
  generalize (spec_to_Z op_spec b2); intros HH4. 
  unfold w_div32.
  match goal with |- context  [znz_div21 ?X ?Y ?Z ?T] =>
    generalize (spec_div21 op_spec Y Z T); case (znz_div21 X Y Z T)
  end.
  intros c r; case c.
  intros q1.
  generalize (spec_to_Z op_spec q1); intros HH5.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  w_rewrite; intros z Hz; simpl in Hz.
  generalize (spec_ww_to_Z z); intros HH6.
  intros H1; case H1; auto; clear H1; intros H1 H2.
  match goal with |- context [w_adjust ?A ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_ww_adjust ([|a1|] * wwB + [|a2|] * wB + [|a3|]) X Y Z T U); case (w_adjust A X Y Z T U) 
  end.
  simpl; w_rewrite1.
  intros q2 r2 H3.
  generalize (spec_w_carry q2); intros HH7.
  generalize (spec_ww_to_Z r2); intros HH8.
  case H3; auto with zarith.
  rewrite Hz.
  assert (0 <= [|q1|] * [|b2|]); auto with zarith.
  match goal with |- ?X + ?Y - ?Z < ?T => apply Zle_lt_trans with (X + Y); auto with zarith end.
  repeat (rewrite (fun x => Zmult_comm x wB)); apply wB_lex_inv; auto with zarith.
  rewrite Hz; rewrite  Zmult_assoc; rewrite <- Zmult_plus_distr_l.
  rewrite H1; simpl; ring.
  intro z; w_rewrite1; intros Hz; simpl in Hz.
  generalize (spec_ww_to_Z z); intros HH6.
  intros H1; case H1; auto; clear H1; intros H1 H2; simpl in H1.
  match goal with |- context [w_adjust ?A ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_ww_adjust ([|a1|]  * wwB + [|a2|] * wB + [|a3|]) X Y Z T U); case (w_adjust A X Y Z T U) 
  end.
  simpl Z_of_nat; autorewrite with rm10.
  w_rewrite1.
  intros q2 r2 H3.
  generalize (spec_w_carry q2); intros HH7.
  generalize (spec_ww_to_Z r2); intros HH8.
  case H3; auto with zarith.
  rewrite Hz; simpl.
  rewrite  Zmult_assoc; rewrite <- Zmult_plus_distr_l; rewrite H1; ring.
  autorewrite with distr; rewrite Zmult_assoc.
  assert (wB * wB <= 2 * [|b1|] * wB); auto with zarith.
  apply Zmult_le_compat_r; auto with zarith.
  apply wB_div2; auto.
  intros q1.
  generalize (spec_to_Z op_spec q1); intros HH5.
  w_rewrite1.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  w_rewrite; intros z Hz; simpl in Hz.
  generalize (spec_ww_to_Z z); intros HH6.
  intros H1; case H1; auto; clear H1; intros H1 H2.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  w_rewrite.
  intros z0 Hz0; simpl in Hz0.
  generalize (spec_ww_to_Z z0); intros HH7.
  match goal with |- context [w_adjust ?A ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_ww_adjust ([|a1|] * wwB + [|a2|] * wB + [|a3|]) X Y Z T U); case (w_adjust A X Y Z T U) 
  end.
  w_rewrite1; simpl.
  intros q2 r2 H3.
  generalize (spec_w_carry q2); intros HH8.
  generalize (spec_ww_to_Z r2); intros HH9.
  case H3; auto with zarith.
  rewrite Hz0; rewrite Hz.
  assert (0 <= [|q1|] * [|b2|]); auto with zarith.
  assert (0 <= [|b2|] * wB); auto with zarith.
  match goal with |- ?X - ?Y - ?Z < ?T => apply Zle_lt_trans with X; auto with zarith end.
  repeat (rewrite (fun x => Zmult_comm x wB)); apply wB_lex_inv; auto with zarith.
  rewrite Hz0; rewrite Hz; rewrite  Zmult_assoc; rewrite <- Zmult_plus_distr_l.
  rewrite H1; simpl; ring.
  intro z0; w_rewrite1; intros Hz0.
  generalize (spec_ww_to_Z z0); intros HH7.
  match goal with |- context [w_adjust ?A ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_ww_adjust ([|a1|]  * wwB + [|a2|] * wB + [|a3|]) X Y Z T U); case (w_adjust A X Y Z T U) 
  end.
  intros q2 r2; w_rewrite1; intros H3.
  generalize (spec_w_carry q2); intros HH8.
  generalize (spec_ww_to_Z r2); intros HH9.
  case H3; auto with zarith.
  simpl Z_of_nat; autorewrite with rm10.
  rewrite  Zmult_assoc; rewrite <- Zmult_plus_distr_l; rewrite H1.
  match goal with |-  _ = ?X  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [pattern Y at 1; rewrite  Hz0 | ring]
   end end.
  rewrite Hz; ring.
  simpl Z_of_nat.
  autorewrite with distr; rewrite Zmult_assoc.
  assert (wB * wB <= 2 * [|b1|] * wB); auto with zarith.
  apply Zmult_le_compat_r; auto with zarith.
  apply wB_div2; auto.
  autorewrite with rm10.
  autorewrite with distr; rewrite Zmult_assoc.
  assert (wB * wB <= 2 * [|b1|] * wB); auto with zarith.
  intros z; autorewrite with w_rewrite; intros Hz.
  match goal with |- context [ww_sub_c ?X ?Y ?T] =>
      generalize (spec_ww_sub_c Y T); case (ww_sub_c X Y T)
   end.
  w_rewrite.
  intro z0; w_rewrite; intros Hz0; simpl in Hz0.
  intros H1; case H1; clear H1; auto; intros H1 H2.
  generalize (spec_ww_to_Z z0); intros HH7.
  match goal with |- context [w_adjust ?A ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_ww_adjust ([|a1|]  * wwB + [|a2|] * wB + [|a3|]) X Y Z T U); case (w_adjust A X Y Z T U) 
  end.
  intros q2 r2; w_rewrite1; intros H3.
  generalize (spec_w_carry q2); intros HH8.
  generalize (spec_ww_to_Z r2); intros HH9.
  case H3; auto with zarith.
  simpl Z_of_nat; autorewrite with rm10.
  rewrite  Zmult_assoc; rewrite <- Zmult_plus_distr_l; rewrite H1.
  rewrite Hz0.
  match goal with |-  _ = ?X  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [pattern Y at 1; rewrite  Hz | ring]
   end end.
  w_rewrite1; ring.
  simpl Z_of_nat; autorewrite with rm10.
  autorewrite with distr; rewrite Zmult_assoc.
  assert (wB * wB <= 2 * [|b1|] * wB); auto with zarith.
  apply Zmult_le_compat_r; auto with zarith.
  apply wB_div2; auto.
  intro z0; w_rewrite; intros Hz0; simpl in Hz0.
  intros H1; case H1; clear H1; auto; intros H1 H2.
  generalize (spec_ww_to_Z z0); intros HH7.
  match goal with |- context [w_adjust ?A ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_ww_adjust ([|a1|]  * wwB + [|a2|] * wB + [|a3|]) X Y Z T U); case (w_adjust A X Y Z T U) 
  end.
  intros q2 r2; w_rewrite1; intros H3.
  generalize (spec_w_carry q2); intros HH8.
  generalize (spec_ww_to_Z r2); intros HH9.
  case H3; auto with zarith.
  simpl Z_of_nat; autorewrite with rm10.
  rewrite  Zmult_assoc; rewrite <- Zmult_plus_distr_l; rewrite H1.
  match goal with |-  _ = ?X  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [pattern Y at 1; rewrite  Hz0 | ring]
   end end.
  match goal with |-  _ = ?X  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [pattern Y at 1; rewrite  Hz | ring]
   end end.
  w_rewrite1; ring.
  simpl Z_of_nat; autorewrite with rm10.
  autorewrite with distr; rewrite Zmult_assoc.
  assert (2 * wB * wB <= 4 * ([|b1|] * wB)); auto with zarith.
  rewrite Zmult_assoc; apply Zmult_le_compat_r; auto with zarith.
   replace 4 with (2 * 2); auto with zarith.
  rewrite <- Zmult_assoc; apply Zmult_le_compat_l; auto with zarith.
  apply wB_div2; auto.
  Qed.

  Theorem wwB_div: wwB  = 2 * (wwB / 2).
  rewrite wwB_div_2; rewrite  Zmult_assoc; rewrite  wB_div_2; auto.
  apply wwB_wBwB.
  Qed.

  Theorem   spec_ww_div21 : forall a1 a2 b,
     wwB/2 <= [[b]] ->
     let (q,r) := ww_div21 w_op a1 a2 b in
     [[a1]] *wwB+[[a2]] = [+[q]] *  [[b]] + [[r]] /\ 0 <= [[r]] < [[b]].
  assert (U: 0 < wB); auto with zarith.
  apply Zlt_trans with 1; auto with zarith.
  assert (U1: 0 < wwB); auto with zarith.
  apply Zlt_trans with 1; auto with zarith.
  intros a b c H; unfold ww_div21.
  generalize (spec_ww_to_Z c); intros HH0.
  assert (Eq: 0 < [[c]]).
  apply Zmult_lt_reg_r with 2; auto with zarith.
  autorewrite with rm10; rewrite Zmult_comm.
  apply Zlt_le_trans with wwB; auto with zarith.
  rewrite wwB_div; auto with zarith.
  case a.
  case b.
  simpl; autorewrite with rm10; split; auto with zarith.
  intros a1 a2.
  generalize (spec_to_Z op_spec a1); intros HH.
  generalize (spec_to_Z op_spec a2); intros HH1.
  match goal with |-context [ww_compare ?X ?Y ?Z] =>
    generalize (spec_ww_compare Y Z); case (ww_compare X Y Z)
  end.
  simpl; w_rewrite1; autorewrite with rm10; auto with zarith.
  simpl; w_rewrite1; autorewrite with rm10; auto with zarith.
  simpl; w_rewrite1; autorewrite with rm10; auto with zarith.
  assert (Eq1: wB * [|a1|] + [|a2|] < wwB); auto with zarith.
  generalize (spec_ww_to_Z (WW a1 a2)); simpl; auto with zarith.
  intros H1; rewrite Zmod_def_small; auto with zarith.
  split; auto with zarith.
  split; auto with zarith.
  assert (wB * [|a1|] + [|a2|] < 2 * [[c]]); auto with zarith.
  apply Zlt_le_trans with (1:= Eq1).
  rewrite wwB_div; auto with zarith.
  split; auto with zarith.
  rewrite <- wwB_wBwB; auto with zarith.
  intros a1 a2.
  generalize (spec_to_Z op_spec a1); intros HH.
  generalize (spec_to_Z op_spec a2); intros HH1.
  match goal with |- context [ww_split ?X ?Y] =>
    generalize (spec_ww_split Y); case (ww_split X Y)
  end.
  intros a3 a4; simpl fst; simpl snd; intros Hb.
  generalize (spec_to_Z op_spec a3); intros HH2.
  generalize (spec_to_Z op_spec a4); intros HH3.
  match goal with |- context [ww_split ?X ?Y] =>
    generalize (spec_ww_split Y); case (ww_split X Y)
  end.
  intros b1 b2; simpl fst; simpl snd; intros Hc.
  generalize (spec_to_Z op_spec b1); intros HH4.
  generalize (spec_to_Z op_spec b2); intros HH5.
  match goal with |-context [w_div32 ?K ?X ?Y ?Z ?T ?U] =>
    generalize (spec_w_div32 X Y Z T U); case (w_div32 K X Y Z T U)
  end.
  assert (Eq1: wB / 2 <= [|b1|]).
  apply (@wB_lex  (wB / 2) 0 [|b1|] [|b2|]); auto with zarith.
  autorewrite with rm10; repeat rewrite (Zmult_comm wB).
  rewrite <- wwB_div_2; rewrite <- Hc; auto with zarith.
  intros q1 r V1; case V1; clear V1; try intros V1 V2; auto. 
  match goal with |- context [ww_split ?X ?Y] =>
    generalize (spec_ww_split Y); case (ww_split X Y)
  end.
  intros r1 r2; simpl fst; simpl snd; intros Hr.
  match goal with |-context [w_div32 ?K ?X ?Y ?Z ?T ?U] =>
    generalize (spec_w_div32 X Y Z T U); case (w_div32 K X Y Z T U)
  end.
  intros q2 s V3; case V3; clear V3; auto; intros V3 V4.
  assert (Eq2: [|without_c q2|] = [+|q2|]).
  generalize V3; case q2; auto; clear V3.
  intros w0; w_rewrite1; intros V3.
  case V2; clear V2; intros _ V5; contradict V5; apply Zle_not_lt.
  rewrite Hr.
  assert (Eq2: 0 <= [|snd (ww_split w_op s)|] <= [[s]]).
  case s; simpl; w_solve1.
  intros w1 w2; generalize (spec_to_Z op_spec w1); intros WW.
  assert (0 <= wB * [|w1|]); auto with zarith.
  generalize (spec_to_Z op_spec w2); auto with zarith.
  match goal with |- ?X <= ?Y =>
    apply (@beta_lex  X  [|snd (ww_split w_op s)|] Y [|a4|] wB) ; auto with zarith
  end.
  repeat (rewrite (Zmult_comm wB)); autorewrite with distr.
  generalize (spec_to_Z op_spec w0); intros HH6.
  repeat rewrite <- Zmult_assoc; rewrite V3; w_rewrite.
  assert (0 <= [|b1|] * wB * [|w0|] + [|b2|] * [|w0|]); auto with zarith.
  rewrite (Zmult_comm (wB + [|w0|])); autorewrite with distr.
  repeat (rewrite Zmult_assoc || rewrite Zplus_assoc); auto with zarith.
  apply (spec_to_Z op_spec (snd (ww_split w_op s))).
  generalize V1; case q1; clear V1.
  intros Q V1; simpl; w_rewrite1; rewrite Eq2.
  simpl in V1.
  split; auto with zarith.
  rewrite Hb; rewrite Hc.
  match goal with |-  _ = ?X  =>
    match type of V1 with _ = ?Y => apply trans_equal with (wB *  (Y - Y) + X);
         [pattern Y at 1; rewrite  <- V1 | ring]
   end end.
  match goal with |-  _ = ?X  =>
    match type of V3 with _ = ?Y => apply trans_equal with ( (Y - Y) + X);
         [pattern Y at 1; rewrite  <- V3 | ring]
   end end.
  rewrite wwB_wBwB; rewrite Hr; ring.
  intros Q;  w_rewrite; simpl; w_rewrite1; intros V1; rewrite Eq2.
  split; auto with zarith.
  rewrite Hb; rewrite Hc.
  match goal with |-  _ = ?X  =>
    match type of V1 with _ = ?Y => apply trans_equal with (wB *  (Y - Y) + X);
         [pattern Y at 1; rewrite  <- V1 | ring]
   end end.
  match goal with |-  _ = ?X  =>
    match type of V3 with _ = ?Y => apply trans_equal with ( (Y - Y) + X);
         [pattern Y at 1; rewrite  <- V3 | ring]
   end end.
  rewrite wwB_wBwB; rewrite Hr; ring.
  Qed.

  Let digits :=  znz_digits w_op.
  Let wdigits := xO (znz_digits w_op).

  Theorem wB_power: wB = 2 ^ (Zpos digits).
  unfold base.
  trivial.
  Qed.

  Theorem wwB_power: wwB = 2 ^ (Zpos wdigits).
   trivial.
   Qed.
 
Theorem Zpower_lt_monotone: forall a b c: Z, 1 < a -> 0 <= b < c -> a ^ b < a ^
 c.
intros a b c H (H1, H2).
rewrite <- (Zmult_1_r (a ^ b)); replace c with (b + (c - b)); auto with zarith.
rewrite Zpower_exp; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
assert (0 < a ^ (c - b)); auto with zarith.
apply Zlt_le_trans with (a ^1); auto with zarith.
rewrite Zpower_exp_1; auto with zarith.
apply Zpower_le_monotone; auto with zarith.
Qed.

Theorem nat_of_P_xO: 
  forall p,  nat_of_P (xO p) =  (2 * nat_of_P p)%nat.
  intros p; unfold nat_of_P; simpl; rewrite Pmult_nat_2_mult_2_permute; auto with arith.
Qed.

Theorem nat_of_P_xI: 
  forall p,  nat_of_P (xI p) =  (2 * nat_of_P p + 1)%nat.
  intros p; unfold nat_of_P; simpl; rewrite Pmult_nat_2_mult_2_permute; auto with arith.
  rewrite S_to_plus_one;  ring.
Qed.

Theorem nat_of_P_xH: nat_of_P xH = 1%nat.
  trivial.
  Qed.


Hint Rewrite
  nat_of_P_xO nat_of_P_xI nat_of_P_xH
  nat_of_P_succ_morphism
  nat_of_P_plus_carry_morphism
  nat_of_P_plus_morphism
  nat_of_P_mult_morphism
  nat_of_P_minus_morphism: pos_morph.

Ltac pos_tac :=
  match goal with |- ?X = ?Y => 
    assert (tmp: Zpos X = Zpos Y); 
     [idtac; repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P; eq_tac | injection tmp; auto]
  end; autorewrite with pos_morph.

  Theorem Zmult_lt_compat_bis:
      forall n m p q : Z, 0 <= n < p -> 0 <= m < q -> n * m < p * q.
  intros n m p q (H1, H2) (H3,H4).
  case Zle_lt_or_eq with (1 := H1); intros H5; auto with zarith.
  case Zle_lt_or_eq with (1 := H3); intros H6; auto with zarith.
  apply Zlt_trans with (n * q).
  apply Zmult_lt_compat_l; auto.
  apply Zmult_lt_compat_r; auto with zarith.
  rewrite <- H6; autorewrite with rm10; apply Zmult_lt_0_compat; auto with zarith.
  rewrite <- H5; autorewrite with rm10; apply Zmult_lt_0_compat; auto with zarith.
  Qed.

Axiom ok: forall P, P.

  Theorem spec_ww_head0  : forall x,  0 < [[x]] -> wwB/ 2 <= 2 ^ (Z_of_N (ww_head0 w_op x)) * [[x]] < wwB. 
  intros x; case x; simpl. 
  intros H; contradict H; auto with zarith.
  intros xh xl H.
  generalize (spec_to_Z op_spec xh); intros HH; rewrite wB_power in HH.
  generalize (spec_to_Z op_spec xl); intros HH1; rewrite wB_power in HH1.
  assert (Hl := spec_compare op_spec xh (znz_0 w_op));
  destruct (znz_compare w_op xh (znz_0 w_op)).
  generalize Hl; w_rewrite1; clear Hl; intros Hl.
  generalize H; rewrite Hl; autorewrite with rm10; clear H; intros H.
  assert (Hl1 := spec_znz_head0 op_spec xl);
  destruct (znz_head0 w_op xl).
  simpl in Hl1; rewrite Zmult_1_l in Hl1.
  generalize (wB_power); simpl; unfold digits; intros tmp; rewrite <-tmp; clear tmp.
  split; auto with zarith.
  rewrite <- wwB_wBwB; rewrite wwB_div_2; rewrite Zmult_comm.
  apply Zmult_le_compat_l; auto with zarith.
  apply Zmult_lt_compat_l; auto with zarith.
  simpl; simpl in Hl1.
  replace (Zpower_pos 2 (znz_digits w_op + p)) with (wB * (Zpower_pos 2 p)).
  rewrite <- Zmult_assoc; split; auto with zarith.
  rewrite <- wwB_wBwB; rewrite wwB_div_2; rewrite Zmult_comm.
  apply Zmult_le_compat_l; auto with zarith.
  rewrite wB_power; auto with zarith.
  apply Zmult_lt_compat_l; auto with zarith.
  rewrite wB_power; auto with zarith.
  rewrite wB_power; simpl.
  generalize (Zpower_exp 2 (Zpos digits) (Zpos p)); simpl; auto with zarith.
  intros tmp; rewrite <- tmp; auto with zarith.
  generalize Hl; w_rewrite1; clear Hl; intros Hl; contradict Hl; auto with zarith.
  generalize Hl; w_rewrite1; clear Hl; intros Hl.
  assert (Hl1 := spec_znz_head0 op_spec xh);  destruct (znz_head0 w_op xh).
  simpl in Hl1; rewrite Zmult_1_l in Hl1.
  simpl; rewrite Zmult_1_l.
  split; auto with zarith.
  apply Zle_trans with (wB * [|xh|]); auto with zarith.
  rewrite <- wwB_wBwB; rewrite wwB_div_2; rewrite Zmult_comm.
  apply Zmult_le_compat_l; auto with zarith.
  rewrite <- (Zplus_0_r (wB * wB));  apply wB_lex_inv; auto with zarith.
  simpl Z_of_N in Hl1;  simpl Z_of_N.
  split; auto with zarith.
  apply Zle_trans with (wB * (2 ^Zpos p * [|xh|])); auto with zarith.
  rewrite <- wwB_wBwB; rewrite wwB_div_2; rewrite Zmult_comm.
  apply Zmult_le_compat_l; auto with zarith.
  rewrite wB_power; auto with zarith.
  rewrite Zmult_assoc; rewrite (Zmult_comm wB); rewrite <- Zmult_assoc.
  apply Zmult_le_compat_l; auto with zarith.
  assert (Eq1: 2 ^ Zpos p  < wB).
  rewrite <- (Zmult_1_r (2 ^ Zpos p)); apply Zle_lt_trans with (2 ^Zpos p * [|xh|]); auto with zarith.
  assert (Eq2: Zpos p < Zpos digits).
  case (Zle_or_lt (Zpos digits) (Zpos p)); auto with zarith; intros H1.
  contradict  Eq1; apply Zle_not_lt.
  rewrite wB_power; apply Zpower_le_monotone; auto with zarith.
  pattern wB at 2; replace wB with (2 ^ Zpos p * 2 ^ (Zpos digits - Zpos p)).
  rewrite <- Zmult_assoc; apply Zmult_lt_compat_l; auto with zarith.
  rewrite (fun x => Zmult_comm x wB).
  rewrite <- (Zplus_0_r (wB * 2 ^ (Zpos digits - Zpos p)));  apply wB_lex_inv; auto with zarith.
  apply Zmult_lt_reg_r with (2 ^ Zpos p); auto with zarith.
  repeat rewrite (fun x => Zmult_comm x (2 ^ Zpos p)).
  rewrite <- Zpower_exp; auto with zarith.
  assert (tmp: forall x y , x + (y - x) = y); try rewrite tmp; auto with zarith; clear tmp.
  rewrite <- wB_power; auto with zarith.
  rewrite wB_power; auto with zarith.
  rewrite <- Zpower_exp; auto with zarith.
  assert (tmp: forall x y , x + (y - x) = y); try rewrite tmp; auto with zarith; clear tmp.
 Qed.

 Theorem spec_ww_add_mul_div : forall x y p,
       0 < Zpos p < Zpos wdigits ->
       [[ ww_add_mul_div w_op x y p]] =
	 ([[x]] * (2 ^ (Zpos p)) + [[y]] / (2 ^ (Zpos wdigits - (Zpos p)))) mod wwB.
  assert (U: 0 < wB); auto with zarith.
  apply Zlt_trans with 1; auto with zarith.
  assert (U1: 0 < wwB); auto with zarith.
  apply Zlt_trans with 1; auto with zarith.
  assert (U2:Zpos digits < Zpos wdigits).
  unfold wdigits, digits, base; rewrite Zpos_xO; auto with zarith.
  assert (1 <= Zpos (znz_digits w_op)); auto with zarith.
  case (znz_digits w_op); compute; auto; intros; discriminate.
  assert (U3:2 ^ (Zpos digits) < 2 ^ (Zpos wdigits)).
  assert (Zdiv_lt_0: forall a b, 0 <= a < b -> a / b = 0).
  intros a b H; apply sym_equal; apply Zdiv_unique with a; auto with zarith.
  apply Zpower_lt_monotone; auto with zarith.
  assert (U4: Zpos wdigits = 2 * Zpos digits).
  replace wdigits with (xO digits);  auto; rewrite Zpos_xO.
  assert (U5: Zpos wdigits = Zpos digits + Zpos digits); auto with zarith.
  assert (Zdiv_lt_0: forall a b, 0 <= a < b -> a / b = 0).
  intros a b H; apply sym_equal; apply Zdiv_unique with a; auto with zarith.
  intros x y p Hp.
  assert (U6: Zpos wdigits = Zpos (wdigits - p) + Zpos p).
  repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P; autorewrite with pos_morph; auto with zarith.
  rewrite inj_minus1; auto with zarith.
  match goal with |- (?X <= ?Y)%nat =>
    case (le_or_lt X Y); auto; intro tmp; absurd (Z_of_nat X < Z_of_nat Y); 
        try apply Zle_not_lt; auto with zarith
  end.
  repeat rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
  assert (Zpos wdigits > Zpos p); auto with zarith.
  case x; simpl ww_add_mul_div.
  case y; simpl.
  rewrite Zdiv_0; try rewrite Zmod_def_small; auto with zarith.
  case Hp; clear Hp; intros Hp0 Hp1.
  match goal with |- context [(?X ?= ?Y)%positive Eq] => case_eq (Pcompare X Y Eq) end; intros H1;
   auto with zarith.
  absurd (Zpos wdigits < Zpos wdigits); auto with zarith.
  apply Zlt_trans with (2 := Hp1); auto.
  intros xh xl.
  generalize (spec_to_Z op_spec xh); intros HH; rewrite wB_power in HH.
  generalize (spec_to_Z op_spec xl); intros HH1; rewrite wB_power in HH1.
  match goal with |- context [(?X ?= ?Y)%positive Eq] => case_eq (Pcompare X Y Eq) end; intros H1;
   auto with zarith.
  match goal with |- context [(?X ?= ?Y)%positive Eq] => case_eq (Pcompare X Y Eq) end; intros H2;
   auto with zarith.
  absurd (Zpos p < Zpos p); auto with zarith.
  pattern p at 2; rewrite <- Pcompare_Eq_eq with (1:= H2); auto with zarith.
  absurd (Zpos wdigits < Zpos digits); auto with zarith.
  unfold digits; rewrite <- Pcompare_Eq_eq with (1:= H1); auto with zarith.
  rewrite wwB_power.
  w_rewrite1; autorewrite with rm10.
  rewrite wB_power;  replace (wdigits - p)%positive  with digits; auto with zarith.
  rewrite Zmult_comm; rewrite Zplus_comm; rewrite Z_div_plus; auto with zarith.
  rewrite Zdiv_lt_0; autorewrite with rm10; auto with zarith.
  rewrite Zmod_def_small; auto with zarith.
  unfold wdigits, digits; rewrite <- Pcompare_Eq_eq with (1:= H1).
  pos_tac; auto with zarith.
  assert (Zpos (xO p) > Zpos p); auto; rewrite Zpos_xO; auto with zarith.
  match goal with |- context [(?X ?= ?Y)%positive Eq] => case_eq (Pcompare X Y Eq) end; intros H2;
   auto with zarith.
  absurd (Zpos p < Zpos p); auto with zarith.
  pattern p at 2; rewrite <- Pcompare_Eq_eq with (1:= H2); auto with zarith.
  absurd (Zpos p < Zpos p); auto with zarith.
  apply Zlt_trans with (Zpos digits); auto.
  apply Zlt_trans with (1 := U2); auto.
  assert (Eq1: Zpos p < Zpos digits); auto with zarith.
  assert (Eq2: Zpos wdigits > Zpos p); auto with zarith.
  assert (Eq3: Zpos (wdigits - p) = Zpos digits + (Zpos digits - Zpos p)).
  repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P; autorewrite with pos_morph; auto with zarith.
  rewrite inj_minus1; auto with zarith.
  replace wdigits with (xO digits);  auto.
  autorewrite with pos_morph; simpl.
  repeat rewrite inj_plus; simpl; ring.
  match goal with |- (?X <= ?Y)%nat =>
    case (le_or_lt X Y); auto; intro tmp; absurd (Z_of_nat X < Z_of_nat Y); 
        try apply Zle_not_lt; auto with zarith
  end.
  repeat rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
  rewrite wwB_power.
  w_rewrite1; autorewrite with rm10. 
  rewrite (spec_add_mul_div op_spec); auto with zarith.
  w_rewrite1; autorewrite with rm10. 
  rewrite wB_power.
  repeat rewrite Zmod_def_small; auto with zarith.
  fold digits.
  apply Zdiv_unique with (2 ^ (Zpos digits) * ([|xh|] mod (2 ^(Zpos digits - Zpos p))) + [|xl|]); auto with zarith.
  split; auto with zarith.
  apply Zplus_le_0_compat; try apply Zmult_le_0_compat; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end; auto with zarith.
  match goal with H: (0 <= ?Y < ?Z) |- ?X + ?Y < _ =>  
    apply Zlt_le_trans with (X + Z) 
  end; auto with zarith.
  pattern (2 ^Zpos digits) at 2; rewrite <- Zmult_1_r.
  rewrite <- Zmult_plus_distr_r.
  rewrite Eq3; rewrite Zpower_exp; auto with zarith.
  apply Zmult_le_compat_l; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end; auto with zarith.
  rewrite Eq3; rewrite Zpower_exp; auto with zarith.
  repeat rewrite <- Zmult_assoc; rewrite Zplus_assoc; rewrite <- Zmult_plus_distr_r.
  rewrite <- Z_div_mod_eq; auto with zarith.
  split; auto with zarith.
  apply Zle_lt_trans with  (2 ^ (Zpos wdigits) / (2 ^(Zpos (wdigits  - p)))); auto with zarith.
  apply Zge_le; apply Z_div_ge; auto with zarith.
 generalize (spec_ww_to_Z (WW xh xl)); intros V1.
  simpl in V1; rewrite wwB_power in V1; rewrite wB_power in V1; auto with zarith.
  rewrite <- Zdiv_unique with (q:= 2 ^(Zpos p)) (r := 0); auto with zarith.
  apply Zpower_lt_monotone; auto with zarith.
  rewrite <- Zpower_exp; auto with zarith.
  autorewrite with rm10; eq_tac; auto with zarith.
  fold digits; auto with zarith.
  split; auto with zarith.
  apply Zle_lt_trans with [|xh|]; auto with zarith.
  case (Zle_lt_or_eq 0 [|xh|]); auto with zarith; intros V1.
  apply Zlt_le_weak; apply Z_div_lt; auto with zarith.
  apply Zle_ge; pattern 2 at 1; rewrite <- Zpower_exp_1; try apply Zpower_le_monotone; auto with zarith.
  rewrite <- V1; rewrite Zdiv_0; auto with zarith.
  assert (Eq1: Zpos p > Zpos digits); auto with zarith.
  match goal with |- context [(?X ?= ?Y)%positive Eq] => case_eq (Pcompare X Y Eq) end; intros H2;
   auto with zarith.
  case Hp; intros Hp1 Hp2; contradict Hp2; apply Zle_not_lt.
  unfold digits; rewrite <- Pcompare_Eq_eq with (1:= H2); auto with zarith.
  case Hp; intros Hp1 Hp2; contradict Hp2; apply Zle_not_lt; auto with zarith.
  apply Zlt_le_weak; auto.
  assert (Eq2: Zpos wdigits > Zpos p); auto with zarith.
  assert (Eq3: Zpos (p - digits) < Zpos digits). 
  repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P; autorewrite with pos_morph; auto with zarith.
  repeat rewrite inj_minus1; auto with zarith.
  repeat rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
  match goal with |- (?X <= ?Y)%nat =>
    case (le_or_lt X Y); auto; intro tmp; absurd (Z_of_nat X < Z_of_nat Y); 
        try apply Zle_not_lt; auto with zarith
  end.
  repeat rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
  w_rewrite.
  repeat rewrite (spec_add_mul_div op_spec); autorewrite with rm10; auto with zarith.
  2: split; auto; compute; auto.
  2: split; auto; compute; auto.
  rewrite wB_power; rewrite wwB_power; fold digits.
  w_rewrite1; autorewrite with rm10.
  assert (Eq4: Zpos (wdigits - p) = Zpos digits - Zpos(p - digits)).
  repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P; autorewrite with pos_morph; auto with zarith.
  repeat rewrite inj_minus1; auto with zarith.
  replace wdigits with (xO digits);  auto.
  autorewrite with pos_morph; simpl.
  repeat rewrite inj_plus; simpl; ring.
  match goal with |- (?X <= ?Y)%nat =>
    case (le_or_lt X Y); auto; intro tmp; absurd (Z_of_nat X < Z_of_nat Y); 
        try apply Zle_not_lt; auto with zarith
  end.
  repeat rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
  match goal with |- (?X <= ?Y)%nat =>
    case (le_or_lt X Y); auto; intro tmp; absurd (Z_of_nat X < Z_of_nat Y); 
        try apply Zle_not_lt; auto with zarith
  end.
  repeat rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
  rewrite <- Eq4.
  rewrite Zmod_def_small with (n := 2 ^Zpos wdigits); auto with zarith.
  2: split; auto with zarith.
  2: apply Zle_lt_trans with (2 ^  Zpos wdigits / (2 ^Zpos (wdigits - p))); auto with zarith.
  2: apply Zge_le; apply Z_div_ge; auto with zarith.
  2: generalize (spec_ww_to_Z (WW xh xl)); intro V1; simpl in V1; rewrite wwB_power in V1; 
      rewrite wB_power in V1; auto with zarith.
  2: pattern (Zpos wdigits) at 1; replace (Zpos wdigits) with (Zpos p + Zpos (wdigits - p)); auto with zarith.
  2: rewrite Zpower_exp; auto with zarith.
  2: rewrite Z_div_mult; auto with zarith.
  2: apply Zpower_lt_monotone; auto with zarith.
  rewrite Zmod_def_small.
  2: split; auto with zarith.
  2: case (Zle_lt_or_eq 0 [|xh|]); auto with zarith; intro V1.
  2: apply Zlt_trans with [|xh|]; auto with zarith.
  2: apply Z_div_lt; auto with zarith.
  2: pattern 2 at 2; rewrite <- Zpower_exp_1; apply Zle_ge; apply Zpower_le_monotone; auto with zarith.
  2: rewrite <- V1; rewrite Zdiv_0; auto with zarith.
  rewrite Z_div_mod_eq with (a := [|xh|] * 2 ^ Zpos (p - digits)) (b := 2 ^Zpos digits); auto with zarith.
  rewrite <- Zplus_assoc.
  match goal with |- context [ ((?X * ?Y) + ?Z) mod ?X] =>
     replace ((X * Y) + Z) with (Z + (Y * X)); [rewrite Z_mod_plus| ring];
     auto with zarith
   end;  auto with zarith.
  rewrite Zmod_def_small; auto with zarith.
  rewrite <- Zdiv_Zmult_compat_l with (c:= 2 ^ (Zpos (p - digits))); auto with zarith.
  rewrite <- Zpower_exp; auto with zarith.
  rewrite Eq4.
  assert (tmp: forall x y, x + (y - x) = y); try rewrite tmp; auto with zarith; clear tmp.
  rewrite <- Eq4.
  rewrite (Zmult_comm [|xh|]).
  rewrite (fun x => Zmult_comm x (2 ^ Zpos digits)); auto with zarith.
  rewrite Zplus_assoc.
  rewrite <- Z_div_mod_eq; auto with zarith.
  replace (Zpos digits) with (Zpos (wdigits - p) + Zpos (p - digits)).
  rewrite Zpower_exp; auto with zarith.
  match goal with |- context [ ((?X * ?Y * ?T) + ?Z) / ?X] =>
     replace ((X * Y * T) + Z) with (Z + ((Y * T) * X)); [rewrite Z_div_plus| ring];
     auto with zarith
   end.
  rewrite Eq4; ring.
  split; auto with zarith.
  apply Zplus_le_0_compat; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end; auto with zarith.
  pattern (Zpos digits) at 1; replace (Zpos digits) with (Zpos (p - digits) + Zpos (wdigits - p)); auto with zarith.
  rewrite Zmult_comm; rewrite Zpower_exp; auto with zarith.
  rewrite Zmult_mod_distr_l; auto with zarith.
  replace (2 ^Zpos digits) with (2 ^Zpos (p - digits)  * (2 ^ Zpos (wdigits - p) - 1) + 2 ^Zpos (p - digits)).
  apply Zplus_le_lt_compat; auto with zarith.
  apply Zmult_le_compat_l; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  rewrite Eq4; rewrite <- Zpower_exp; auto with zarith.
  assert (tmp: forall x y, x + (y - x) = y); try rewrite tmp; auto with zarith; clear tmp.
  autorewrite with distr rm10.
  rewrite Eq4; rewrite <- Zpower_exp; auto with zarith.
  assert (tmp: forall x y, x + (y - x) = y); try rewrite tmp; auto with zarith; clear tmp.
  intros xh xl.
  generalize (spec_to_Z op_spec xh); intros HH; rewrite wB_power in HH.
  generalize (spec_to_Z op_spec xl); intros HH1; rewrite wB_power in HH1.
  case y.
  match goal with |- context [(?X ?= ?Y)%positive Eq] => case_eq (Pcompare X Y Eq) end; intros H1;
   auto with zarith.
  w_rewrite1; autorewrite with rm10.
  rewrite Pcompare_Eq_eq with (1:= H1); auto with zarith.
  rewrite wB_power; fold digits; autorewrite with distr.
  match goal with |- context[(?X * ?Y * ?X + ?Z) mod (?X * ?X)]  =>
    replace (X * Y * X + Z) with (Z + Y * (X * X)); [rewrite Z_mod_plus | ring]; auto with zarith
  end.
  apply sym_equal; apply Zmod_def_small; auto with zarith.
  split; auto with zarith.
  apply Zmult_lt_compat_r; auto with zarith.
  assert (Eq1: Zpos p < Zpos digits); auto.
   rewrite wwB_power.
   w_rewrite1; rewrite Zdiv_0; autorewrite with rm10; auto with zarith.
  repeat rewrite (spec_add_mul_div op_spec); autorewrite with rm10; auto with zarith.
  rewrite wB_power; fold digits.
  w_rewrite1; rewrite Zdiv_0; autorewrite with rm10; auto with zarith.
  pattern [|xh|] at 1; rewrite Z_div_mod_eq with (b := (2 ^ (Zpos digits  - Zpos p))); auto with zarith.
  autorewrite with distr.
  match goal with |- context [2 ^ ?X * ?Y * 2 ^?Z]  =>
    replace (2 ^ X * Y * 2 ^Z) with (Y * (2 ^X * 2 ^Z)); [rewrite <- Zpower_exp | ring]; auto with zarith
  end.
  assert (tmp: forall x y, x - y + y = x); try rewrite tmp; auto with zarith; clear tmp.
  match goal with |- context [(?X * ?Y + ?Z + ?T) mod ?Y]  => 
    replace (X * Y + Z + T) with (Z + T + X * Y); [try rewrite Z_mod_plus | ring]; auto with zarith
  end.
  rewrite Zmod_def_small.
  autorewrite with distr.
  rewrite <- Zmult_assoc; rewrite <- Zpower_exp; auto with zarith.
  rewrite Zmult_comm; rewrite <- Zmult_mod_distr_l; auto with zarith.
  rewrite <- Zpower_exp; auto with zarith.
  assert (tmp: forall x y, x + y + (y - x) = y + y); try rewrite tmp; auto with zarith; clear tmp.
  rewrite <- U5.
  rewrite Zpower_exp; auto with zarith.
  assert (div_th1: forall p q r, 0 <= p <= q -> 0 <= r -> r / 2 ^ (q - p) = (r * 2 ^ p) / (2 ^ q)).
  intros a b c (J1, J2) J3.
  rewrite Zmult_comm; pattern b at 2; replace b with (a + (b - a)); auto with zarith.
  rewrite Zpower_exp; auto with zarith.
  rewrite Zdiv_Zmult_compat_l; auto with zarith.
  rewrite div_th1; auto with zarith.
  rewrite <- Zplus_assoc.
  rewrite (fun x y => Zmult_comm (x/y)); rewrite <- Z_div_mod_eq; auto with zarith.
  rewrite Zmod_plus; auto with zarith.
  rewrite Zmod_def_small with (a := [|xl|] * 2 ^Zpos p); auto with zarith.
  repeat rewrite <- Zmult_assoc; rewrite (Zmult_comm (2 ^Zpos p)); repeat (rewrite Zmult_assoc).
  apply sym_equal; apply Zmod_def_small; auto with zarith.
Fail.
  rewrite Zmod_mod; auto with zarith.
  apply ok.
  assert (Eq1: Zpos p > Zpos digits); auto.
   rewrite wwB_power.
  w_rewrite1; rewrite Zdiv_0; autorewrite with rm10; auto with zarith.
  repeat rewrite (spec_add_mul_div op_spec); autorewrite with rm10; auto with zarith.
  rewrite wB_power; fold digits.
  w_rewrite1; rewrite Zdiv_0; autorewrite with rm10; auto with zarith.
  apply ok.
  apply Zpower_lt_0; auto with zarith.
  apply ok.
  fold digits; split; auto with zarith.
  compute; auto.
  apply ok.
  intros yh yl.
  generalize (spec_to_Z op_spec yh); intros HH2; rewrite wB_power in HH2.
  generalize (spec_to_Z op_spec yl); intros HH3; rewrite wB_power in HH3.
  match goal with |- context [(?X ?= ?Y)%positive Eq] => case_eq (Pcompare X Y Eq) end; intros H1;
   auto with zarith.
  rewrite wwB_power.
  w_rewrite1; autorewrite with rm10.
  rewrite Pcompare_Eq_eq with (1:= H1); auto with zarith.
  rewrite wB_power ; fold digits.
  rewrite U5.
  assert (tmp: forall x, x + x - x = x); try rewrite tmp; auto with zarith; clear tmp.
  match goal with |- context [ ((?X * ?Y) + ?Z) / ?X] =>
     replace ((X * Y) + Z) with (Z + (Y  * X)); [rewrite Z_div_plus| ring];
     auto with zarith
   end.
  rewrite Zdiv_lt_0; auto with zarith; autorewrite with rm10.
  rewrite Zpower_exp; auto with zarith.
  match goal with |- context[((?X  * ?Y + ? T) * ?X + ?Z) mod (?X * ?X)]  => 
    replace ((X * Y  + T) * X + Z) with (T * X + Z + Y * (X * X)); [rewrite Z_mod_plus | ring]; auto with zarith
  end.
  apply sym_equal; apply Zmod_def_small; auto with zarith.
  rewrite <- Zpower_exp; try rewrite <- U5; auto with zarith.
  rewrite <- wwB_power; rewrite <- wB_power.
  rewrite Zmult_comm; generalize (spec_ww_to_Z (WW xl yh)); simpl; auto with zarith.
  rewrite wwB_power.
  w_rewrite1; autorewrite with rm10.
  repeat rewrite (spec_add_mul_div op_spec); autorewrite with rm10; auto with zarith.
  rewrite wB_power; fold digits.
  assert (Eq1: Zpos p < Zpos digits); auto.
  apply ok.
  rewrite wwB_power.
  w_rewrite1; autorewrite with rm10.
  repeat rewrite (spec_add_mul_div op_spec); autorewrite with rm10; auto with zarith.
  rewrite wB_power; fold digits.
  assert (Eq1: Zpos p > Zpos digits); auto.
  apply ok.
  apply ok.
  apply ok.
Qed.


End Proof.
