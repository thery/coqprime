Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import ZPowerAux.
Require Import Basic_type.
Require Import ZnZ.
Require Import ZnZDivn1.
Require Import Zn2Z_for_Proof.
Require Import JMeq.

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

 Notation "[! n | x !]" := (gen_to_Z (xO (znz_digits w_op)) (ww_to_Z w_op) n x)
              (at level 0, x at level 99).
 
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
    (spec_opp op_spec)
    (spec_opp_carry op_spec)
    (spec_succ_c op_spec)
    (spec_add_c op_spec)
    (spec_add_carry_c op_spec)
    (spec_succ op_spec)
    (spec_add op_spec)
    (spec_add_carry op_spec)
    (spec_pred_c op_spec)
    (spec_sub_c op_spec)
    (spec_sub_carry_c op_spec)
    (spec_pred op_spec)
    (spec_sub op_spec)
    (spec_sub_carry op_spec)
    (spec_mul_c op_spec)
    (spec_mul op_spec)
    : w_rewrite.

 Hint Resolve (spec_to_Z op_spec) : ww_spec.
 Ltac zarith := auto with ww_spec zarith. 
 Ltac w_rewrite := autorewrite with w_rewrite.
 Ltac w_solve := trivial;w_rewrite;trivial;try ring;zarith.

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
  replace (wB*wB - 1) with ((wB - 1) * wB + (wB - 1)) ...
  apply Zplus_le_compat...  apply Zmult_le_compat ...
 Qed.
 Hint Resolve spec_ww_to_Z : ww_spec.
  
 Theorem spec_ww_of_pos : forall p, 
       Zpos p = 
        (Z_of_N (fst (ww_of_pos w_op p)))*wwB + [[(snd (ww_of_pos w_op p))]].
 Proof.
  intros p; simpl.
  unfold ww_of_pos.
  generalize (spec_of_pos op_spec p); case  (znz_of_pos w_op p).
  intros n w0 Hw0; rewrite Hw0; case n; simpl fst; simpl snd; w_rewrite.
  simpl; w_rewrite; rewrite Zmult_0_l; rewrite Zplus_0_l; auto.
  intros p0.
  generalize (spec_of_pos op_spec p0); case  (znz_of_pos w_op p0).
  intros n0 w1; simpl fst; simpl snd; w_rewrite.
  intros H; replace (Z_of_N (Npos p0)) with (Zpos p0).
  2: case p0; simpl; auto.
  unfold ww_to_Z; rewrite spec_WW; auto.
  rewrite H; simpl; w_solve1.
 Qed.

 Lemma lt_0_wB : 0 < wB.
 Proof.
  assert (H:=spec_to_Z op_spec (znz_1 w_op));omega.
 Qed.

 Lemma lt_0_wwB : 0 < wwB.
 Proof.
  assert (H:=spec_ww_to_Z W0);omega.
 Qed.
 Hint Resolve lt_0_wB lt_0_wwB : zarith.

 Theorem  wB_pos: 1 < wB.
 Proof.
  unfold base. 
  apply Zlt_le_trans with 2; auto with zarith.
  pattern 2 at 1; rewrite <- (Zpower_exp_1).    
  apply Zpower_le_monotone; auto with zarith.
  split; auto with zarith. 
  case (znz_digits w_op); compute; intros; try discriminate.
 Qed.
 Hint Resolve wB_pos.

 Theorem wwB_pos: 1 < wwB. 
 Proof.
  rewrite wwB_wBwB.
  rewrite <- (Zmult_1_r 1).
  apply Zmult_lt_compat; auto with zarith.
  generalize wB_pos; auto with zarith.
 Qed.
 Hint Resolve wwB_pos.

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

 Lemma spec_ww_hl: forall h l, [[WW h l]] = [|h|] * wB + [|l|].
 Proof. intros; simpl; auto. Qed.
 Hint Rewrite spec_ww_hl: w_rewrite.

    (*    Auxillary lemmas *)

 Theorem beta_lex: forall a b c d beta, 
       a * beta + b <= c * beta + d -> 
       0 <= b < beta -> 0 <= d < beta -> 
       a <= c.
 Proof.
  intros a b c d beta H1 (H3, H4) (H5, H6).
  assert (a - c < 1); auto with zarith.
  apply Zmult_lt_reg_r with beta; auto with zarith.
  apply Zle_lt_trans with (d  - b); auto with zarith.
  rewrite Zmult_minus_distr_r; auto with zarith.
 Qed.

 Theorem beta_lex_inv: forall a b c d beta,
      a < c -> 0 <= b < beta ->
      0 <= d < beta -> 
      a * beta + b < c * beta  + d. 
 Proof.
  intros a b c d beta H1 (H3, H4) (H5, H6).
  case (Zle_or_lt (c * beta + d) (a * beta + b)); auto with zarith.
  intros H7; contradict H1;apply Zle_not_lt;apply beta_lex with (1 := H7);auto.
 Qed.

 Theorem wB_lex: forall a b c d, 
      a * wB + b <= c * wB + d -> 
      0 <= b < wB -> 0 <= d < wB -> 
      a <= c.
 Proof.
  intros a b c d H1 H2 H3; apply beta_lex with (1 := H1); auto.
 Qed.

 Theorem wB_lex_inv: forall a b c d, 
      a < c -> 
      0 <= b < wB -> 
      0 <= d < wB -> 
      a * wB + b < c  * wB + d. 
 Proof.
  intros a b c d H1 H2 H3; apply beta_lex_inv with (1 := H1); auto.
 Qed.

 Theorem wBwB_lex: forall a b c d,
      a * (wB * wB) + b <= c * (wB * wB) + d -> 
      0 <= b < wB * wB -> 
      0 <= d < wB * wB -> 
      a <= c.
 Proof.
  intros a b c d H1 H2 H3; apply beta_lex with (1 := H1); auto.
 Qed.

 Theorem wBwB_lex_inv: forall a b c d, 
      a < c -> 
      0 <= b < wB * wB -> 
      0 <= d < wB * wB ->
      a * (wB * wB) + b < c * (wB * wB) + d. 
 Proof.
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

 Lemma mod_wwB : forall z w, 
   (z*wB + [|w|]) mod wwB = (z mod wB)*wB + [|w|].
 Proof with w_solve.
  intros z w'.
  rewrite Zmod_plus...
  pattern wwB at 1;rewrite wwB_wBwB.
  rewrite (Zmult_comm z);rewrite Zmod_Zmult_compat_l...
  rewrite (Zmult_comm wB).
  rewrite (Zmod_def_small (z mod wB * wB + [|w'|] mod wwB)).
  rewrite (Zmod_def_small [|w'|]);trivial.
  generalize (spec_ww_to_Z (WW (znz_0 w_op) w'));simpl...
  destruct (Z_mod_lt z wB) ...
  destruct (Z_mod_lt [|w'|] wwB) ...
  split...
  apply Zlt_le_trans with (z mod wB * wB + wB)...
  apply Zplus_le_lt_compat...
  destruct (spec_to_Z op_spec w');rewrite Zmod_def_small...
  generalize (spec_ww_to_Z (WW (znz_0 w_op) w'));simpl...
  apply Zle_trans with ((wB - 1) * wB + wB).
  apply Zplus_le_compat...
  replace ((wB - 1) * wB + wB) with wwB;w_solve1.
 Qed.

 Lemma spec_ww_opp : forall x, [[ww_opp w_op x]] = (-[[x]]) mod wwB.
 Proof with w_solve.
  destruct x;simpl ...
  assert (H1:=spec_opp_c op_spec w1);destruct (znz_opp_c w_op w1).
  simpl in H1.
  replace (- ([|w0|] * wB + [|w1|])) with ((-[|w0|]) * wB + - [|w1|])...
  rewrite <- H1;rewrite mod_wwB ...
  assert (znz_to_Z w_op w2 = 0). 
   destruct (spec_to_Z op_spec w2);destruct (spec_to_Z op_spec w1)...
  rewrite H...
  unfold interp_carry in H1.
  replace (- ([|w0|] * wB + [|w1|])) with ((-[|w0|]) * wB + - [|w1|])...
  rewrite <- H1.
  replace (- [|w0|] * wB + (-1 * wB + [|w2|])) with
      ((-([|w0|] + 1)) * wB + [|w2|]) ...
  rewrite mod_wwB ...
  rewrite <-(Zmod_unique (- ([|w0|] + 1)) wB (-1) (wB -([|w0|] + 1)))...
  assert (H2:=spec_to_Z op_spec w0) ...
 Qed.

 Lemma spec_ww_opp_carry : forall x, [[ww_opp_carry w_op x]] = wwB - [[x]] - 1.
 Proof. unfold ww_to_Z;destruct x;simpl; w_solve1. Qed.

 Lemma spec_ww_succ_c : forall x, [+[ww_succ_c w_op x]] = [[x]] + 1.
 Proof with w_solve.
  destruct x;simpl. w_solve.
  assert (H1:=spec_succ_c op_spec w1);destruct (znz_succ_c w_op w1).
  unfold interp_carry in * ...
  assert (H2:=spec_succ_c op_spec w0);destruct (znz_succ_c w_op w0);
   simpl;w_rewrite1.
  rewrite H2; unfold interp_carry in * ...
  rewrite H2; unfold interp_carry in * ... 
 Qed.

 Hint Rewrite 
   spec_ww_opp_c spec_ww_opp spec_ww_opp_carry spec_ww_succ_c : w_rewrite.

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

 Lemma spec_ww_succ : forall x, [[ww_succ w_op x]] = ([[x]] + 1) mod wwB.
 Proof with w_solve.
  destruct x;simpl. w_solve. 
   rewrite Zmod_def_small;trivial.
   generalize (spec_ww_to_Z (WW (znz_0 w_op) (znz_1 w_op)));simpl;w_solve.
  assert (H1:=spec_succ_c op_spec w1);destruct (znz_succ_c w_op w1).
  simpl in *;rewrite Zmod_def_small.
  rewrite H1;ring.
  rewrite <-Zplus_assoc;rewrite <- H1;exact (spec_ww_to_Z (WW w0 w2)).
  simpl;w_rewrite.
  rewrite <-Zplus_assoc;rewrite <- H1.
  unfold interp_carry.
  replace ([|w0|] * wB + (1 * wB + [|w2|])) with 
          (([|w0|] + 1) * wB + [|w2|]).
  rewrite mod_wwB...
  ring.
 Qed.

 Lemma spec_ww_add : 
  forall x y, [[ww_add w_op x y]] = ([[x]] + [[y]]) mod wwB.
 Proof with w_solve.
  destruct x;simpl.
  intros;rewrite Zmod_def_small...
  destruct y;simpl.
  rewrite Zplus_0_r;rewrite Zmod_def_small...
  apply (spec_ww_to_Z (WW w0 w1)).
  assert (H1:=spec_add_c op_spec w1 w3);destruct (znz_add_c w_op w1 w3);
  unfold ww_to_Z;w_rewrite.
  replace ([|w0|] * wB + [|w1|] + ([|w2|] * wB + [|w3|])) with
     (([|w0|]+[|w2|]) * wB + ([|w1|] + [|w3|])) ...
  simpl in H1;rewrite <- H1;rewrite mod_wwB...
  replace ([|w0|] * wB + [|w1|] + ([|w2|] * wB + [|w3|])) with
     (([|w0|]+[|w2|]) * wB + ([|w1|] + [|w3|])) ...
  unfold interp_carry in H1;rewrite <- H1.
  replace (([|w0|] + [|w2|]) * wB + (1 * wB + [|w4|])) with
   (([|w0|] + [|w2|] + 1) * wB + [|w4|])...
  rewrite mod_wwB...
 Qed.

 Lemma spec_ww_add_carry : 
   forall x y, [[ww_add_carry w_op x y]] = ([[x]] + [[y]] + 1) mod wwB.
 Proof with w_solve.
  destruct x;simpl;intros y.
  fold (ww_succ w_op y);apply spec_ww_succ.
  destruct y;simpl.
  fold (ww_succ w_op (WW w0 w1)). rewrite spec_ww_succ.
  rewrite Zplus_0_r;simpl ...
  assert (H1:=spec_add_carry_c op_spec w1 w3);
    destruct (znz_add_carry_c w_op w1 w3);unfold ww_to_Z;simpl.
  replace ([|w0|] * wB + [|w1|] + ([|w2|] * wB + [|w3|])+1) with
     (([|w0|]+[|w2|]) * wB + ([|w1|] + [|w3|] +1)) ...
  simpl in H1;rewrite <- H1;rewrite mod_wwB...
  replace ([|w0|] * wB + [|w1|] + ([|w2|] * wB + [|w3|])+1) with
     (([|w0|]+[|w2|]) * wB + ([|w1|] + [|w3|] + 1)) ...
  unfold interp_carry in H1;rewrite <- H1.
  replace (([|w0|] + [|w2|]) * wB + (1 * wB + [|w4|])) with
   (([|w0|] + [|w2|] + 1) * wB + [|w4|])...
  rewrite mod_wwB...
 Qed.

 Hint Rewrite spec_ww_succ spec_ww_add spec_ww_add_carry : w_rewrite.

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

 Lemma spec_ww_pred : forall x, [[ww_pred w_op x]] = ([[x]] - 1) mod wwB.
 Proof with w_solve.
  destruct x;simpl...
  rewrite <-(Zmod_unique (-1) wwB (-1) (-1+wB*wB))...
  assert (H:= lt_0_wwB);rewrite <- wwB_wBwB;split...
  w_solve1.
  assert (H:= spec_pred_c op_spec w1);destruct (znz_pred_c w_op w1).
  unfold interp_carry,ww_to_Z in *;simpl...
  replace ([|w0|] * wB + [|w1|] - 1) with ([|w0|] * wB + ([|w1|] - 1))...
  rewrite <- H;rewrite mod_wwB...
  destruct (spec_to_Z op_spec w0);rewrite Zmod_def_small ...
  unfold interp_carry in H;unfold ww_to_Z...
  replace ([|w0|] * wB + [|w1|] - 1) with ([|w0|] * wB + ([|w1|] - 1))...
  rewrite <- H.
  replace ([|w0|] * wB + (-1 * wB + [|w2|])) with
   (([|w0|] - 1)* wB  + [|w2|]) ...
  rewrite mod_wwB ...
 Qed.

 Hint Rewrite spec_ww_pred : w_rewrite.

 Lemma spec_ww_sub : forall x y, 
   [[ww_sub w_op x y]] = ([[x]] - [[y]]) mod wwB.
 Proof with w_solve.
  destruct y;simpl ...
  replace ([[x]] - 0) with [[x]] ...
  destruct (spec_ww_to_Z x);rewrite Zmod_def_small ...
  destruct x.
  fold (ww_opp w_op (WW w0 w1)) ... 
  assert (H:= spec_sub_c op_spec w3 w1);destruct (znz_sub_c w_op w3 w1);
  unfold interp_carry in H;unfold ww_to_Z;simpl...
  replace ([|w2|] * wB + [|w3|] - ([|w0|] * wB + [|w1|])) with
    (([|w2|] - [|w0|]) * wB + ([|w3|] - [|w1|])) ...
  rewrite <- H;rewrite mod_wwB...
  replace ([|w2|] * wB + [|w3|] - ([|w0|] * wB + [|w1|])) with
    (([|w2|] - [|w0|]) * wB + ([|w3|] - [|w1|])) ...
  rewrite <- H.
  replace (([|w2|] - [|w0|]) * wB + (-1 * wB + [|w4|])) with
  (([|w2|] - [|w0|] - 1) * wB + [|w4|]) ...
  rewrite mod_wwB...
 Qed.

 Lemma spec_ww_sub_carry : 
   forall x y, [[ww_sub_carry w_op x y]] = ([[x]] - [[y]] - 1) mod wwB.
 Proof with w_solve.
  destruct y;simpl.
  fold (ww_pred w_op x) ...
  replace ([[x]] - 0) with [[x]] ...
  destruct x;unfold ww_to_Z;simpl...
  rewrite <- (Zmod_unique (- ([|w0|] * wB + [|w1|]) - 1) wwB (-1)
            (wB*wB + (- ([|w0|] * wB + [|w1|]) - 1)))...
  rewrite<-wwB_wBwB;generalize (spec_ww_to_Z (WW w0 w1)) ...
  w_solve1.
  assert (H1:=spec_sub_carry_c op_spec w3 w1);
    destruct (znz_sub_carry_c w_op w3 w1);unfold interp_carry in H1 ...
  replace ([|w2|] * wB + [|w3|] - ([|w0|] * wB + [|w1|]) - 1) with
    (([|w2|] - [|w0|]) * wB + ([|w3|] - [|w1|] -1)) ...
  rewrite <- H1;rewrite mod_wwB...
  replace ([|w2|] * wB + [|w3|] - ([|w0|] * wB + [|w1|]) - 1) with
    (([|w2|] - [|w0|]) * wB + ([|w3|] - [|w1|] -1)) ...
  rewrite <- H1.
  replace (([|w2|] - [|w0|]) * wB + (-1 * wB + [|w4|])) with
  (([|w2|] - [|w0|] - 1) * wB + [|w4|]) ...
  rewrite mod_wwB...
 Qed.

 Hint Rewrite spec_ww_sub spec_ww_sub_carry : w_rewrite.

 Theorem mult_wwB: forall x y, [|x|] * [|y|] < wwB.
 Proof.
  intros x y; rewrite wwB_wBwB.
  generalize (spec_to_Z op_spec x); intros U.
  generalize (spec_to_Z op_spec y); intros U1.
  apply Zle_lt_trans with ((wB -1 ) * (wB - 1)); auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_r || rewrite Zmult_minus_distr_l); 
	auto with zarith.
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

 Theorem spec_znz_mul_c : forall x y, [[znz_mul_c w_op x y]] = [|x|] * [|y|].
 Proof. intros x y; unfold ww_to_Z; apply spec_mul_c; auto. Qed.
 Hint Rewrite spec_znz_mul_c: w_rewrite.

 Lemma sum_mul_carry : forall xh xl yh yl wc cc,
   [|wc|]*wB*wB + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] -> 
   0 <= [|wc|] <= 1.
 Proof.
  intros. zmult_lt_b xh yl;zmult_lt_b xl yh;spec_to_Z wc.
  assert (H3 := spec_ww_to_Z cc). split;zarith.
  apply wBwB_lex with (b := [[cc]]) (d := wB * wB - 2); auto with zarith.
  rewrite Zmult_assoc; auto with zarith.
  rewrite <- wwB_wBwB; auto with zarith.
  generalize wB_pos; auto with zarith.
 Qed.

 Theorem mult_add_ineq: forall xH yH crossH, 
               0 <= [|xH|] * [|yH|] + [|crossH|] < wwB.
 Proof.
  intros xH yH crossH.
  generalize (spec_to_Z op_spec xH); intros HH.
  generalize (spec_to_Z op_spec yH); intros HH1.
  generalize (spec_to_Z op_spec crossH); intros HH2.
  split; auto with zarith.
  rewrite wwB_wBwB.
  apply Zle_lt_trans with  ((wB - 1) * (wB - 1) + (wB -1)); auto with zarith.
  apply Zplus_le_compat; auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); 
    auto with zarith.
 Qed.
 Hint Resolve mult_add_ineq.

 Theorem C1_plus_wwB: forall z,  [+[C1 z]] = wwB + [[z]].
 Proof. intros zz; simpl; case wwB; auto with zarith. Qed.

 Theorem C1_plus_wB: forall z,  [+|C1 z|] = wB + [|z|].
 Proof. intros zz; simpl; case wB; auto with zarith. Qed.

 Theorem C1_minus_wwB: forall z, [-[C1 z]]  =  [[z]] - wwB.
 Proof.
  intro zz; simpl; generalize (wwB_pos); case wwB.
  intros; ring.
  intros; ring.
  intros p Hp; discriminate Hp.
 Qed.

 Theorem C1_minus_wB: forall z, [-|C1 z|]  =  [|z|] - wB.
 Proof.
  intro zz; simpl; generalize (wB_pos); case wB.
  intros; ring.
  intros; ring.
  intros p Hp; discriminate Hp.
 Qed.

 Hint Rewrite C1_plus_wwB C1_plus_wB C1_minus_wwB C1_minus_wB: w_rewrite.

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
  assert (HH8: 0 <= [[hh]] + [|wc|] * wB < wB * wB).
  split; auto with zarith.
  replace (wB * wB) with ((wB * wB - wB)  + wB); auto with zarith.
  apply Zplus_lt_le_compat; auto with zarith.
  rewrite H.
  apply Zle_lt_trans with ((wB -1) * (wB - 1)); auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); 
     auto with zarith.
  generalize (wB_pos); auto with zarith.
  pattern wB at 2; rewrite <- Zmult_1_l; auto with zarith.
  destruct cc.
  simpl; autorewrite with w_rewrite.
  rewrite wwB_wBwB; rewrite Zmod_def_small; auto with zarith.
  ring.
  auto with zarith.
  generalize (spec_to_Z op_spec w0); intros HH9.
  generalize (spec_to_Z op_spec w1); intros HH10.
  assert (U: 0 <= [[hh]] + ([|wc|] * wB + [|w0|]) < wB * wB).
  split; auto with zarith.
  generalize H1; autorewrite with w_rewrite; clear H1; intros H1.
  assert ([|wc|] * wB + [|w0|] < 2 * wB - 1); auto with zarith.
  apply Zmult_lt_reg_r with wB; auto with zarith.
  rewrite Zmult_plus_distr_l.
  apply Zplus_lt_reg_r with [|w1|].
  rewrite <- Zplus_assoc; rewrite H1.
  apply Zle_lt_trans with ((wB - 1) * (wB - 1) + (wB - 1) * (wB - 1));
    auto with zarith.
  apply Zplus_le_compat; apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r);
    auto with zarith.
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
    replace X with (([|xh|] * wB + [|xl|]) * ([|yh|] * wB + [|yl|]))
  end; auto with zarith.
  apply Zle_lt_trans with ((wwB - 1) * (wwB - 1)); auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  simpl in HH12; auto with zarith.
  simpl in HH13; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); 
    auto with zarith.
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
 Proof.
  intros x y; case x; auto; intros xh xl.
  case y; auto; try ring; intros yh yl.
  match goal with |- _ = ?X => set (tmp:= X); simpl; unfold tmp end.
  set (hh :=  (znz_mul_c w_op xh yh)).
  set (ll  :=  (znz_mul_c w_op xl yl)).
  generalize (spec_ww_add_c (znz_mul_c w_op xh yl) (znz_mul_c w_op xl yh)).
  case (ww_add_c w_op (znz_mul_c w_op xh yl) (znz_mul_c w_op xl yh)).
  intros wc Hwc.
  apply  spec_mul_aux with 
    (cc := wc) (wc := w_op.(znz_0)) (hh := hh) (ll := ll).
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
  rewrite Zmult_1_l; split; auto with zarith.
  apply Zle_lt_trans with ((wwB - 2 * wB + 1) + (wB + 0)); auto with zarith.
  apply Zplus_le_compat_r.
  unfold hh, ww_to_Z; repeat rewrite spec_mul_c; auto with arith.
  match goal with |- ?X <= ? Y => assert (0 <= X <= Y) end; auto with zarith.
  rewrite wwB_wBwB; apply Zmult_lt_b; w_solve1.
  apply spec_to_Z; auto.
  assert (1 < wB); auto with zarith.
  intros cc1 cc2 Hwc.
  apply  spec_mul_aux 
    with (cc := (WW cc1 cc2)) (wc := w_op.(znz_1)) (hh := hh) (ll := ll).
  unfold hh; unfold ww_to_Z; apply spec_mul_c; auto.
  unfold ll; unfold ww_to_Z; apply spec_mul_c; auto.
  generalize Hwc; w_rewrite.
  unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  rewrite wwB_wBwB; clear Hwc; intros Hwc; rewrite <- Hwc; ring.
 Qed.

 Opaque ww_add.
 Theorem spec_ww_mul: forall x y, 
          [[ww_mul w_op x y]] = ([[x]] * [[y]]) mod wwB.
 Proof.
  assert (U:= lt_0_wB).
  assert (U1:= lt_0_wwB).
  intros x y; case x; auto; intros xh xl.
  case y; auto.
  simpl; rewrite Zmult_0_r; rewrite Zmod_def_small; auto with zarith.
  intros yh yl.
  simpl; w_rewrite.
  rewrite <- Zmod_plus; auto with zarith.
  repeat (rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r).
  rewrite <- Zmult_mod_distr_r; auto with zarith.
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
 Proof.
  intros x; case x; auto; intros xh xl.
  match goal with |- _ = ?X => set (tmp:= X); simpl; unfold tmp end.
  set (hh :=  (znz_square_c w_op xh)).
  set (ll  :=  (znz_square_c w_op xl)).
  generalize (spec_ww_add_c (znz_mul_c w_op xh xl) (znz_mul_c w_op xh xl)).
  case (ww_add_c w_op (znz_mul_c w_op xh xl) (znz_mul_c w_op xh xl)).
  intros wc Hwc.
  apply spec_mul_aux with 
      (cc := wc) (wc := w_op.(znz_0)) (hh := hh) (ll := ll).
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
  rewrite Zmult_1_l; split; auto with zarith.
  apply Zle_lt_trans with ((wwB - 2 * wB + 1) + (wB + 0)); auto with zarith.
  apply Zplus_le_compat_r.
  unfold hh, ww_to_Z; repeat rewrite spec_square_c; auto with arith.
  match goal with |- ?X <= ? Y => assert (0 <= X <= Y) end; auto with zarith.
  rewrite wwB_wBwB; apply Zmult_lt_b; w_solve1.
  assert (1 < wB); auto with zarith.
  intros cc1 cc2 Hwc.
  apply spec_mul_aux with
    (cc := (WW cc1 cc2)) (wc := w_op.(znz_1)) (hh := hh) (ll := ll).
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
   let (wc,cc) :=  
    match (znz_add_c w_op xh xl)  with
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
        match ww_add_c w_op (znz_mul_c w_op xhl yhl) (WW yhl (znz_0 w_op)) with
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
          match 
           ww_add_c w_op (znz_mul_c w_op xhl yhl) (WW suml (znz_0 w_op)) with
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
          match 
             ww_add_c w_op (znz_mul_c w_op xhl yhl) (WW suml (znz_0 w_op)) with
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
 Proof.
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
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); 
                                    [ring | rewrite Eq] end.
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
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); 
                                     [idtac | rewrite Eq] end.
  rewrite Hhh; rewrite Hll.
  rewrite Hz; rewrite Hw0; rewrite Zplus_0_r.
  rewrite <- Zmult_plus_distr_r.
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
    match type of Hw1 with ?Y = _ => 
        apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
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
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [idtac | pattern Y at 1; rewrite  Hw1]; ring
   end end.
  intro z0; w_rewrite; intros Hz0.
  rewrite Zmult_0_l; rewrite Zplus_0_l.
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); 
                                      [idtac | rewrite Eq] end.
  match goal with |-  ?X = _  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hz with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with ([|w0|] * (Y - Y) + X);
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
  match goal with |- ?X mod _ = ? Y => assert (Eq: X = Y); 
               [idtac | rewrite Eq] end.
  rewrite Hhh; rewrite Hll; rewrite Hz.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with (([|yh|] + [|yl|]) * (Y - Y) + X);
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
    match type of Hw0 with ?Y = _ =>
         apply trans_equal with (([|yh|] + [|yl|]) * (Y - Y) + X);
         [idtac | pattern Y at 1; rewrite  Hw0]; ring
   end end.
  intro z0; w_rewrite; intros Hz0.
  rewrite Zmult_0_l; rewrite Zplus_0_l.
  match goal with |- ?X mod _ = ? Y => 
       assert (Eq: X = Y); [ring | rewrite Eq] end.
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with (([|yh|] + [|yl|]) * (Y - Y) + X);
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ =>
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  ring.
  intros z1; w_rewrite; intros Hz1.
  match goal with |-  ?X = _  =>
    match type of Hz1 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz1]
   end end.
  rewrite Hz0;rewrite Hz;rewrite Hw2;rewrite Hll;rewrite Hhh; rewrite wwB_wBwB.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  ring.
  intros z0; w_rewrite; intro Hz0.
  rewrite Zmult_0_l; rewrite Zplus_0_l.
  match goal with |- ?X mod _ = ? Y => 
       assert (Eq: X = Y); [idtac | rewrite Eq] end.
  rewrite Hll.
  match goal with |-  ?X = _  =>
    match type of Hz0 with ?Y = _ => apply trans_equal with ((Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hz0]
   end end.
  rewrite Hz; rewrite Hw2.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  rewrite wwB_wBwB; ring.
  intro z1; w_rewrite; intro Hz1.
  match goal with |-  ?X = _  =>
    match type of Hz1 with ?Y = _ => 
         apply trans_equal with ((Y - Y) + X);
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
    match type of Hw0 with ?Y = _ =>
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ =>
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ =>
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw1]
   end end.
  ring.
  intros z; w_rewrite; intros Hz.
  generalize (spec_ww_to_Z z); intro HH6.
  rewrite Zmod_minus; auto with zarith.
  rewrite Zmod_mod; auto with zarith.
  rewrite <- Zmod_minus; auto with zarith.
  match goal with |- ?Z + ?X mod _ = ? Y =>
         assert (Eq: X = Y - 3 * Z); [idtac | rewrite Eq] end.
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
    match type of Hw0 with ?Y = _ => 
         apply trans_equal with ([|w1|] * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw0 with ?Y = _ => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite  Hw0]
   end end.
  match goal with |-  ?X = _  =>
    match type of Hw1 with ?Y = _ => 
         apply trans_equal with (([|xh|] + [|xl|]) * (Y - Y) + X);
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

 Theorem spec_ww_karatsuba_c: forall x y, 
             [||ww_karatsuba_c w_op x y||] = [[x]] * [[y]].
 Proof.
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
  match goal with |- context [znz_add_c ?X ?Y ?Z] =>case (znz_add_c X Y Z) end.
  intro w0.
  match goal with |- context [znz_add_c ?X ?Y ?Z] =>case (znz_add_c X Y Z) end.
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
  match goal with |- context [znz_add_c ?X ?Y ?Z] =>case (znz_add_c X Y Z) end.
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
  match goal with |- context [znz_add_c ?X ?Y ?Z] =>case (znz_add_c X Y Z) end.
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

 Theorem spec_w_carry:  forall q, 0 <= [+|q|].
 Proof.
  intro q;case q;intros q1;generalize (spec_to_Z op_spec q1);
    w_rewrite; simpl; auto with zarith.
 Qed.

 Theorem spec_znz_WW: forall x y, [[znz_WW w_op x y]] = [|x|] * wB  + [|y|].
 Proof.
  intros x y; unfold ww_to_Z; rewrite spec_WW; auto with zarith.
 Qed.
 Hint Rewrite spec_znz_WW: w_rewrite.

 Theorem wB_div_2:  2 * (wB / 2) = wB.
 Proof.
  unfold base.
  assert (2 ^ (Zpos (znz_digits w_op)) = 
              2 * (2 ^ (Zpos (znz_digits w_op) - 1) )).
  pattern 2 at 2; rewrite <- Zpower_exp_1.
  rewrite <- Zpower_exp; auto with zarith.
  eq_tac; auto with zarith.
  case (znz_digits w_op); compute; intros; discriminate.
  rewrite H.
  eq_tac; auto with zarith.
  rewrite Zmult_comm; apply Z_div_mult; auto with zarith.
 Qed.

 Theorem wwB_div_2: wwB / 2 = wB / 2 * wB.
 Proof.
  rewrite wwB_wBwB.
  pattern wB at 1; rewrite <- wB_div_2; auto.
  rewrite <- Zmult_assoc.
  repeat (rewrite (Zmult_comm 2); rewrite Z_div_mult); auto with zarith.
  Qed.

  Theorem wB_div2: forall x, wB/2  <= x -> wB <= 2 * x.
  intros x H; rewrite <- wB_div_2; apply Zmult_le_compat_l; auto with zarith.
 Qed.

 Theorem spec_ww_split: forall a, [[a]] =
      [|fst (ww_split w_op a)|] * wB + [|snd(ww_split w_op a)|].
 Proof.
  intros a; case a; w_rewrite1; simpl; w_rewrite; intros; ring.
 Qed.

 Lemma Zmult_lt_0_reg_r_2 : forall n m : Z, 0 <= n -> 0 < m * n -> 0 < m.
 Proof.
  intros n m H1 H2;apply Zmult_lt_0_reg_r with n;trivial.
  destruct (Zle_lt_or_eq _ _ H1);trivial.
  subst;rewrite Zmult_0_r in H2;discriminate H2.
 Qed.

 Theorem spec_w_div32 : forall a1 a2 a3 b1 b2,
     wB/2 <= [|b1|] ->
     [[WW a1 a2]] < [[WW b1 b2]] ->
     let (q,r) := w_div32 w_op a1 a2 a3 b1 b2 in
     [|a1|] * wwB + [|a2|] * wB  + [|a3|] = 
        [|q|] *  ([|b1|] * wB + [|b2|])  + [[r]] /\ 
     0 <= [[r]] < [|b1|] * wB + [|b2|].
 Proof.
  intros a1 a2 a3 b1 b2 Hle Hlt.
  assert (U:= lt_0_wB).
  assert (U1:= lt_0_wwB).
  generalize (spec_to_Z op_spec a1); intros HH.
  generalize (spec_to_Z op_spec a2); intros HH1.
  generalize (spec_to_Z op_spec a3); intros HH2.
  generalize (spec_to_Z op_spec b1); intros HH3. 
  generalize (spec_to_Z op_spec b2); intros HH4. 
  replace ([|a1|] * wwB + [|a2|] * wB + [|a3|]) with
     (([|a1|]*wB + [|a2|])*wB + [|a3|]).
  2:rewrite wwB_wBwB;ring.
  unfold w_div32.
  assert (Hcmp:= spec_compare op_spec a1 b1);destruct (znz_compare w_op a1 b1).
  simpl in Hlt.
  rewrite Hcmp in Hlt;assert ([|a2|] < [|b2|]). omega.
  assert ([[WW (znz_sub w_op a2 b2) a3]] =
             ([|a2|]-[|b2|])*wB + [|a3|] + wwB).
   simpl;w_rewrite.
   assert ([|a2|] - [|b2|] = wB*(-1) + ([|a2|] - [|b2|] + wB)). ring.
   assert (0 <= [|a2|] - [|b2|] + wB < wB). omega.
   rewrite <- (Zmod_unique ([|a2|]-[|b2|]) wB (-1) ([|a2|]-[|b2|]+wB) U H1 H0).
   w_solve1.
  assert (U2 := wB_pos).
  generalize (spec_ww_add_c (WW (znz_sub w_op a2 b2) a3) (WW b1 b2));
  rewrite H0;destruct (ww_add_c w_op (WW (znz_sub w_op a2 b2) a3) (WW b1 b2))
  as [r|r]; w_rewrite.
  simpl;intros H1.
  rewrite (Zmod_def_small (wB - 1 - 1)).
  2:omega.
  assert (0<= ([[r]] + ([|b1|] * wB + [|b2|])) - wwB < [|b1|] * wB + [|b2|]).
   assert (H2:= spec_ww_to_Z r);split;zarith.
   rewrite H1.
   assert (H12:= wB_div2 Hle). assert (wwB <= 2 * [|b1|] * wB).
   rewrite wwB_wBwB;zarith.
   assert (-wwB < ([|a2|] - [|b2|]) * wB + [|a3|] < 0).
   split.
   apply Zlt_le_trans with (([|a2|] - [|b2|]) * wB);zarith.
   rewrite wwB_wBwB;replace (-(wB*wB)) with (-wB*wB);w_solve.
   apply Zmult_lt_compat_r;zarith.
   apply Zle_lt_trans with (([|a2|] - [|b2|]) * wB + (wB -1));zarith.
   replace ( ([|a2|] - [|b2|]) * wB + (wB - 1)) with
     (([|a2|] - [|b2|] + 1) * wB + - 1);w_solve.
   assert (([|a2|] - [|b2|] + 1) * wB <= 0);w_solve.
   replace 0 with (0*wB);zarith.
   replace (([|a2|] - [|b2|]) * wB + [|a3|] + wwB + ([|b1|] * wB + [|b2|]) +
              ([|b1|] * wB + [|b2|]) - wwB) with
         (([|a2|] - [|b2|]) * wB + [|a3|] + 2*[|b1|] * wB + 2*[|b2|]);w_solve.
  rewrite <- (Zmod_unique ([[r]] + ([|b1|] * wB + [|b2|])) wwB
                1 ([[r]] + ([|b1|] * wB + [|b2|]) - wwB));w_solve.
  split. rewrite H1;rewrite Hcmp;ring. trivial.
  assert (H3:= spec_ww_to_Z (WW b1 b2));simpl in H3;zarith.
  intros H1.
  assert ([[r]] = ([|a2|] - [|b2|]) * wB + [|a3|] + ([|b1|] * wB + [|b2|])).
    zarith.
  split. rewrite H2;rewrite Hcmp;ring.
  split. assert (H3:= spec_ww_to_Z r);zarith.
  rewrite H2.
  assert (([|a2|] - [|b2|]) * wB + [|a3|] < 0);zarith.
  apply Zle_lt_trans with (([|a2|] - [|b2|]) * wB + (wB -1));zarith.
   replace ( ([|a2|] - [|b2|]) * wB + (wB - 1)) with
     (([|a2|] - [|b2|] + 1) * wB + - 1);w_solve.
   assert (([|a2|] - [|b2|] + 1) * wB <= 0);w_solve.
   replace 0 with (0*wB);zarith.
 (* Cas Lt *)
  assert (Hdiv21 := spec_div21 op_spec a1 a2 b1 Hle Hcmp);
    destruct (znz_div21 w_op a1 a2 b1) as (q, r);destruct Hdiv21.
  rewrite H.
  assert (Hq := spec_to_Z op_spec q).
  generalize
    (spec_ww_sub_c (znz_WW w_op r a3) (znz_mul_c w_op q b2));
    destruct (ww_sub_c w_op (znz_WW w_op r a3) (znz_mul_c w_op q b2))
    as [r1|r1];w_rewrite.
  intros H1;simpl in H1;rewrite H1.
  split. ring.
  split. rewrite <- H1;destruct (spec_ww_to_Z r1);trivial.
  apply Zle_lt_trans with ([|r|] * wB + [|a3|]).
  assert ( 0 <= [|q|] * [|b2|]).
   assert (H2:= spec_to_Z op_spec q);apply Zmult_le_0_compat;zarith.
  zarith.
  apply beta_lex_inv;w_solve.
  intros H1;assert ([[r1]] = [|r|] * wB + [|a3|] - [|q|] * [|b2|] + wwB).
  rewrite <- H1;ring.
  assert (H3 := spec_ww_to_Z r1); assert (0 <= [|r|]*wB). zarith.
  assert (0 < [|q|] * [|b2|]). zarith.
  assert (0 < [|q|]). 
   apply Zmult_lt_0_reg_r_2 with [|b2|];zarith.
  generalize (spec_ww_add_c r1 (WW b1 b2)); 
   destruct (ww_add_c w_op r1 (WW b1 b2)) as [r2|r2];w_rewrite.
  simpl;intros H7.
  assert (0 < [|q|] - 1).
   assert (1 <= [|q|]). zarith.
   destruct (Zle_lt_or_eq _ _ H8);zarith.
   rewrite <- H9 in H2;rewrite H2 in H7.
   assert (0 < [|b1|]*wB). apply Zmult_lt_0_compat;zarith.
   assert (H11 := spec_ww_to_Z r2). zarith.
  rewrite (Zmod_def_small ([|q|] -1));zarith.
  rewrite (Zmod_def_small ([|q|] -1 -1));zarith.
  assert ([[r2]] + ([|b1|] * wB + [|b2|]) =
       wwB * 1 +
       ([|r|] * wB + [|a3|] - [|q|] * [|b2|] + 2 * ([|b1|] * wB + [|b2|]))).
   rewrite H7;rewrite H2;ring.
  assert 
   ([|r|]*wB + [|a3|] - [|q|]*[|b2|] + 2 * ([|b1|]*wB + [|b2|]) 
       < [|b1|]*wB + [|b2|]).
  assert (H10 := spec_ww_to_Z r2);omega.
  assert (H11 := spec_ww_to_Z (WW b1 b2));simpl in H11.
  assert 
   (0 <= [|r|]*wB + [|a3|] - [|q|]*[|b2|] + 2 * ([|b1|]*wB + [|b2|]) 
       < wwB). split;try omega.
  replace (2 * ([|b1|] * wB + [|b2|])) with ((2*[|b1|]) * wB + 2*[|b2|]).
  2:ring.
  assert (H12:= wB_div2 Hle). assert (wwB <= 2 * [|b1|] * wB).
  rewrite wwB_wBwB;zarith. omega.
  rewrite <- (Zmod_unique 
            ([[r2]] + ([|b1|] * wB + [|b2|]))
            wwB
            1
            ([|r|] * wB + [|a3|] - [|q|] * [|b2|] + 2*([|b1|] * wB + [|b2|]))
            lt_0_wwB
            H12 H9).
  split. ring. zarith.
  intros; rewrite (Zmod_def_small ([|q|] -1));zarith.
  split.
  replace [[r2]] with  ([[r1]] + ([|b1|] * wB + [|b2|]) -wwB).
  rewrite H2; ring. rewrite <- H7; ring.
  assert (H8 := spec_ww_to_Z r2).
  assert (H9 := spec_ww_to_Z r1).
  omega.
  simpl in Hlt.
  assert ([|a1|] * wB + [|a2|] <= [|b1|] * wB + [|b2|]). zarith.
  assert (H1 := beta_lex _ _ H HH1 HH4). zarith.
 Qed.

 Theorem wwB_div: wwB  = 2 * (wwB / 2).
 Proof.
  rewrite wwB_div_2; rewrite  Zmult_assoc; rewrite  wB_div_2; auto.
  apply wwB_wBwB.
 Qed.

 Theorem   spec_ww_div21 : forall a1 a2 b,
     wwB/2 <= [[b]] ->
     [[a1]] < [[b]] ->
     let (q,r) := ww_div21 w_op a1 a2 b in
     [[a1]] *wwB+[[a2]] = [[q]] *  [[b]] + [[r]] /\ 0 <= [[r]] < [[b]].
 Proof.
  assert (U:= lt_0_wB).
  assert (U1:= lt_0_wwB).
  intros a b c H Hlt; unfold ww_div21.
  assert (HH0 := spec_ww_to_Z c).
  assert (Eq: 0 < [[c]]).
   assert (H1 := spec_ww_to_Z a);omega.
  generalize Hlt;clear Hlt;case a.
  case b.
  simpl; autorewrite with rm10; split; auto with zarith.
  intros a1 a2.
  assert (HH := spec_to_Z op_spec a1); assert (HH1 :=spec_to_Z op_spec a2).
  match goal with |-context [ww_compare ?X ?Y ?Z] =>
    generalize (spec_ww_compare Y Z); case (ww_compare X Y Z)
  end.
  simpl; w_rewrite1; autorewrite with rm10; auto with zarith.
  simpl; w_rewrite1; autorewrite with rm10; auto with zarith.
  simpl; w_rewrite1; autorewrite with rm10; auto with zarith.
  assert (Eq1: [|a1|] * wB + [|a2|] < wwB); auto with zarith.
  generalize (spec_ww_to_Z (WW a1 a2)); simpl; auto with zarith.
  intros H1; rewrite Zmod_def_small; auto with zarith.
  split; auto with zarith.
  split; auto with zarith.
  assert ([|a1|] * wB + [|a2|] < 2 * [[c]]); auto with zarith.
  apply Zlt_le_trans with (1:= Eq1).
  rewrite wwB_div; auto with zarith.
  split; auto with zarith.
  rewrite <- wwB_wBwB; auto with zarith.
  intros a1 a2.
  assert (HH:=spec_to_Z op_spec a1);assert (HH1 := spec_to_Z op_spec a2).
  match goal with |- context [ww_split ?X ?Y] =>
    generalize (spec_ww_split Y); case (ww_split X Y)
  end.
  intros a3 a4; simpl fst; simpl snd; intros Hb.
  assert (HH2:=spec_to_Z op_spec a3); assert (HH3:=spec_to_Z op_spec a4).
  match goal with |- context [ww_split ?X ?Y] =>
    generalize (spec_ww_split Y); case (ww_split X Y)
  end.
  intros b1 b2; simpl fst; simpl snd; intros Hc Hlt.
  rewrite Hc in Hlt;simpl in Hlt.
  assert (HH4 := spec_to_Z op_spec b1);assert (HH5 := spec_to_Z op_spec b2).
  match goal with |-context [w_div32 ?K ?X ?Y ?Z ?T ?U] =>
    generalize (spec_w_div32 X Y Z T U); case (w_div32 K X Y Z T U)
  end.
  assert (Eq1: wB / 2 <= [|b1|]).
  apply (@wB_lex  (wB / 2) 0 [|b1|] [|b2|]); auto with zarith.
  autorewrite with rm10; repeat rewrite (Zmult_comm wB).
  rewrite <- wwB_div_2; rewrite <- Hc; auto with zarith.
  intros q1 r V1; case V1; clear V1; try intros V1 V2; auto. 
  generalize V2;clear V2.
  match goal with |- context [ww_split ?X ?Y] =>
    generalize (spec_ww_split Y); case (ww_split X Y)
  end.
  intros r1 r2; simpl fst; simpl snd; intros Hr V2.
  match goal with |-context [w_div32 ?K ?X ?Y ?Z ?T ?U] =>
    generalize (spec_w_div32 X Y Z T U); case (w_div32 K X Y Z T U)
  end.
  intros q2 s V3; case V3; clear V3; auto; try intros V3 V4.
  rewrite Hr in V2;simpl in * ;zarith. 
  split; auto with zarith.
  w_rewrite1;rewrite Hb; rewrite Hc.
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
 Proof. unfold base; trivial. Qed.

 Theorem wwB_power: wwB = 2 ^ (Zpos wdigits).
 Proof. trivial. Qed.
 
 Theorem spec_ww_head0  : forall x, 
      0 < [[x]] -> 
      wwB/ 2 <= 2 ^ (Z_of_N (ww_head0 w_op x)) * [[x]] < wwB. 
 Proof.
  intros x; case x; simpl. 
  intros H; contradict H; auto with zarith.
  intros xh xl H.
  generalize (spec_to_Z op_spec xh); intros HH; rewrite wB_power in HH.
  generalize (spec_to_Z op_spec xl); intros HH1; rewrite wB_power in HH1.
  assert (Hl := spec_compare op_spec xh (znz_0 w_op));
  destruct (znz_compare w_op xh (znz_0 w_op)).
  generalize Hl; w_rewrite1; clear Hl; intros Hl.
  generalize H; rewrite Hl; autorewrite with rm10; clear H; intros H.
  assert (Hl1 := spec_head0 op_spec xl);
  destruct (znz_head0 w_op xl).
  simpl in Hl1; rewrite Zmult_1_l in Hl1.
  generalize (wB_power);simpl;unfold digits;intros tmp;rewrite <-tmp;clear tmp.
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
  generalize (Zpower_exp 2 (Zpos digits) (Zpos p)); simpl; auto with zarith.
  intros tmp; rewrite <- tmp; auto with zarith.
  generalize Hl; w_rewrite1; clear Hl;intros Hl;contradict Hl;auto with zarith.
  generalize Hl; w_rewrite1; clear Hl; intros Hl.
  assert (Hl1 := spec_head0 op_spec xh);  destruct (znz_head0 w_op xh).
  simpl in Hl1; rewrite Zmult_1_l in Hl1.
  simpl; rewrite Zmult_1_l.
  split; auto with zarith.
  apply Zle_trans with ([|xh|] * wB); auto with zarith.
  rewrite <- wwB_wBwB; rewrite wwB_div_2.
  apply Zmult_le_compat_r; auto with zarith.
  rewrite <- (Zplus_0_r (wB * wB));  apply wB_lex_inv; auto with zarith.
  simpl Z_of_N in Hl1;  simpl Z_of_N.
  split; auto with zarith.
  apply Zle_trans with  (2 ^Zpos p * [|xh|] * wB); auto with zarith.
  rewrite <- wwB_wBwB; rewrite wwB_div_2.
  apply Zmult_le_compat_r; auto with zarith.
  rewrite wB_power; auto with zarith.
  rewrite <- Zmult_assoc.
  apply Zmult_le_compat_l; auto with zarith.
  assert (Eq1: 2 ^ Zpos p  < wB).
  rewrite <- (Zmult_1_r (2 ^ Zpos p));
     apply Zle_lt_trans with (2 ^Zpos p * [|xh|]); auto with zarith.
  assert (Eq2: Zpos p < Zpos digits).
  case (Zle_or_lt (Zpos digits) (Zpos p)); auto with zarith; intros H1.
  contradict  Eq1; apply Zle_not_lt.
  rewrite wB_power; apply Zpower_le_monotone; auto with zarith.
  pattern wB at 2; replace wB with (2 ^ Zpos p * 2 ^ (Zpos digits - Zpos p)).
  rewrite <- Zmult_assoc; apply Zmult_lt_compat_l; auto with zarith.
  rewrite <- (Zplus_0_r (2 ^ (Zpos digits - Zpos p) * wB)); 
    apply wB_lex_inv; auto with zarith.
  apply Zmult_lt_reg_r with (2 ^ Zpos p); auto with zarith.
  repeat rewrite (fun x => Zmult_comm x (2 ^ Zpos p)).
  rewrite <- Zpower_exp; auto with zarith.
  assert (tmp: forall x y , x + (y - x) = y);try rewrite tmp; zarith;clear tmp.
  rewrite <- wB_power; auto with zarith.
  rewrite wB_power; auto with zarith.
  rewrite <- Zpower_exp; auto with zarith.
  assert (tmp: forall x y , x + (y - x) = y); try rewrite tmp;zarith;clear tmp.
 Qed.

 Theorem spec_ww_add_mul_div_aux : forall xh xl yh yl p,
   Zpos p < Zpos wdigits ->
   [[match (p ?= znz_digits w_op)%positive Eq with
          | Eq => znz_WW w_op xl yh
          | Lt =>
              znz_WW w_op (znz_add_mul_div w_op p xh xl)
                (znz_add_mul_div w_op p xl yh)
          | Gt =>
              znz_WW w_op (znz_add_mul_div w_op (p - znz_digits w_op) xl yh)
                (znz_add_mul_div w_op (p - znz_digits w_op) yh yl)
          end]] =
    ([[WW xh xl]] * 2 ^ Zpos p + 
         [[WW yh yl]] / 2 ^ (Zpos wdigits - Zpos p)) mod wwB.
 Proof.
  assert (U:= lt_0_wB); assert (U1:=lt_0_wwB).
  assert (U2:Zpos digits < Zpos wdigits).
  unfold wdigits, digits, base; rewrite Zpos_xO; auto with zarith.
  assert (1 <= Zpos (znz_digits w_op)); auto with zarith.
  case (znz_digits w_op); compute; auto; intros; discriminate.
  assert (U3:2 ^ (Zpos digits) < 2 ^ (Zpos wdigits)).
  apply Zpower_lt_monotone; auto with zarith.
  assert (U4: Zpos wdigits = 2 * Zpos digits).
  replace wdigits with (xO digits);  auto; rewrite Zpos_xO.
  assert (U5: Zpos wdigits = Zpos digits + Zpos digits); auto with zarith.
  intros xh xl yh yl p Hp.
  generalize (spec_to_Z op_spec xh); intros HH; rewrite wB_power in HH.
  generalize (spec_to_Z op_spec xl); intros HH1; rewrite wB_power in HH1.
  generalize (spec_to_Z op_spec yh); intros HH2; rewrite wB_power in HH2.
  generalize (spec_to_Z op_spec yl); intros HH3; rewrite wB_power in HH3.
  assert (U6: Zpos wdigits = Zpos (wdigits - p) + Zpos p).
  rewrite Zpos_minus; auto with zarith.
  assert (U7: Zpos digits = Zpos p + (Zpos digits - Zpos p)); try (ring; fail).
  assert (U8: Zpos digits = Zpos digits - Zpos p + Zpos p); try (ring; fail).
  match goal with |- context [(?X ?= ?Y)%positive Eq] => 
       case_eq (Pcompare X Y Eq) end; intros H1;auto with zarith.
  assert (E1: Zpos p = Zpos digits); auto.
  rewrite Pcompare_Eq_eq with (1:= H1); auto with zarith.
  rewrite E1.
  rewrite wwB_power.
  replace (Zpos wdigits - Zpos digits) with (Zpos digits); auto with zarith.
  2: rewrite U5; ring.
  w_rewrite1.
  repeat rewrite (Zmult_comm wB).
  rewrite wB_power.
  rewrite Zdiv_shift_r; auto with zarith.
  rewrite Zmod_shift_r; auto with zarith.
  2: split; auto with zarith.
  2: apply Zdiv_lt_upper_bound; try rewrite Zpower_exp; auto with zarith.
  2: apply Zmult_lt_compat_r; auto with zarith.
  rewrite Z_div_mult; auto with zarith.
  autorewrite with distr.
  rewrite <- Zmult_assoc; rewrite <- Zpower_exp; auto with zarith.
  rewrite <- U5.
  rewrite Zmod_shift_r; auto with zarith.
  rewrite Zmod_mult_0; auto with zarith.
  rewrite U5; rewrite Zpower_exp; auto with zarith.
  split; auto with zarith.
  apply Zmult_lt_compat_r; auto with zarith.
  assert (Eq1: Zpos p < Zpos digits); auto.
  rewrite wwB_power.
  w_rewrite1.
  repeat rewrite (Zmult_comm wB).
  repeat rewrite (spec_add_mul_div op_spec);autorewrite with rm10; zarith.
  rewrite wB_power; fold digits.
  rewrite Zmod_shift_r; auto with zarith.
  2: split; auto with zarith.
  2: apply Zdiv_lt_upper_bound; try rewrite Zpower_exp; auto with zarith.
  2: rewrite <- Zpower_exp; try (rewrite <- U7); auto with zarith.
  rewrite Zmod_shift_r; auto with zarith.
  2: split; auto with zarith.
  2: apply Zdiv_lt_upper_bound; try rewrite Zpower_exp; auto with zarith.
  2: rewrite <- Zpower_exp; try (rewrite <- U7); auto with zarith.
  rewrite Zdiv_shift_r; auto with zarith.
  replace (Zpos digits + Zpos digits - Zpos p) with 
       ((Zpos digits - Zpos p) + Zpos digits); try (ring; fail).
  rewrite Zpower_exp; auto with zarith.
  rewrite Zdiv_Zmult_compat_r; auto with zarith.
  rewrite Zmod_shift_r; auto with zarith.
  2: split; auto with zarith.
  2: apply Zdiv_lt_upper_bound; try rewrite Zpower_exp; auto with zarith.
  2: rewrite <- Zpower_exp; try (rewrite <- U7); auto with zarith.
  rewrite U6; rewrite Zpos_minus; auto with zarith.
  rewrite Zpower_exp; auto with zarith; rewrite Zmult_mod_distr_r; zarith.
  rewrite Zmod_shift_r; auto with zarith.
  pattern (Zpos digits) at 3 4; rewrite U8; rewrite Zpower_exp; zarith.
  rewrite Zmult_mod_distr_r; auto with zarith.
  pattern [|xl|] at 3; rewrite Z_div_mod_eq with 
       (b := 2 ^ (Zpos digits - Zpos p)); auto with zarith.
  pattern (Zpos p) at 5; rewrite U7.
  replace (Zpos wdigits - Zpos p) with (Zpos digits + (Zpos digits - Zpos p)).
  repeat rewrite Zpower_exp; auto with zarith.
  repeat rewrite Zmult_assoc; rewrite Zmult_mod_distr_r; auto with zarith.
  repeat rewrite <- Zpower_exp; auto with zarith.
  rewrite <- U7; ring.
  rewrite U5; ring.
  assert (Eq1: Zpos p > Zpos digits); auto.
  assert (Eq2: Zpos digits - (Zpos p - Zpos digits) = Zpos wdigits - Zpos p).
  rewrite U5; ring.
  assert(Eq3: Zpos(p - digits) < Zpos digits); auto with zarith.
  rewrite Zpos_minus; auto with zarith.
  rewrite wwB_power.
  w_rewrite1.
  repeat rewrite (Zmult_comm wB).
  rewrite wB_power.
  repeat rewrite (spec_add_mul_div op_spec); autorewrite with rm10; zarith.
  rewrite wB_power; fold digits.
  repeat rewrite Zpos_minus; try rewrite Eq2; auto with zarith.
  rewrite Zmod_shift_r; auto with zarith.
  2: split; auto with zarith.
  2: apply Zdiv_lt_upper_bound; try rewrite Zpower_exp; auto with zarith.
  2: rewrite <- Zpower_exp; try (rewrite <- U7); auto with zarith.
  2: match goal with |- _ < 2  ^ ?X => replace X with (Zpos digits);zarith end.
  rewrite Zmod_shift_r; auto with zarith.
  2: split; auto with zarith.
  2: apply Zdiv_lt_upper_bound; try rewrite Zpower_exp; auto with zarith.
  2: rewrite <- Zpower_exp; try (rewrite <- U7); auto with zarith.
  2: match goal with |- _ < 2  ^ ?X => replace X with (Zpos digits);zarith end.
  rewrite Zmod_shift_r; auto with zarith.
  2: split; auto with zarith.
  2: apply Zdiv_lt_upper_bound; try rewrite Zpower_exp; auto with zarith.
  2: rewrite <- Zpower_exp; auto with zarith.
  2:match goal with |- _ < 2  ^ ?X => replace X with (Zpos wdigits);zarith end.
  2: generalize (spec_ww_to_Z (WW yh yl)); simpl; rewrite wwB_power;
      rewrite wB_power; simpl; auto with zarith.
  pattern (Zpos wdigits) at 3; rewrite U6; rewrite Zpower_exp;zarith.
  rewrite Zmult_mod_distr_r; auto with zarith.
  repeat rewrite Zpos_minus; auto with zarith.
  rewrite Zmod_plus; auto with zarith.
  pattern (Zpos digits) at 6; replace (Zpos digits) with 
	(Zpos p - Zpos digits + (Zpos wdigits - Zpos p)).
  2: rewrite <- Eq2; ring.
  rewrite Zpower_exp; auto with zarith.
  rewrite Zmult_assoc; rewrite Zmod_mult_0; zarith; autorewrite with rm10.
  rewrite Zmod_mod; auto with zarith.
  pattern (Zpos digits) at 2; replace 
	(Zpos digits) with (Zpos wdigits - Zpos p + (Zpos p - Zpos digits) ).
  rewrite Zpower_exp; auto with zarith.
  rewrite Zmult_mod_distr_r; auto with zarith.
  2: rewrite <- Eq2; ring.
  autorewrite with distr.
  rewrite <- Zmult_assoc; rewrite <- Zpower_exp; auto with zarith.
  replace (Zpos p - Zpos digits + Zpos digits) with (Zpos p); try (ring; fail).
  pattern (Zpos digits) at 1; replace (Zpos digits) with 
	(Zpos wdigits - Zpos p + (Zpos p - Zpos digits)); 
	try (rewrite <- Eq2; ring; fail).
  rewrite Zpower_exp; auto with zarith.
  rewrite Zmult_assoc.
  pattern (Zpos digits) at 3; replace (Zpos digits) with 
	(Zpos wdigits - Zpos p + (Zpos p - Zpos digits)); 
	try (rewrite <- Eq2; ring; fail).
  rewrite Zpower_exp; auto with zarith.
  rewrite Zmult_mod_distr_r; auto with zarith.
  match goal with |- ?X + ?Y * ?X1 * ?X2  + (?T  * ?X2 + ?U) = _ =>
    apply trans_equal with (X + (X1 * Y + T)  * X2 + U); 
    [ring | rewrite <- Z_div_mod_eq]
  end; auto with zarith.
  pattern (Zpos digits) at 2; replace (Zpos digits) with 
  	(Zpos p - Zpos digits + (Zpos wdigits - Zpos p)).
  2: rewrite <- Eq2; ring.
  rewrite Zpower_exp; auto with zarith.
  rewrite Zmult_assoc.
  rewrite Z_div_plus_l; auto with zarith.
 Qed.

 Theorem spec_ww_add_mul_div : forall x y p,
    Zpos p < Zpos wdigits ->
    [[ ww_add_mul_div w_op p x y]] =
    ([[x]] * (2 ^ (Zpos p)) + [[y]] / (2 ^ (Zpos wdigits - (Zpos p)))) mod wwB.
 Proof.
  intros x y p H.
  generalize (@spec_ww_add_mul_div_aux 
                  (fst (ww_split w_op x)) (snd (ww_split w_op x))
                  (fst (ww_split w_op y)) (snd (ww_split w_op y)) p H).
  case x; case y; auto.
  intros w1 w2; simpl.
  match goal with |- context [(?X ?= ?Y)%positive Eq] =>
       case_eq (Pcompare X Y Eq) end; intros H1.
  w_rewrite1; autorewrite with rm10; auto.
  w_rewrite1; autorewrite with rm10; auto.
  intros H2; rewrite <- H2. 
  rewrite (spec_add_mul_div op_spec (znz_0 w_op)(znz_0 w_op));
     autorewrite with rm10; auto with zarith.
  w_rewrite1; autorewrite with rm10; auto with zarith.
  auto.
  w_rewrite1; autorewrite with rm10; auto.
  intros w1 w2; simpl.
  match goal with |- context [(?X ?= ?Y)%positive Eq] =>
       case_eq (Pcompare X Y Eq) end; intros H1.
  w_rewrite1; autorewrite with rm10; auto.
  w_rewrite1; autorewrite with rm10; auto.
  w_rewrite1; autorewrite with rm10; auto.
  assert (H2: Zpos p > Zpos digits); auto.
  intros H3; rewrite <- H3. 
  rewrite (spec_add_mul_div op_spec (znz_0 w_op)(znz_0 w_op));
      autorewrite with rm10; auto with zarith.
  w_rewrite1; autorewrite with rm10; auto with zarith.
  rewrite Zpos_minus; auto with zarith.
  generalize H; replace (Zpos wdigits) with
    (Zpos digits + Zpos digits); auto with zarith.
  fold digits; auto with zarith.
  replace wdigits with (xO (digits)); auto; rewrite Zpos_xO; ring.
  fold digits; auto with zarith.
 Qed.

 Hint Resolve 
   spec_ww_WW spec_ww_head0 spec_ww_add_mul_div spec_ww_div21 : ww_spec.

 Lemma spec_ww_pos_mod : forall w p,
       [[ww_pos_mod w_op p w]] = [[w]] mod (2 ^ Zpos p).
 assert (F0: forall x y, x - y + y = x); auto with zarith.
 intros w1 p; unfold ww_pos_mod; case w1.
 autorewrite with w_rewrite; rewrite Zmod_def_small; auto with zarith.
  match goal with |- context [(?X ?= ?Y)%positive Eq] =>
       case_eq (Pcompare X Y Eq) end; intros H1.
 assert (E1: Zpos p = Zpos digits); auto.
 rewrite Pcompare_Eq_eq with (1:= H1); auto with zarith.
 rewrite E1.
 intros xh xl; autorewrite with w_rewrite rm10.
 match goal with |- context id [2 ^Zpos digits] =>
   let v := context id [wB] in change v
 end.
 rewrite Zmod_plus; auto with zarith.
 rewrite Zmod_mult_0; auto with zarith.
 autorewrite with rm10.
 rewrite Zmod_mod; auto with zarith.
 rewrite Zmod_def_small; auto with zarith.
 apply spec_to_Z; auto.
 assert (Eq1: Zpos p < Zpos digits); auto.
 intros xh xl; autorewrite with w_rewrite rm10.
 rewrite spec_pos_mod; auto with zarith.
 assert (Eq2: Zpos p + (Zpos digits - Zpos p) = Zpos digits); auto with zarith.
 unfold base; unfold digits in Eq1; unfold digits in Eq2; rewrite <- Eq2.
 rewrite Zpower_exp; auto with zarith.
 rewrite (fun x => (Zmult_comm (2 ^ x))); rewrite Zmult_assoc.
 rewrite Zmod_plus; auto with zarith.
 rewrite Zmod_mult_0; auto with zarith.
 autorewrite with rm10.
 rewrite Zmod_mod; auto with zarith.
 assert (Eq1: Zpos p > Zpos digits); auto.
 intros xh xl; autorewrite with w_rewrite rm10.
 rewrite spec_pos_mod; auto with zarith.
 pattern [|xh|] at 2; rewrite Z_div_mod_eq with (b := 2 ^ Zpos (p - znz_digits w_op));
  auto with zarith.
 rewrite (fun x => (Zmult_comm (2 ^ x))); rewrite Zmult_plus_distr_l.
 unfold base; rewrite <- Zmult_assoc; rewrite <- Zpower_exp;
    auto with zarith.
 unfold digits in Eq1; rewrite Zpos_minus; auto with zarith.
 rewrite F0; auto with zarith.
 rewrite <- Zplus_assoc; rewrite Zmod_plus; auto with zarith.
 rewrite Zmod_mult_0; auto with zarith.
 autorewrite with rm10.
 rewrite Zmod_mod; auto with zarith.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 case (spec_to_Z op_spec xh); intros U1 U2.
 case (spec_to_Z op_spec xl); intros U3 U4.
 split; auto with zarith.
 apply Zplus_le_0_compat; auto with zarith.
 apply Zmult_le_0_compat; auto with zarith.
 match goal with |- 0 <= ?X mod ?Y =>
  case (Z_mod_lt X Y); auto with zarith
 end.
 match goal with |- ?X mod ?Y * ?U + ?Z < ?T =>
  apply Zle_lt_trans with ((Y - 1) * U + Z );
   [case (Z_mod_lt X Y); auto with zarith | idtac]
 end.
 match goal with |- ?X * ?U + ?Y < ?Z =>
  apply Zle_lt_trans with (X * U + (U - 1))
 end.
 apply Zplus_le_compat_l; auto with zarith.
 case (spec_to_Z op_spec xl); unfold base; auto with zarith.
 rewrite Zmult_minus_distr_r; rewrite <- Zpower_exp; auto with zarith.
 rewrite F0; auto with zarith.
 Qed.
   
 Lemma spec_ww_divn1 : forall n a b, 0 < [[b]] ->
    let (q,r) := ww_divn1 w_op n a b in
    ([!n|word_of_word_tr (zn2z w) n a!]) = [!n|q!] * [[b]] + [[r]] /\
     0 <= [[r]] < [[b]].
 Proof.
  intros n a b Hlt;unfold ww_divn1.
  assert (Hs := spec_ww_split b);destruct (ww_split w_op b) as (b1,b2);
  simpl in Hs.
  assert (Hc := spec_compare op_spec b1 (znz_0 w_op));destruct 
    (znz_compare w_op b1 (znz_0 w_op)).
  rewrite Hc in Hs;rewrite (spec_0 op_spec) in Hs;rewrite Zmult_0_l in Hs;
   rewrite Zplus_0_l in Hs;rewrite Hs in Hlt.
  assert (Hd := spec_divn1 op_spec (S n) a b2 Hlt);destruct 
     (znz_divn1 w_op (S n) a b2) as (q,r).
  rewrite gen_to_Z_S in Hd;rewrite gen_to_Z_S_case in Hd;
   fold (ww_to_Z w_op) in Hd.
  destruct Hd as (Heq,H1);rewrite Heq. w_rewrite. rewrite Hs.
  rewrite Zmult_0_l;rewrite Zplus_0_l;auto.
  generalize Hc;w_rewrite;intros;assert (H := spec_to_Z op_spec b1);
   elimtype False;omega.
(********** BEUUUUUUUUUUUUURK ****)
  replace
      (match word_tr_word (zn2z w) n in (_ = y) return y with
      | refl_equal => a
      end) with (word_of_word_tr (zn2z w) n a).
  apply spec_gen_divn1;auto with ww_spec.
  intros; apply spec_ww_add_mul_div; auto with zarith.
  unfold wdigits; auto with zarith.
  exact spec_ww_div21.
  unfold word_of_word_tr; simpl.
  case (word_tr_word (zn2z w) n); auto.
 Qed.

 Lemma to_Z_div_minus_p : forall x p,
   Zpos p < Zpos (znz_digits w_op) ->
   0 <= [|x|] / 2 ^ (Zpos (znz_digits w_op) - Zpos p) < 2 ^ Zpos p.
 Proof.
  intros x p H;assert (H0 := spec_to_Z op_spec x).
  split. apply Zdiv_le_lower_bound;zarith.
  apply Zdiv_lt_upper_bound;zarith.
  rewrite <- Zpower_exp;zarith.
  replace (Zpos p + (Zpos (znz_digits w_op) - Zpos p)) with 
    (Zpos (znz_digits w_op));try ring.
  unfold base in H0;zarith.
 Qed.
 Hint Resolve to_Z_div_minus_p : zarith.

 Lemma spec_ww_div_gt_aux : forall a b bh bl,
      [[a]] > [[b]] ->
      [[b]] = [|bh|]*wB + [|bl|] ->
      0 < [|bh|] ->
      let (q,r) := ww_div_gt_aux w_op a b bh bl in
      [[a]] = [[q]] * [[b]] + [[r]] /\
      0 <= [[r]] < [[b]].
 Proof.
  intros a b bh bl Hgt Heq Hpos;unfold ww_div_gt_aux.
  assert (Hh := spec_head0 op_spec bh Hpos); destruct (znz_head0 w_op bh).
  simpl Z_of_N in Hh; rewrite Zpower_exp_0 in Hh; rewrite Zmult_1_l in Hh;destruct Hh.
  assert (wwB <= 2*[[b]]).
   rewrite Heq. apply Zle_trans with (2*[|bh|]*wB).
   rewrite wwB_wBwB; apply Zmult_le_compat_r; zarith.
   rewrite <- wB_div_2; apply Zmult_le_compat_l; zarith.
   replace (2*([|bh|]*wB + [|bl|])) with (2*[|bh|]*wB + 2*[|bl|]);try ring.
   assert (H1 := spec_to_Z op_spec bl);zarith.
  assert (H2 := spec_ww_to_Z a).
  simpl;w_rewrite;rewrite Zmult_0_l; autorewrite with rm10;
  rewrite Zmod_def_small;split;zarith.
  unfold Z_of_N in Hh.
  assert (Hsplita := spec_ww_split a);destruct (ww_split w_op a) as (ah,al).
  simpl in Hsplita. 
  assert (H: Zpos p < Zpos (znz_digits w_op)).
   destruct (Z_lt_ge_dec  (Zpos p) (Zpos (znz_digits w_op)));trivial.
   elimtype False.
   assert (2 ^ Zpos p * [|bh|] >= wB);auto with zarith.
   apply Zle_ge; replace wB with (wB * 1);try ring.
   assert (H:= spec_to_Z op_spec bh);apply Zmult_le_compat;zarith.
   unfold base;apply Zpower_le_monotone;zarith.
  generalize (spec_add_mul_div op_spec (znz_0 w_op) ah H)
   (spec_add_mul_div op_spec ah al H)
   (spec_add_mul_div op_spec al (znz_0 w_op) H)
   (spec_add_mul_div op_spec bh bl H)
   (spec_add_mul_div op_spec bl (znz_0 w_op) H);
  rewrite (spec_0 op_spec); repeat rewrite Zmult_0_l;repeat rewrite Zplus_0_l;
  rewrite Zdiv_0;repeat rewrite Zplus_0_r.
  assert (H1 := spec_to_Z op_spec ah);assert (H2 := spec_to_Z op_spec bh).
  unfold base;repeat rewrite Zmod_shift_r;zarith.
  2:apply Zpower_lt_0;zarith.
  assert (H3 := to_Z_div_minus_p ah H);assert (H4 := to_Z_div_minus_p al H);
  assert (H5 := to_Z_div_minus_p bl H).
  rewrite Zmult_comm in Hh. 
  assert (2^Zpos p < wB). unfold base;apply Zpower_lt_monotone;zarith.
  unfold base in H0;rewrite Zmod_def_small;zarith.
  fold wB; rewrite (Zmod_def_small ([|bh|] * 2 ^ Zpos p));zarith.
  assert (F: 0 < Zpos (znz_digits w_op)); auto with zarith.
  red; auto with zarith.
  intros U1 U2 U3 V1 V2.
  generalize (spec_w_div32(znz_add_mul_div w_op p (znz_0 w_op) ah)
              (znz_add_mul_div w_op p ah al)
              (znz_add_mul_div w_op p al (znz_0 w_op))
              (znz_add_mul_div w_op p bh bl)
              (znz_add_mul_div w_op p bl (znz_0 w_op))).
  destruct (w_div32 w_op (znz_add_mul_div w_op p (znz_0 w_op) ah)
             (znz_add_mul_div w_op p ah al)
             (znz_add_mul_div w_op p al (znz_0 w_op))
             (znz_add_mul_div w_op p bh bl)
             (znz_add_mul_div w_op p bl (znz_0 w_op))) as (q,r).
  rewrite V1;rewrite V2. rewrite Zmult_plus_distr_l. 
  rewrite <- (Zplus_assoc ([|bh|] * 2 ^ Zpos p * wB)). 
  unfold base;rewrite <- shift_unshift_mod;zarith. fold wB.
  replace ([|bh|] * 2 ^ Zpos p * wB + [|bl|] * 2 ^ Zpos p) with
   ([[b]] * 2^Zpos p). 2:rewrite Heq;ring.
  fold wwB. rewrite wwB_wBwB. rewrite U1;rewrite U2;rewrite U3.
  rewrite Zmult_assoc. rewrite Zmult_plus_distr_l. 
  rewrite (Zplus_assoc ([|ah|] / 2^(Zpos(znz_digits w_op) - Zpos p)*wB*wB)).
  rewrite <- Zmult_plus_distr_l.  rewrite <- Zplus_assoc. 
  unfold base;repeat rewrite <- shift_unshift_mod;zarith. fold wB.
  replace ([|ah|] * 2 ^ Zpos p * wB + [|al|] * 2 ^ Zpos p) with
   ([[a]] * 2^Zpos p). 2:rewrite Hsplita;ring.
  intros Hd;destruct Hd;zarith.
  simpl. apply beta_lex_inv;zarith. rewrite U1;rewrite V1.
  assert ([|ah|] / 2 ^ (Zpos (znz_digits w_op) - Zpos p) < wB/2);zarith.
  apply Zdiv_lt_upper_bound;zarith.
  unfold base.
  replace (2^Zpos (znz_digits w_op)) with (2^(Zpos (znz_digits w_op) - 1)*2).
  rewrite Z_div_mult;zarith.  rewrite <- Zpower_exp;zarith.
  apply Zlt_le_trans with wB;zarith.
  unfold base;apply Zpower_le_monotone;zarith.
  pattern 2 at 2;replace 2 with (2^1);trivial.
  rewrite <- Zpower_exp;zarith. ring (Zpos (znz_digits w_op) - 1 + 1);trivial.
  w_rewrite. 
  rewrite Zmult_0_l;rewrite Zplus_0_l.
  replace [[ww_add_mul_div w_op (xO (znz_digits w_op) - p) W0 r]] with
   ([[r]]/2^Zpos p).
  assert (0 < 2^Zpos p). apply Zpower_lt_0;zarith.
  split.
  rewrite <- (Z_div_mult [[a]] (2^Zpos p));zarith.
  rewrite H6;rewrite Zmult_assoc;apply Z_div_plus_l;trivial.
  split;[apply Zdiv_le_lower_bound| apply Zdiv_lt_upper_bound];zarith.
  rewrite spec_ww_add_mul_div;rewrite Zpos_minus;unfold wdigits;
   change (Zpos (xO (znz_digits w_op))) with (2*Zpos (znz_digits w_op));zarith.
  rewrite spec_ww_0;rewrite Zmult_0_l;rewrite Zplus_0_l.
  ring (2*Zpos (znz_digits w_op)-(2*Zpos (znz_digits w_op) - Zpos p));trivial.
  rewrite Zmod_def_small;zarith.
  split;[apply Zdiv_le_lower_bound| apply Zdiv_lt_upper_bound];zarith.
  assert (H8 := spec_ww_to_Z r).
  apply Zlt_le_trans with wwB;zarith.
  rewrite <- (Zmult_1_r wwB);apply Zmult_le_compat;zarith.
  assert (0 < Zpos p);zarith.
 Qed.

 Lemma spec_ww_div_gt : forall a b, [[a]] > [[b]] -> 0 < [[b]] ->
      let (q,r) := ww_div_gt w_op a b in
      [[a]] = [[q]] * [[b]] + [[r]] /\
      0 <= [[r]] < [[b]].
 Proof.
  intros a b Hgt Hpos;unfold ww_div_gt. 
  assert (Hsplit := spec_ww_split b);destruct (ww_split w_op b) as (bh,bl).
  fold (ww_div_gt_aux w_op a b bh bl).
  assert (Hcmp := spec_compare op_spec (znz_0 w_op) bh);
   destruct (znz_compare w_op (znz_0 w_op) bh).
  assert (Hsplita := spec_ww_split a);destruct (ww_split w_op a) as (ah,al).
  assert (Hcmpa := spec_compare op_spec (znz_0 w_op) ah);
   destruct (znz_compare w_op (znz_0 w_op) ah).
  assert (Hd := spec_div_gt op_spec al bl);
   destruct (znz_div_gt w_op al bl) as (q,l).
  generalize Hgt Hpos;clear Hgt Hpos.
  rewrite Hsplit;rewrite Hsplita;simpl;rewrite <- Hcmp;rewrite <- Hcmpa.
  w_rewrite;repeat rewrite Zmult_0_l;repeat rewrite Zplus_0_l;trivial.
  generalize Hpos;clear Hpos;rewrite Hsplit;simpl;rewrite <- Hcmp;w_rewrite;
   repeat rewrite Zmult_0_l;repeat rewrite Zplus_0_l;intros Hlt.
  assert (Hd := spec_divn1 op_spec 1 a bl Hlt).
  destruct (znz_divn1 w_op 1 a bl) as (q,r).
  rewrite gen_to_Z_S in Hd. simpl in Hd;unfold gen_wB in Hd;simpl in Hd.
  fold (ww_to_Z w_op) in Hd. unfold word_of_word_tr in Hd;simpl in Hd.
  w_rewrite;trivial.
  generalize Hcmpa;w_rewrite;intros;assert (H := spec_to_Z op_spec ah);
   elimtype False;omega.
  rewrite(spec_0 op_spec)in Hcmp;simpl in Hsplit;apply spec_ww_div_gt_aux;auto.
  generalize Hcmp;w_rewrite;intros;assert (H := spec_to_Z op_spec bh);
   elimtype False;omega.
 Qed.

 Lemma spec_ww_div : forall a b, 0 < [[b]] ->
      let (q,r) := ww_div w_op a b in
      [[a]] = [[q]] * [[b]] + [[r]] /\
      0 <= [[r]] < [[b]].
 Proof.
  intros a b Hpos;unfold ww_div.
  assert (H:=spec_ww_compare a b);destruct (ww_compare w_op a b).
  simpl;w_rewrite;split;zarith. rewrite H;ring.
  simpl;split;[ring|assert (H1 := spec_ww_to_Z a);zarith].
  apply spec_ww_div_gt;trivial.
 Qed.

 Lemma spec_w_modn1_eq : forall n a b, 0 <[|b|] ->
   [|znz_modn1 w_op n a b|] = [|snd (znz_divn1 w_op n a b)|].
 Proof.
  intros n a b Hpos.
  rewrite (spec_modn1 op_spec);trivial.
  assert (H:=spec_divn1 op_spec n a b Hpos).
  destruct (znz_divn1 w_op n a b) as (q,r);simpl.
  rewrite Zmult_comm in H;destruct H.
  symmetry;apply Zmod_unique with 
      (gen_to_Z (znz_digits w_op) (znz_to_Z w_op) n q);auto.
 Qed.

 Lemma spec_ww_modn1_eq : forall n a b, 0 <[[b]] ->
      [[ww_modn1 w_op n a b]] = [[snd (ww_divn1 w_op n a b)]].
 Proof.
  intros n a b Hpos; unfold ww_modn1, ww_divn1.
  assert (H:= spec_ww_split b);destruct (ww_split w_op b) as (bh, bl).
  simpl in H.
  assert (H0 := spec_compare op_spec bh (znz_0 w_op)).
  destruct (znz_compare w_op bh (znz_0 w_op)).
  rewrite H in Hpos;rewrite H0 in Hpos;rewrite (spec_0 op_spec) in Hpos.
  rewrite Zmult_0_l in Hpos;rewrite Zplus_0_l in Hpos.
  assert (H1:=spec_w_modn1_eq (S n) a bl Hpos);
   destruct(znz_divn1 w_op (S n) a bl). simpl in *. w_rewrite.
  rewrite H1;ring.
  rewrite (spec_0 op_spec) in H0;assert (H1 := spec_to_Z op_spec bh);
   elimtype False;omega.
  rewrite <- spec_gen_modn1_aux;trivial.
 Qed.

 Lemma spec_ww_modn1 : forall n a b, 0 < [[b]] ->
      [[ww_modn1 w_op n a b]] = [!n|word_of_word_tr (zn2z w) n a!] mod [[b]].
 Proof.
  intros n a b Hpos.
  assert (H:= spec_ww_divn1 n a b Hpos).
  rewrite (spec_ww_modn1_eq n a b Hpos).
  destruct (ww_divn1 w_op n a b)as(q,r);destruct H.
  apply Zmod_unique with[!n|q!];simpl;trivial.
  rewrite Zmult_comm;trivial.
 Qed.

 Lemma spec_ww_mod_gt_aux_eq : forall a ah al b bh bl,
      (ah,al) = ww_split w_op a -> 
      ww_mod_gt_aux w_op a ah al b bh bl = snd (ww_div_gt_aux w_op a b bh bl).
 Proof.
  intros a ah al b bh bl Heq. unfold ww_mod_gt_aux, ww_div_gt_aux.
  rewrite <- Heq.
  destruct (znz_head0 w_op bh). trivial.
  destruct ( w_div32 w_op (znz_add_mul_div w_op p (znz_0 w_op) ah)
              (znz_add_mul_div w_op p ah al)
              (znz_add_mul_div w_op p al (znz_0 w_op))
              (znz_add_mul_div w_op p bh bl)
              (znz_add_mul_div w_op p bl (znz_0 w_op)));trivial.
 Qed.

 Lemma spec_ww_mod_gt_aux : forall a ah al b bh bl,
   (ah,al) = ww_split w_op a -> 
   [[a]] > [[b]] ->
   [[b]] = [|bh|]*wB + [|bl|] ->
    0 < [|bh|] ->
    [[ww_mod_gt_aux w_op a ah al b bh bl]] = [[a]] mod [[b]].
 Proof.
  intros. rewrite spec_ww_mod_gt_aux_eq;trivial.
  assert (H3 := spec_ww_div_gt_aux a b bh bl H0 H1 H2).
  destruct (ww_div_gt_aux w_op a b bh bl) as (q,r);simpl.
  apply Zmod_unique with [[q]];try rewrite Zmult_comm;zarith.
 Qed.
 


 Lemma spec_w_mod_gt_eq : forall a b, [|a|] > [|b|] -> 0 <[|b|] ->
   [|znz_mod_gt w_op a b|] = [|snd (znz_div_gt w_op a b)|].
 Proof.
  intros a b Hgt Hpos.
  rewrite (spec_mod_gt op_spec);trivial.
  assert (H:=spec_div_gt op_spec a b Hgt Hpos).
  destruct (znz_div_gt w_op a b) as (q,r);simpl.
  rewrite Zmult_comm in H;destruct H.
  symmetry;apply Zmod_unique with [|q|];trivial.
 Qed.
  
 Lemma spec_ww_mod_gt_eq : forall a b, [[a]] > [[b]] -> 0 < [[b]] ->
      [[ww_mod_gt w_op a b]] = [[snd (ww_div_gt w_op a b)]].
 Proof.
  intros a b Hgt Hpos;unfold ww_mod_gt, ww_div_gt.
  assert (H1 := spec_ww_split b);destruct (ww_split w_op b) as (bh,bl).
  fold (ww_div_gt_aux w_op a b bh bl).
  case_eq (ww_split w_op a);intros ah al Heq.
  fold (ww_mod_gt_aux w_op a ah al b bh bl).
  assert (H2 := spec_compare op_spec (znz_0 w_op) bh);
   destruct (znz_compare w_op (znz_0 w_op) bh).
  2:rewrite spec_ww_mod_gt_aux_eq;trivial;symmetry;trivial.
  2:rewrite spec_ww_mod_gt_aux_eq;trivial;symmetry;trivial.
  assert (H3 := spec_compare op_spec (znz_0 w_op) ah);
   destruct (znz_compare w_op (znz_0 w_op) ah).
  generalize Hgt Hpos;clear Hgt Hpos.
  assert (H4 := spec_ww_split a);rewrite Heq in H4;simpl in H4.
  rewrite H1;rewrite H4;simpl. rewrite <- H2;rewrite <- H3.
  rewrite (spec_0 op_spec);repeat rewrite Zmult_0_l;repeat rewrite Zplus_0_l.
  intros Hgt Hpos; assert (H5 := spec_w_mod_gt_eq al bl Hgt Hpos).
  destruct (znz_div_gt w_op al bl);w_rewrite;rewrite H5;simpl;w_rewrite;ring.
  generalize Hpos;clear Hpos.
  rewrite H1;simpl;rewrite <- H2;rewrite (spec_0 op_spec);
    repeat rewrite Zmult_0_l;repeat rewrite Zplus_0_l.
  intros Hpos; assert (H4 := spec_w_modn1_eq 1 a bl Hpos).
  destruct (znz_divn1 w_op 1 a bl);simpl in *;w_rewrite;rewrite H4;ring.
  rewrite (spec_0 op_spec) in H3;assert (H4 := spec_to_Z op_spec ah);
   elimtype False;omega.
 Qed.

 Lemma spec_ww_mod_gt : forall a b, [[a]] > [[b]] -> 0 < [[b]] ->
      [[ww_mod_gt w_op a b]] = [[a]] mod [[b]].
 Proof.
  intros a b Hgt Hpos.
  assert (H:= spec_ww_div_gt a b Hgt Hpos).
  rewrite (spec_ww_mod_gt_eq a b Hgt Hpos).
  destruct (ww_div_gt w_op a b)as(q,r);destruct H.
  apply Zmod_unique with[[q]];simpl;trivial.
  rewrite Zmult_comm;trivial.
 Qed.

 Lemma  spec_ww_mod :  forall a b, 0 < [[b]] ->
      [[ww_mod w_op a b]] = [[a]] mod [[b]].
 Proof.
  intros a b Hpos;unfold ww_mod. 
  assert (H := spec_ww_compare a b);destruct (ww_compare w_op a b).
  simpl;apply Zmod_unique with 1;try rewrite H;zarith.
  assert (H1 := spec_ww_to_Z a);symmetry;apply Zmod_def_small;zarith.
  apply spec_ww_mod_gt;trivial.
 Qed.

 Lemma Zis_gcd_mod : forall a b d, 
   0 < b -> Zis_gcd b (a mod b) d -> Zis_gcd a b d.
 Proof.
  intros a b d H H1; apply Zis_gcd_for_euclid with (a/b).
  pattern a at 1;rewrite (Z_div_mod_eq a b).
  ring (b * (a / b) + a mod b - a / b * b);trivial. zarith.
 Qed.

 Lemma spec_ww_gcd_gt_aux_body : 
  forall a b n cont,
   [[b]] <= 2^n -> 
   [[a]] > [[b]] ->
   (forall x y, 
     [[x]] > [[y]] -> [[y]] <= 2^(n-1) -> Zis_gcd [[x]] [[y]] [[cont x y]]) ->
   Zis_gcd [[a]] [[b]]
    [[(let (bh, bl) := ww_split w_op b in
       match znz_compare w_op (znz_0 w_op) bh with
       | Eq =>
         match znz_compare w_op (znz_0 w_op) bl with
         | Eq => a
         | _ => WW (znz_0 w_op) (znz_gcd_gt w_op bl (znz_modn1 w_op 1 a bl))
         end
       | _  =>
         let (ah, al) := ww_split w_op a in
         let (mh, ml) := ww_split w_op (ww_mod_gt_aux w_op a ah al b bh bl) in
         match znz_compare w_op (znz_0 w_op) mh with
         | Eq =>
           match znz_compare w_op (znz_0 w_op) ml with
           | Eq => b
           | _  => WW (znz_0 w_op) (znz_gcd_gt w_op ml (znz_modn1 w_op 1 b ml))
           end
         | _  =>
           cont (ww_mod_gt_aux w_op a ah al b bh bl)
             (ww_mod_gt_aux w_op b bh bl
                  (ww_mod_gt_aux w_op a ah al b bh bl) mh ml)
         end
       end)]].
 Proof.
  intros a b n cont Hlog Hgt Hcont.
  generalize (spec_ww_split b);case_eq (ww_split w_op b);intros bh bl Heqb Hb.
  simpl in Hb.
  assert (Hbh := spec_compare op_spec (znz_0 w_op) bh);
   destruct (znz_compare w_op (znz_0 w_op) bh). 
  rewrite Hb;rewrite <- Hbh;rewrite (spec_0 op_spec);
   rewrite Zmult_0_l;rewrite Zplus_0_l.
  assert (Hbl := spec_compare op_spec (znz_0 w_op) bl);
   destruct (znz_compare w_op (znz_0 w_op) bl). 
  rewrite <- Hbl;rewrite (spec_0 op_spec);apply Zis_gcd_0.
  simpl;rewrite (spec_0 op_spec);rewrite Zmult_0_l;rewrite Zplus_0_l.
  rewrite (spec_0 op_spec) in Hbl.
  apply Zis_gcd_mod;zarith.
  change [[a]] with 
    (gen_to_Z (znz_digits w_op) (znz_to_Z w_op) 1 (word_of_word_tr w 1 a)).
  rewrite <- (spec_modn1 op_spec 1 a bl Hbl).
  apply (spec_gcd_gt op_spec).
  apply Zlt_gt;rewrite (spec_modn1 op_spec);trivial.
  match goal with | |- ?x mod ?y < ?y => destruct (Z_mod_lt x y);zarith end.
  rewrite (spec_0 op_spec) in Hbl;assert (H := spec_to_Z op_spec bl);
   elimtype False;omega.
  rewrite (spec_0 op_spec) in Hbh. 
  generalize (spec_ww_split a);case_eq (ww_split w_op a);intros ah al Heqa Ha.
  simpl in Ha;assert (H2 : 0 < [[b]]). 
   rewrite Hb;assert (H2:=spec_to_Z op_spec bl).
   apply Zlt_le_trans with ([|bh|]*wB);zarith.
   apply Zmult_lt_0_compat;zarith.
  apply Zis_gcd_mod;trivial. 
  rewrite <- (@spec_ww_mod_gt_aux a ah al b bh bl);zarith.
  assert (Hm := spec_ww_split (ww_mod_gt_aux w_op a ah al b bh bl));
  destruct (ww_split w_op (ww_mod_gt_aux w_op a ah al b bh bl)) as (mh,ml).
  simpl in Hm;assert (Hmh := spec_compare op_spec (znz_0 w_op) mh);
   destruct (znz_compare w_op (znz_0 w_op) mh). 
  rewrite Hm; rewrite <- Hmh;rewrite (spec_0 op_spec);rewrite Zmult_0_l;
   rewrite Zplus_0_l. 
  assert (Hml := spec_compare op_spec (znz_0 w_op) ml);
   destruct (znz_compare w_op (znz_0 w_op) ml). 
  rewrite <- Hml;rewrite (spec_0 op_spec);apply Zis_gcd_0;zarith. 
  simpl;rewrite (spec_0 op_spec);rewrite Zmult_0_l;rewrite Zplus_0_l. 
  rewrite (spec_0 op_spec) in Hml;apply Zis_gcd_mod;trivial. 
  change [[b]] with 
    (gen_to_Z (znz_digits w_op) (znz_to_Z w_op) 1 (word_of_word_tr w 1 b)).
  rewrite <- (spec_modn1 op_spec 1 b ml Hml).
  apply (spec_gcd_gt op_spec).
  apply Zlt_gt;rewrite (spec_modn1 op_spec);trivial.
  match goal with | |- ?x mod ?y < ?y => destruct (Z_mod_lt x y);zarith end.
  rewrite (spec_0 op_spec) in Hml;assert (H1 := spec_to_Z op_spec ml);
   elimtype False;omega.
  rewrite (spec_0 op_spec) in Hmh.
  assert (0 < [[ww_mod_gt_aux w_op a ah al b bh bl]]).
   rewrite Hm;assert (H3:=spec_to_Z op_spec ml).
   apply Zlt_le_trans with ([|mh|]*wB);zarith.
   apply Zmult_lt_0_compat;zarith.
  apply Zis_gcd_mod;trivial. 
  generalize (ww_mod_gt_aux w_op a ah al b bh bl) Hm H 
   (@spec_ww_mod_gt_aux a ah al b bh bl (sym_eq Heqa) Hgt Hb Hbh);clear Hm H.
  intros m Hm H0 Hmod.
  assert ([[b]] > [[m]]).
   apply Zlt_gt;rewrite Hmod.
   match goal with | |- ?x mod ?y < ?y => destruct (Z_mod_lt x y);zarith end.
  rewrite <- (@spec_ww_mod_gt_aux b bh bl m mh ml);zarith.
  apply Hcont; rewrite spec_ww_mod_gt_aux;zarith.
  apply Zlt_gt.
  match goal with | |- ?x mod ?y < ?y => destruct (Z_mod_lt x y);zarith end.
  apply Zle_trans with (2^n/2). 
  apply Zdiv_le_lower_bound;zarith.
  apply Zle_trans with [[b]];trivial.
  assert (U : [[m]] > 0);zarith.
  assert (H3 := Z_div_mod_eq [[b]] [[m]] U).
  assert (H4 : 0 <= [[b]]/[[m]]).
   apply Zge_le;apply Z_div_ge0;zarith.
  pattern [[b]] at 2;rewrite H3.
  destruct (Zle_lt_or_eq _ _ H4).
  assert (H6 : [[b]] mod [[m]] = [[b]] - [[m]] * ([[b]]/[[m]])).
   pattern [[b]] at 2;rewrite H3;ring.
  assert ([[m]] <= [[m]] * ([[b]]/[[m]])).
   pattern [[m]] at 1;rewrite <- Zmult_1_r;zarith.
  assert (H8 := Z_mod_lt [[b]] [[m]]);zarith.
  rewrite <- H1 in H3;assert (H8 := Z_mod_lt [[b]] [[m]]);zarith.
  pattern n at 1;replace n with (n-1+1);try ring.
  rewrite Zpower_exp;zarith. change (2^1) with 2.
  rewrite Z_div_mult;zarith.
  assert (2^1 <= 2^n). change (2^1) with 2;zarith.
  assert (H3 := @Zpower_le_monotone_inv 2 1 n);zarith.
  rewrite (spec_0 op_spec) in Hmh;assert (H1 := spec_to_Z op_spec mh);
   elimtype False;omega.
  rewrite (spec_0 op_spec) in Hbh;assert (H1 := spec_to_Z op_spec bh);
   elimtype False;omega.
 Qed.

 Lemma spec_ww_gcd_gt_aux : 
   forall p cont n,
   (forall x y, 
     [[x]] > [[y]] -> [[y]] <= 2^n -> Zis_gcd [[x]] [[y]] [[cont x y]]) ->
   forall a b , [[a]] > [[b]] ->
     [[b]] <= 2^(Zpos p + n) ->
     Zis_gcd [[a]] [[b]] [[ww_gcd_gt_aux w_op p cont a b]].
 Proof.
  induction p;intros cont n Hcont a b Hgt Hs;simpl.
  assert (0 < Zpos p). unfold Zlt;reflexivity.
  apply spec_ww_gcd_gt_aux_body with 
    (cont := ww_gcd_gt_aux w_op p (ww_gcd_gt_aux w_op p cont))
    (n := Zpos (xI p) + n);trivial;rewrite Zpos_xI.
  intros. apply IHp with (n := Zpos p + n);zarith.
  intros. apply IHp with (n := n );zarith.
  apply Zle_trans with (2 ^ (2* Zpos p + 1+ n -1));zarith.
  apply Zpower_le_monotone2;zarith.
  assert (0 < Zpos p). unfold Zlt;reflexivity.
  apply spec_ww_gcd_gt_aux_body with 
    (cont := ww_gcd_gt_aux w_op p (ww_gcd_gt_aux w_op p cont))
    (n := Zpos (xO p) + n );trivial.
  rewrite (Zpos_xO p).
  intros. apply IHp with (n := Zpos p + n - 1);zarith.
  intros. apply IHp with (n := n -1 );zarith.
  intros;apply Hcont;zarith.
  apply Zle_trans with (2^(n-1));zarith.
  apply Zpower_le_monotone2;zarith.
  apply Zle_trans with (2 ^ (Zpos p + n -1));zarith.
  apply Zpower_le_monotone2;zarith.
  apply Zle_trans with (2 ^ (2*Zpos p + n -1));zarith.
  apply Zpower_le_monotone2;zarith. 
  apply spec_ww_gcd_gt_aux_body with 
    (cont := cont)
    (n := n+1);trivial.
  apply Zle_trans with (2 ^ (1 + n));zarith.
  apply Zpower_le_monotone2;zarith.
  replace (n + 1 - 1) with n;auto. ring.
 Qed.

 Lemma spec_ww_gcd_gt : forall a b, [[a]] > [[b]] ->
      Zis_gcd [[a]] [[b]] [[ww_gcd_gt w_op a b]].
 Proof.
  intros a b Hgt;unfold ww_gcd_gt.
  assert (Ha := spec_ww_split a);
   destruct (ww_split w_op a) as (ah,al);simpl in Ha.
  assert (Hcmp := spec_compare op_spec (znz_0 w_op) ah);
  destruct (znz_compare w_op (znz_0 w_op) ah);rewrite (spec_0 op_spec) in Hcmp.
  assert (Hb := spec_ww_split b);destruct (ww_split w_op b) as (bh,bl);
    simpl in Hb.
  rewrite Ha in Hgt;rewrite Hb in Hgt.
  assert (H:=wB_lex _ _ (Zlt_le_weak _ _ (Zgt_lt _ _ Hgt))
           (spec_to_Z op_spec bl) (spec_to_Z op_spec al)).
  assert ([|bh|] = 0). assert (H1 := spec_to_Z op_spec bh);zarith.
  generalize Hgt;clear Hgt;rewrite Ha;rewrite Hb;simpl;
  rewrite <- Hcmp;rewrite (spec_0 op_spec);rewrite H0;rewrite Zmult_0_l;
  repeat rewrite Zplus_0_l. intros Hgt.
  apply (spec_gcd_gt op_spec);zarith.
  change (Zis_gcd [[a]] [[b]]
    [[ww_gcd_gt_aux w_op (xO (znz_digits w_op)) 
             (fun x y => 
                match ww_compare w_op (WW (znz_0 w_op) (znz_1 w_op)) y with
                | Eq => WW (znz_0 w_op) (znz_1 w_op)
                | _ => x
                end) a b]]).
  apply spec_ww_gcd_gt_aux with (n:=0);zarith.
  intros x y Hgt' Hle. simpl in Hle.
  assert (Hcmpy := spec_ww_compare (WW (znz_0 w_op) (znz_1 w_op)) y).
  destruct (ww_compare w_op (WW (znz_0 w_op) (znz_1 w_op)) y);
   rewrite spec_ww_1 in Hcmpy.
  rewrite spec_ww_1;rewrite <- Hcmpy;apply Zis_gcd_mod;zarith.
  rewrite <- (Zmod_unique [[x]] 1 [[x]] 0);zarith.
  elimtype False;zarith.
  assert ([[y]] = 0). assert (H:=spec_ww_to_Z y);zarith.
  rewrite H;zarith.
  rewrite Zplus_0_r;fold wwB.
  destruct (spec_ww_to_Z b);zarith.
  destruct (spec_to_Z op_spec ah);elimtype False;zarith.
 Qed.

 Lemma spec_ww_gcd : forall a b, Zis_gcd [[a]] [[b]] [[ww_gcd w_op a b]].
 Proof.
  intros a b;unfold ww_gcd.
  change (Zis_gcd [[a]] [[b]] [[match ww_compare w_op a b with
          | Gt => ww_gcd_gt w_op a b
          | Eq => a
          | Lt => ww_gcd_gt w_op b a
          end]]).
  assert (Hcmp := spec_ww_compare a b);destruct (ww_compare w_op a b).
  assert (H:= spec_ww_to_Z b);rewrite Hcmp.
  apply Zis_gcd_for_euclid with 1;zarith.
  ring ([[b]] - 1 * [[b]]). apply Zis_gcd_0;zarith.
  apply Zis_gcd_sym;apply spec_ww_gcd_gt;zarith.
  apply spec_ww_gcd_gt;zarith.
 Qed.

End Proof.
