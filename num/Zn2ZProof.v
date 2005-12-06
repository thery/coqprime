(*
Unset Boxed Definitions.
*)

Set Implicit Arguments.

Require Import ZArith.
Require Import ZnZ.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Zn2Z.

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
  
 Axiom spec_ww_of_pos : forall p, 
       Zpos p = 
        (Z_of_N (fst (ww_of_pos w_op p)))*wB + [[(snd (ww_of_pos w_op p))]].

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

Theorem beta_lex_inv: forall a b c d beta, a < c -> 0 <= b < beta -> 0 <= d < beta -> beta * a + b < beta * c + d. 
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

Axiom wB_pos: 1 < wB.
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

Axiom ok: forall P, P.

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

Theorem Zmult_mod_distr_l: forall a b c, 0 < a -> 0 < c -> (a * b) mod (a * c) = a * (b mod c).
  intros a b c H Hc.
  apply sym_equal; apply Zmod_unique with (b / c); auto with zarith.
  apply Zmult_lt_0_compat; auto.
  case (Z_mod_lt b c); auto with zarith; intros; split; auto with zarith.
  apply Zmult_lt_compat_l; auto.
  rewrite <- Zmult_assoc; rewrite <- Zmult_plus_distr_r.
  rewrite <- Z_div_mod_eq; auto with zarith.
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

(*
    
    (* Special divisions operations *)
    spec_ww_div21_fst : forall a1 a2 b, 
     (base (znz_digits ww_op)/2 <= [|b|] ->
     [+|fst (w_div21 a1 a2 b)|] = ([|a1|]*(base (znz_digits ww_op)+[|a2|])/ [|b|];
    spec_ww_div21_snd : forall a1 a2 b, 
     (base (znz_digits ww_op)/2 <= [|b|] ->
     [|snd (w_div21 a1 a2 b)|] = ([|a1|]*(base (znz_digits ww_op)+[|a2|]) mod [|b|];
    spec_ww_add_mul_div : forall x y p,
       0 < Zpos p < Zpos w_digits ->
       [| w_add_mul_div x y p|] =
	 ([|x|] * (Zpower 2 (Zpos p)) + 
          [|y|] / (Zpower 2 ((Zpos w_digits) - (Zpos p)))) mod (base (znz_digits ww_op)
  }.


*)


End Proof.
