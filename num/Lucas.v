Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import ZnZ.
Require Import W.
Require Import Mod_op.
Require Import LucasLehmer.

Open Scope Z_scope. 

Section test.

Variable w: Set.
Variable w_op: znz_op w.
Variable op_spec: znz_spec w_op.
Variable p: positive.
Variable b: w.

Notation "[| x |]" :=
   (znz_to_Z w_op x)  (at level 0, x at level 99).


Hypothesis p_more_1: 2 < Zpos p.
Hypothesis b_p: [|b|] = 2 ^ Zpos p - 1.

Lemma b_pos: 0 < [|b|].
rewrite b_p; auto with zarith.
assert (2 ^ 0 < 2 ^ Zpos p); auto with zarith.
apply ZAux.Zpower_lt_monotone; auto with zarith.
rewrite ZAux.Zpower_exp_0 in H; auto with zarith.
Qed.

Hint Resolve b_pos.

Variable m_op: mod_op w.
Variable m_op_spec: mod_spec w_op b m_op.

Let w2 := m_op.(add_mod) w_op.(znz_1) w_op.(znz_1).

Lemma w1_b: [|w_op.(znz_1)|] = 1 mod [|b|].
rewrite (spec_1 op_spec); simpl; auto.
rewrite Zmod_def_small; auto with zarith.
split; auto with zarith.
rewrite b_p.
assert (2 ^ 1 < 2 ^ Zpos p); auto with zarith.
apply ZAux.Zpower_lt_monotone; auto with zarith.
rewrite ZAux.Zpower_exp_1 in H; auto with zarith.
Qed.

Lemma w2_b: [|w2|] = 2 mod [|b|].
unfold w2; rewrite (add_mod_spec m_op_spec _ _ _ _ w1_b w1_b).
rewrite w1_b; rewrite <- Zmod_plus; auto with zarith.
Qed.

Let w4 := m_op.(add_mod) w2 w2.

Lemma w4_b: [|w4|] = 4 mod [|b|].
unfold w4; rewrite (add_mod_spec m_op_spec _ _ _ _ w2_b w2_b).
rewrite w2_b; rewrite <- Zmod_plus; auto with zarith.
Qed.

Let square_m2 :=
   let square := m_op.(square_mod) in
   let sub := m_op.(sub_mod) in
   fun x => sub (square x) w2.

Definition lucastest :=
 w_op.(znz_to_Z) (iter_pos (Pminus p 2) _ square_m2 w4).

Theorem lucastest_aux_correct:
 forall p1 z n, 0 <= n -> [|z|] = fst (s n) mod (2 ^ Zpos p - 1) ->
       [|iter_pos p1 _ square_m2 z|] = fst (s (n + Zpos p1)) mod (2 ^ Zpos p - 1).
intros p1; pattern p1; apply Pind; simpl iter_pos; simpl s; clear p1.
intros z p1 Hp1 H.
unfold square_m2.
rewrite <- b_p in H.
generalize (square_mod_spec m_op_spec _ _ H); intros H1.
rewrite (sub_mod_spec m_op_spec _ _ _ _ H1 w2_b).
rewrite H1; rewrite w2_b; auto with zarith.
rewrite H; rewrite <- Zmod_mult; auto with zarith.
rewrite <- Zmod_minus; auto with zarith.
rewrite sn; simpl; auto with zarith.
rewrite b_p; auto.
intros p1 Rec w1 z Hz Hw1.
rewrite Pplus_one_succ_l; rewrite iter_pos_plus;
 simpl iter_pos.
match goal with |- context[square_m2 ?X] =>
  set (tmp := X); unfold square_m2; unfold tmp; clear tmp
end.
generalize (Rec _ _ Hz Hw1); intros H1.
rewrite <- b_p in H1.
generalize (square_mod_spec m_op_spec _ _ H1); intros H2.
rewrite (sub_mod_spec m_op_spec _ _ _ _ H2 w2_b).
rewrite H2; rewrite w2_b; auto with zarith.
rewrite H1; rewrite <- Zmod_mult; auto with zarith.
rewrite <- Zmod_minus; auto with zarith.
replace (z + Zpos (1 + p1)) with ((z + Zpos p1) + 1); auto with zarith.
rewrite sn; simpl fst; try rewrite b_p; auto with zarith.
rewrite Zpos_plus_distr; auto with zarith.
Qed.

Theorem lucastest_prop: lucastest = fst(s (Zpos p -2)) mod (2 ^ Zpos p - 1).
unfold lucastest.
assert (F: 0 <= 0); auto with zarith.
generalize (lucastest_aux_correct (p -2) w4 F); simpl Zplus;
   rewrite Zpos_minus; auto with zarith.
intros tmp; apply tmp; clear tmp.
rewrite <- b_p; simpl; exact w4_b.
Qed.

Theorem lucastest_prop_cor: lucastest = 0 -> (2 ^ Zpos p - 1 | fst(s (Zpos p - 2))).
intros H.
apply Zmod_divide.
assert (H1: 2 ^ 1 < 2 ^ Zpos p); auto with zarith.
apply ZAux.Zpower_lt_monotone; auto with zarith.
rewrite ZAux.Zpower_exp_1 in H1; auto with zarith.
apply trans_equal with (2:= H); apply sym_equal; apply lucastest_prop; auto.
Qed.

Theorem lucastest_prime:  lucastest = 0 -> prime (2 ^ Zpos p - 1).
intros H1; case (prime_dec (2 ^ Zpos p - 1)); auto; intros H2.
case Zdivide_div_prime_le_square with (2 := H2).
assert (H3: 2 ^ 1 < 2 ^ Zpos p); auto with zarith.
apply ZAux.Zpower_lt_monotone; auto with zarith.
rewrite ZAux.Zpower_exp_1 in H3; auto with zarith.
intros q (H3, (H4, H5)).
contradict H5; apply Zlt_not_le.
generalize q_more_than_square; unfold Mp; intros tmp; apply tmp;
  auto; clear tmp.
apply lucastest_prop_cor; auto.
case (Zle_lt_or_eq 2 q); auto.
apply prime_le_2; auto.
intros H5; subst.
absurd (2 <= 1); auto with arith.
apply Zdivide_le; auto with zarith.
case H4; intros x Hx.
exists (2 ^ (Zpos p -1) - x).
rewrite Zmult_minus_distr_r; rewrite <- Hx; unfold Mp.
pattern 2 at 2; rewrite <- Zpower_exp_1; rewrite <- Zpower_exp; auto with zarith.
replace (Zpos p - 1 + 1) with (Zpos p); auto with zarith.
Qed.

End test.

Definition znz_of_Z (w:Set) (op:znz_op w) z :=
 match z with
 | Zpos p => snd (op.(znz_of_pos) p)
 | _ => op.(znz_0)
 end.

Fixpoint plength (p: positive) : positive :=
  match p with 
    xH => xH
  | xO p1 => Psucc (plength p1)
  | xI p1 => Psucc (plength p1)
  end.

Definition lucas p :=
 let op := cmk_op (nat_of_P (plength p) - 3) in
 let b := znz_of_Z op (Zpower 2 (Zpos p) - 1) in
 let mod_op := mmake_mod_op op b p (2 * op.(znz_digits) - p) in
  lucastest op p mod_op.

Time Eval compute in lucas 127.

Theorem plength_correct: forall p, (Zpos p < 2 ^ Zpos (plength p))%Z.
assert (F: (forall p, 2 ^ (Zpos (Psucc p)) = 2 * 2 ^ Zpos p)%Z).
intros p; replace (Zpos (Psucc p)) with (1 + Zpos p)%Z.
rewrite Zpower_exp; auto with zarith.
rewrite Zpos_succ_morphism; unfold Zsucc; auto with zarith.
intros p; elim p; simpl plength; auto.
intros p1 Hp1; rewrite F; repeat rewrite Zpos_xI.
assert (tmp: (forall p, 2 * p = p + p)%Z); 
  try repeat rewrite tmp; auto with zarith.
intros p1 Hp1; rewrite F; rewrite (Zpos_xO p1).
assert (tmp: (forall p, 2 * p = p + p)%Z); 
  try repeat rewrite tmp; auto with zarith.
rewrite ZPowerAux.Zpower_exp_1; auto with zarith.
Qed.

Theorem plength_pred_correct: forall p, (Zpos p <= 2 ^ Zpos (plength (Ppred p)))%Z.
intros p; case (Psucc_pred p); intros H1.
subst; simpl plength.
rewrite ZPowerAux.Zpower_exp_1; auto with zarith.
pattern p at 1; rewrite <- H1.
rewrite Zpos_succ_morphism; unfold Zsucc; auto with zarith.
generalize (plength_correct (Ppred p)); auto with zarith.
Qed.

Definition pheight p := plength (Ppred (plength (Ppred p))).


Theorem pheight_correct: forall p, (Zpos p <= 2 ^ (2 ^ (Zpos (pheight p))))%Z.
intros p; apply Zle_trans with (1 := (plength_pred_correct p)).
apply ZPowerAux.Zpower_le_monotone; auto with zarith.
split; auto with zarith.
unfold pheight; apply plength_pred_correct.
Qed.

Section znz_of_pos.
 
 Variable w : Set.
 Variable w_op : znz_op w.
 Variable op_spec : znz_spec w_op.

 Notation "[| x |]" := (znz_to_Z w_op x)  (at level 0, x at level 99).
 
 Theorem znz_of_pos_correct:
   forall p, Zpos p < base (znz_digits w_op) -> [|(snd (znz_of_pos w_op p))|] = Zpos p.
 intros p Hp.
 generalize (spec_of_pos op_spec p).
 case (znz_of_pos w_op p); intros n w1; simpl.
 case n; simpl Npos; auto with zarith.
 intros p1 Hp1; contradict Hp; apply Zle_not_lt.
 rewrite Hp1; auto with zarith.
 match goal with |- _ <= ?X + ?Y =>
  apply Zle_trans with X; auto with zarith
 end.
 match goal with |- ?X <= _ =>
  pattern X at 1; rewrite <- (Zmult_1_l); 
  apply Zmult_le_compat_r; auto with zarith
 end.
 case p1; simpl; intros; red; simpl; intros; discriminate.
 unfold base; auto with zarith.
 case (spec_to_Z op_spec w1); auto with zarith.
 Qed.

 Theorem znz_of_Z_correct:
   forall p, 0 <= p < base (znz_digits w_op) -> [|znz_of_Z w_op p|] = p.
 intros p; case p; simpl; try rewrite spec_0; auto.
 intros; rewrite znz_of_pos_correct; auto with zarith.
 intros p1 (H1, _); contradict H1; apply Zlt_not_le; red; simpl; auto.
 Qed.
End znz_of_pos.

Theorem lucas_prime:
 forall p, 2 < Zpos p -> lucas p = 0 -> prime (2 ^ Zpos p - 1).
unfold lucas; intros p Hp H.
match type of H with lucastest (cmk_op ?x) ?y ?z = _ =>
   set (w_op := (cmk_op x)); assert(A1: znz_spec w_op)
end.
unfold w_op; apply cmk_spec.
assert (F0: p <= znz_digits w_op).
unfold w_op, base; rewrite (cmk_op_digits (nat_of_P (plength p) - 3)).
apply Zle_trans with (2 ^ plength p).
apply Zlt_le_weak; apply plength_correct.
apply Zpower_le_monotone; auto with zarith.
split; auto with zarith.
case (le_or_lt 3 (nat_of_P (plength p))); intros A2.
rewrite inj_minus1; simpl; auto with zarith.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
rewrite inj_minus2; simpl; auto with zarith.
generalize (inj_le (nat_of_P (plength p)) 3); simpl; auto with zarith.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
assert (F1: znz_to_Z w_op (znz_of_Z w_op (2 ^ p - 1)) = 2 ^ p - 1).
assert (F1: 0 < 2 ^ p - 1).
assert (F2: 2 ^ 0 < 2 ^ p); auto with zarith.
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_exp_0 in F2; auto with zarith.
case_eq (2 ^ p - 1); simpl znz_to_Z.
intros HH; contradict F1; rewrite HH; auto with zarith.
2: intros p1 HH; contradict F1; rewrite HH; 
  apply Zle_not_lt; red; simpl; intros; discriminate.
intros p1 Hp1; apply znz_of_pos_correct; auto.
rewrite <- Hp1.
unfold base.
apply Zlt_le_trans with (2 ^ p); auto with zarith.
apply Zpower_le_monotone; auto with zarith.
match type of H with lucastest (cmk_op ?x) ?y ?z = _ =>
   apply (fun U V =>
    @lucastest_prime _ _ (cmk_spec x) p (znz_of_Z (cmk_op x) 
                 (2 ^ Zpos p  -1)) U V z)
end; auto with zarith; fold w_op.
apply mmake_mod_spec; auto with zarith.
rewrite F1.
assert (F2: 2 ^ 1 < 2 ^p); auto with zarith.
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_exp_1 in F2; auto with zarith.
rewrite Zpos_minus; auto with zarith.
rewrite Zmisc.Zpos_mult; auto with zarith.
rewrite (Zpos_xO (znz_digits w_op)); auto with zarith.
rewrite Zmisc.Zpos_mult; auto with zarith.
Qed.

