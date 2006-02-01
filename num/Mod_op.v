Set Implicit Arguments.

Require Import ZArith.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import ZnZ.
Require Import Zn2Z.
Require Import Zn2Z_for_Proof.
Require Import Zn2ZProof.

Section Mod_op.

 Variable w : Set.
 
 Record mod_op : Set := mk_mod_op {    
   w0_mod     : w;
   w1_mod     : w;
   succ_mod   : w -> w;
   add_mod    : w -> w -> w;
   pred_mod   : w -> w;
   sub_mod    : w -> w -> w;
   mul_mod    : w -> w -> w;
   square_mod : w -> w;
   power_mod  : w -> positive -> w
(*
   shift      : w -> positive -> w;
   trunc      : w -> positive -> w
*)
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
   | Npos p => w_add_mul_div p b w0
   end.

 Let bm1 := w_sub b w1.

 Let mb := without_c (w_opp_c b).

 Let wwb := WW w0 b.

 Let ww_lsl_n :=
   match n with 
   | N0 => fun ww => ww
   | Npos p => 
     let add_mul_div := ww_add_mul_div w_op in 
     fun ww => add_mul_div p ww W0
   end.

 Let w_lsr_n :=
   match n with
   | N0 => fun w => w
   | Npos p =>
     let k := Pminus w_digits p in
     fun w => w_add_mul_div k w0 w
   end.

 Open Scope Z_scope. 
 Notation "[| x |]" :=
   (znz_to_Z w_op x)  (at level 0, x at level 99).

Notation "[[ x ]]" :=
   (ww_to_Z w_op x)  (at level 0, x at level 99).

 Section Mod_spec.
 
   Variable m_op : mod_op.

   Variable wf: w -> Prop.

   Record mod_spec : Set := mk_mod_spec {
    (* Basic constructors *)
      mod_wf_0          : wf w0;
      mod_wf_spec_1     : wf w1;
      succ_mod_wf_spec  : 
                forall w, wf w -> wf (succ_mod m_op w);
      add_mod_wf_spec   : 
            forall w1 w2, wf w1 -> wf w2 -> wf (add_mod m_op w1 w2);
      pred_mod_wf_spec  : 
                forall w, wf w -> wf (pred_mod m_op w);
      sub_mod_wf_spec   : 
            forall w1 w2, wf w1 -> wf w2 -> wf (sub_mod m_op w1 w2);
      mul_mod_wf_spec   : 
            forall w1 w2, wf w1 -> wf w2 -> wf (mul_mod m_op w1 w2);
      square_mod_wf_spec: 
                forall w, wf w -> wf (square_mod m_op w);
      power_mod_wf_spec : 
              forall w p, wf w -> wf (power_mod m_op w p);
(*
      shift_wf_spec     :
              forall w p, wf w -> wf (shift m_op w p);
      trunc_wf_spec     :
              forall w p, wf w -> wf (trunc m_op w p);
*)
      mod_spec_0        : [|w0|] mod [|b|] = 0;
      mod_spec_1        : [|w1|] mod [|b|] = 1;
      succ_mod_spec     : 
                forall w, wf w ->
                          [|succ_mod m_op w|] = ([|w|] + 1) mod [|b|];
      add_mod_spec      :
            forall w1 w2, wf w1 -> wf w2 ->
                          [|add_mod m_op w1 w2|] = ([|w1|] + [|w2|]) mod [|b|];
      pred_mod_spec     :
                forall w, wf w ->
                          [|pred_mod m_op w|] = ([|w|] - 1) mod [|b|];
      sub_mod_spec      :
            forall w1 w2, wf w1 -> wf w2 ->
                          [|sub_mod m_op w1 w2|] = ([|w1|] - [|w2|]) mod [|b|];
      mul_mod_spec      :
            forall w1 w2, wf w1 -> wf w2 ->
                          [|mul_mod m_op w1 w2|] = ([|w1|] * [|w2|]) mod [|b|];
      square_mod_spec   :
                forall w, wf w ->
                          [|square_mod m_op w|] = ([|w|] * [|w|]) mod [|b|];
      power_mod_spec    :
              forall w p, wf w ->
                          [|power_mod m_op w p|] = (Zpower_pos [|w|] p) mod [|b|]
(*
      shift_spec        :
              forall w p, wf w -> 
                          [|shift m_op w p|] = ([|w|] / (Zpower_pos 2 p)) mod [|b|];
      trunc_spec        :
              forall w p, wf w ->
                          [|power_mod m_op w p|] = ([|w1|] mod (Zpower_pos 2 p)) mod [|b|]
*)
    }.

  End Mod_spec.

 Hypothesis b_pos: 1 < [|b|].

 Lemma Zpower_n: 0 < 2 ^ Z_of_N n.
 apply ZPowerAux.Zpower_lt_0; auto with zarith.
 case n; intros; simpl Z_of_N; auto with zarith.
 Qed.

 Hint Resolve Zpower_n ZAux.Zmult_lt_0_compat ZPowerAux.Zpower_lt_0.
 
 Let _wf := fun w => [|w|] < [|b|].

 Variable op_spec: znz_spec w_op.

 Variable m_op : mod_op.

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

 Let _w0_mod := w0.

 Lemma _mod_wf_0: _wf _w0_mod.
 unfold _w0_mod, _wf, w0.
 autorewrite with w_rewrite; auto with zarith. 
 Qed.

 Lemma _mod_spec_0: [|_w0_mod|] mod [|b|] = 0.
 rewrite Zmod_def_small;
 unfold _w0_mod, w0; autorewrite with w_rewrite; auto with zarith. 
 Qed.
 
 Let _w1_mod := w1.

 Lemma _mod_wf_1: _wf _w1_mod.
 unfold _w1_mod, _wf, w1.
 autorewrite with w_rewrite; auto with zarith. 
 Qed.

 Lemma _mod_spec_1: [|_w1_mod|] mod [|b|] = 1.
 rewrite Zmod_def_small;
 unfold _w1_mod, w1; autorewrite with w_rewrite; auto with zarith. 
 Qed.

 Let _succ_mod x :=
  let res := without_c (w_succ_c x) in
  match w_compare res b with 
  | Lt => res
  | _ => w0
  end.

 Let _w0_is_0: [|w0|] = 0.
 unfold znz_to_Z; rewrite <- (spec_0 op_spec); auto.
 Qed.

 Lemma _w0_wf : _wf w0.
 unfold _wf; rewrite _w0_is_0; auto with zarith.
 Qed.

 Let _w1_is_1: [|w1|] = 1.
 unfold znz_to_Z; rewrite <- (spec_1 op_spec); auto.
 Qed.

 Lemma _w1_wf : _wf w1.
 unfold _wf; rewrite _w1_is_1; auto with zarith.
 Qed.

 Theorem Zmod_plus_one: forall a1 b1, 0 < b1 -> (a1 + b1) mod b1 = a1 mod b1.
 intros a1 b1 H; rewrite Zmod_plus; auto with zarith.
 rewrite Z_mod_same; try rewrite Zplus_0_r; auto with zarith.
 apply Zmod_mod; auto.
 Qed.

 Theorem Zmod_minus_one: forall a1 b1, 0 < b1 -> (a1 - b1) mod b1 = a1 mod b1.
 intros a1 b1 H; rewrite Zmod_minus; auto with zarith.
 rewrite Z_mod_same; try rewrite Zminus_0_r; auto with zarith.
 apply Zmod_mod; auto.
 Qed.

 Lemma _succ_mod_spec: forall w, _wf w ->
    [|_succ_mod w|] = ([|w|] + 1) mod [|b|].
 intros w2; unfold _wf, _succ_mod, w_compare; simpl.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; auto with zarith.
 unfold without_c, w_succ_c.
 generalize (spec_succ_c op_spec w2);  unfold interp_carry; 
   case (znz_succ_c w_op w2).
 intros w3 H H1 H2; rewrite <- H; rewrite H1.
 apply sym_equal; apply Z_mod_same; auto with zarith.
 rewrite Zmult_1_l; unfold base.
 intros w3 H H1 H2.
 absurd ([|b|] + 1 <= [|w2|] +1); auto with zarith.
 rewrite <- H; rewrite <- H1; auto with zarith. 
 rewrite (Zplus_comm [|w3|]); apply Zplus_le_compat_r.
 replace 1 with (2 ^ 0); auto with zarith.
 apply ZPowerAux.Zpower_le_monotone; auto with zarith.
 unfold without_c, w_succ_c.
 generalize (spec_succ_c op_spec w2);  unfold interp_carry; 
   case (znz_succ_c w_op w2).
 intros w3 H H1 H2; rewrite <- H.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 split; auto.
 case (spec_to_Z op_spec w3); auto.
 rewrite Zmult_1_l; unfold base.
 intros w3 H H1 H2.
 absurd ([|b|] + 1 <= [|w2|] +1); auto with zarith.
 rewrite <- H; auto with zarith. 
 apply Zle_trans with (2 ^ Zpos (znz_digits w_op)); auto with zarith.
 case (spec_to_Z op_spec b); unfold base; auto with zarith.
 case (spec_to_Z op_spec w3); unfold base; auto with zarith.
 unfold without_c, w_succ_c.
 generalize (spec_succ_c op_spec w2);  unfold interp_carry; 
   case (znz_succ_c w_op w2).
 intros w3 H H1 H2.
 absurd ([|b|] + 1 <= [|w2|] +1); auto with zarith.
 rewrite Zmult_1_l; unfold base.
 intros w3 H H1 H2.
 absurd ([|b|] + 1 <= [|w2|] +1); auto with zarith.
 rewrite <- H; auto with zarith. 
 apply Zle_trans with (2 ^ Zpos (znz_digits w_op)); auto with zarith.
 case (spec_to_Z op_spec b); unfold base; auto with zarith.
 Qed.


 Lemma _succ_mod_wf_spec: forall w, _wf w -> _wf (_succ_mod w).
 intros w2 Hw2; unfold _wf; rewrite _succ_mod_spec; auto.
 case (Z_mod_lt ([|w2|] + 1) [|b|]); auto with zarith.
 Qed.

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

 Lemma _add_mod_spec: forall w1 w2, _wf w1 -> _wf w2 ->
     [|_add_mod w1 w2|] = ([|w1|] + [|w2|]) mod [|b|].
 intros w2 w3; unfold _wf, _add_mod, w_compare, w_add_c; intros H H1.
 match goal with |- context[znz_add_c _ ?x ?y] =>
   generalize (spec_add_c op_spec x y); unfold interp_carry;
   case (znz_add_c w_op x y); autorewrite with w_rewrite
 end; auto with zarith.
 intros w4 H2.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y); unfold interp_carry;
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; auto with zarith.
 intros H3; rewrite <- H2; rewrite H3.
 rewrite Z_mod_same; auto with zarith.
 intros H3; rewrite <- H2.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 case (spec_to_Z op_spec w4); unfold base; auto with zarith.
 intros H3.
 rewrite <- H2.
 assert (F1: 0 < [|w4|] - [|b|]); auto with zarith.
 assert (F2: [|w4|] < [|b|] + [|b|]); auto with zarith.
 rewrite (fun x y => Zmod_def_small (x - y)); auto with zarith.
 rewrite <- (Zmod_minus_one [|w4|]); auto with zarith.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 split; auto with zarith.
 apply Zlt_trans with [|b|]; auto with zarith.
 case (spec_to_Z op_spec b); unfold base; auto with zarith.
 rewrite Zmult_1_l; intros w4 H2; rewrite <- H2.
 unfold mb, w_add; rewrite spec_add; auto with zarith.
 unfold without_c, w_opp_c.
 assert (F1: [|w4|] < [|b|]).
 assert (F2: base (znz_digits w_op) + [|w4|] < base (znz_digits w_op) + [|b|]);
   auto with zarith.
 case (spec_to_Z op_spec w2); auto with zarith.
 assert (F2: [|b|] < base (znz_digits w_op) + [|w4|]); auto with zarith.
 apply Zlt_le_trans with (base (znz_digits w_op)); auto with zarith.
 case (spec_to_Z op_spec b); auto with zarith.
 case (spec_to_Z op_spec w4); auto with zarith.
 assert (F3: base (znz_digits w_op) + [|w4|] < [|b|] + [|b|]); auto with zarith.
 rewrite <- (fun x => Zmod_minus_one (base x + [|w4|])); auto with zarith.
 rewrite (fun x y => Zmod_def_small (x - y)); auto with zarith.
 match goal with |- context[znz_opp_c _ ?x] =>
   generalize (spec_opp_c op_spec x); unfold interp_carry;
   case (znz_opp_c w_op x); autorewrite with w_rewrite
 end; auto with zarith.
 intros w5 H3; rewrite H3.
 rewrite <- (fun x => Zmod_plus_one (-x + [|w4|])); auto with zarith.
 rewrite Zmod_def_small; auto with zarith.
 intros w5 H3.
 replace [|w5|] with (base (znz_digits w_op) - [|b|]); auto with zarith.
 rewrite Zmod_def_small; auto with zarith.
 Qed.

 Lemma _add_mod_wf_spec: forall w1 w2, _wf w1 -> _wf w2 -> _wf (_add_mod w1 w2).
 intros w2 w3 H H1.
 unfold _wf; rewrite _add_mod_spec; auto.
 case (Z_mod_lt ([|w2|] + [|w3|]) [|b|]); auto with zarith.
 Qed.

 Let _pred_mod x :=
  match w_compare w0 x with
  | Eq => bm1
  | _ => without_c (w_pred_c x)
  end.

 Lemma _pred_mod_spec: forall w, _wf w ->
   [|_pred_mod w|] = ([|w|] - 1) mod [|b|].
 intros w2; unfold _wf, _pred_mod, w_compare, bm1; simpl.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 intros H H1; rewrite <- H; simpl.
 rewrite <- (Zmod_plus_one (-1)); auto with zarith.
 repeat rewrite Zmod_def_small; auto with zarith.
 case (spec_to_Z op_spec b); auto with zarith.
 intros H1 H2. 
 unfold without_c, w_pred_c.
 generalize (spec_pred_c op_spec w2);  unfold interp_carry; 
   case (znz_pred_c w_op w2).
 intros w3 H3; rewrite H3.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 intros w3 H3.
 absurd (0 <= [|w2|] -1); auto with zarith.
 rewrite <- H3; auto with zarith. 
 case (spec_to_Z op_spec w3); auto with zarith.
 case (spec_to_Z op_spec w2); auto with zarith.
 Qed.

 Lemma _pred_mod_wf_spec: forall w, _wf w -> _wf (_pred_mod w).
 intros w2 Hw2; unfold _wf; rewrite _pred_mod_spec; auto.
 case (Z_mod_lt ([|w2|] - 1) [|b|]); auto with zarith.
 Qed.

 Let _sub_mod x y :=
  match w_sub_c x y with
  | C0 z => z
  | C1 z => w_add z b
  end.

 Lemma _sub_mod_spec: forall w1 w2, _wf w1 -> _wf w2 ->
   [|_sub_mod w1 w2|] = ([|w1|] - [|w2|]) mod [|b|].
 intros w2 w3; unfold _wf, _sub_mod, w_compare, w_sub_c; intros H H1.
 match goal with |- context[znz_sub_c _ ?x ?y] =>
   generalize (spec_sub_c op_spec x y); unfold interp_carry;
   case (znz_sub_c w_op x y); autorewrite with w_rewrite
 end; auto with zarith.
 intros w4 H2.
 rewrite Zmod_def_small; auto with zarith.
 split; auto with zarith.
 rewrite <- H2; case (spec_to_Z op_spec w4); auto with zarith.
 apply Zle_lt_trans with [|w2|]; auto with zarith.
 case (spec_to_Z op_spec w3); auto with zarith.
 intros w4 H2; rewrite <- H2.
 unfold w_add; rewrite spec_add; auto with zarith.
 case (spec_to_Z op_spec w4); intros F1 F2.
 assert (F3: 0 <= - 1 *  base (znz_digits w_op) + [|w4|] + [|b|]); auto with zarith.
 rewrite H2.
 case (spec_to_Z op_spec w3); case (spec_to_Z op_spec w2); auto with zarith.
 rewrite <- (fun x => Zmod_minus_one ([|w4|] + x)); auto with zarith.
 rewrite <- (fun x y => Zmod_plus_one (-y + x)); auto with zarith.
 repeat rewrite Zmod_def_small; auto with zarith.
 case (spec_to_Z op_spec b); auto with zarith.
 Qed.

 Lemma _sub_mod_wf_spec: forall w1 w2, _wf w1 -> _wf w2 ->
   _wf (_sub_mod w1 w2).
 intros w2 w3 H H1.
 unfold _wf; rewrite _sub_mod_spec; auto.
 case (Z_mod_lt ([|w2|] - [|w3|]) [|b|]); auto with zarith.
 Qed.

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

 Theorem n_spec: base (znz_digits w_op) / 2 <= 2 ^ (Z_of_N n) * [|b|] 
                        < base (znz_digits w_op).
 unfold n, w_head0; apply (spec_head0 op_spec); auto with zarith.
 Qed. 

 Theorem b2n_spec: [|b2n|] = 2 ^ (Z_of_N n) * [|b|].
 unfold b2n, w_add_mul_div; generalize n_spec; case n; auto.
 simpl Z_of_N; rewrite ZPowerAux.Zpower_exp_0; auto with zarith.
 intros p (Hp, Hp1).
 assert (F1: Zpos p < Zpos (znz_digits w_op)).
 case (Zle_or_lt (Zpos (znz_digits w_op)) (Zpos p)); auto with zarith.
 intros H1; contradict Hp1; apply Zle_not_lt; unfold base.
 apply Zle_trans with (2 ^ Zpos p * 1); auto with zarith.
 rewrite Zmult_1_r; apply ZPowerAux.Zpower_le_monotone; auto with zarith.
 rewrite (spec_add_mul_div op_spec); auto with zarith.
 rewrite _w0_is_0; rewrite Zdiv_0; auto with zarith.
 rewrite Zplus_0_r; rewrite Zmult_comm; apply Zmod_def_small; auto with zarith.
 split; auto with zarith; red; auto.
 Qed.

 Theorem ww_lsl_n_spec: forall w, [[w]] < [|b|] * [|b|] ->
   [[ww_lsl_n w]] = 2 ^ (Z_of_N n) * [[w]].
 intros w2 H; unfold ww_lsl_n; generalize n_spec; case n; simpl Z_of_N.
 intros _; rewrite ZPowerAux.Zpower_exp_0; auto with zarith.
 intros p (Hp, Hp1).
 assert (F: forall x, 0 < Zpos x); auto with zarith.
 intros x; red; simpl; auto.
 assert (F0: forall x, 2 * x = x + x); auto with zarith.
 assert (F1: Zpos p < Zpos (znz_digits w_op)).
 case (Zle_or_lt (Zpos (znz_digits w_op)) (Zpos p)); auto.
 intros H1; contradict Hp1; apply Zle_not_lt; unfold base.
 apply Zle_trans with (2 ^ Zpos p * 1); auto with zarith.
 rewrite Zmult_1_r; apply ZPowerAux.Zpower_le_monotone; auto with zarith.
 assert (F2: Zpos p < Zpos (xO (znz_digits w_op))).
 rewrite (Zpos_xO (znz_digits w_op)); rewrite F0; auto with zarith.
 pattern (Zpos p); rewrite <- Zplus_0_r; auto with zarith.
 apply Zplus_lt_compat; auto with zarith.
 rewrite (spec_ww_add_mul_div op_spec); auto with zarith.
 rewrite spec_ww_0; rewrite Zdiv_0; auto with zarith.
 rewrite Zplus_0_r; rewrite Zmod_def_small; auto with zarith.
 split; auto with zarith.
 case (spec_ww_to_Z op_spec w2); auto with zarith.
 apply Zlt_trans with ([|b|] * [|b|] * 2 ^ Zpos p); auto with zarith.
 apply Zmult_lt_compat_r; auto with zarith.
 rewrite <- Zmult_assoc.
 unfold base; unfold base in Hp.
 rewrite (Zpos_xO (znz_digits w_op)); rewrite F0; auto with zarith.
 rewrite Zpower_exp; auto with zarith.
 apply ZAux.Zmult_lt_compat; auto with zarith.
 case (spec_to_Z op_spec b); auto with zarith.
 split; auto with zarith.
 rewrite Zmult_comm; auto with zarith.
 Qed.

 Theorem w_lsr_n_spec: forall w, [|w|] < 2 ^ (Z_of_N n) *  [|b|]->
   [|w_lsr_n w|] = [|w|] / 2 ^ (Z_of_N n).
 intros w2 H.
 assert (F: forall x, 0 < Zpos x); auto with zarith.
 intros x; red; simpl; auto.
 case (spec_to_Z op_spec w2); intros U1 U2.
 unfold w_lsr_n; generalize n_spec; case n; simpl Z_of_N.
 intros _; rewrite ZPowerAux.Zpower_exp_0; auto with zarith.
 pattern [|w2|] at 2; rewrite <- Zmult_1_r; rewrite Z_div_mult; auto with zarith.
 intros p (Hp, Hp1).
 assert (F0: forall x, 2 * x = x + x); auto with zarith.
 assert (F1: Zpos p < Zpos (znz_digits w_op)).
 case (Zle_or_lt (Zpos (znz_digits w_op)) (Zpos p)); auto.
 intros H1; contradict Hp1; apply Zle_not_lt; unfold base.
 apply Zle_trans with (2 ^ Zpos p * 1); auto with zarith.
 rewrite Zmult_1_r; apply ZPowerAux.Zpower_le_monotone; auto with zarith.
 rewrite (spec_add_mul_div op_spec); auto with zarith.
 rewrite _w0_is_0; rewrite Zmult_0_l; auto with zarith.
 rewrite Zplus_0_l; rewrite Zpos_minus; auto with zarith.
 replace (Zpos (znz_digits w_op) - (Zpos w_digits - Zpos p)) with
   (Zpos p); auto with zarith.
 2: unfold w_digits; auto with zarith.
 apply Zmod_def_small; auto with zarith.
 split; auto with zarith.
 case Zle_lt_or_eq with (1 := U1); intros U3; subst.
 apply Zlt_trans with [|w2|]; auto with zarith.
 apply Z_div_lt; auto with zarith.
 apply Zle_ge; pattern 2 at 1; rewrite <- ZPowerAux.Zpower_exp_1; auto with zarith.
 apply ZPowerAux.Zpower_le_monotone; auto with zarith.
 split; auto with zarith.
 case p; intros; red; simpl; auto; intros; discriminate.
 rewrite <- U3; rewrite Zdiv_0; auto with zarith.
 split; auto with zarith.
 unfold w_digits; rewrite Zpos_minus; auto with zarith.
 generalize (F p); auto with zarith.
 Qed.

 Lemma _mul_mod_spec: forall w1 w2, _wf w1 -> _wf w2 ->
   [|_mul_mod w1 w2|] = ([|w1|] * [|w2|]) mod [|b|].
 intros w2 w3; unfold _wf, _mul_mod, ww_compare, wwb, w_mul_c; intros H H1.
 match goal with |- context[znz_mul_c _ ?x ?y] =>
   generalize (spec_mul_c op_spec x y); unfold interp_carry;
   case (znz_mul_c w_op x y); autorewrite with w_rewrite
 end; auto with zarith.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 match goal with |- context[znz_compare
 _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 intros H2 H3 H4; rewrite <- H4.
 simpl; rewrite (spec_0 op_spec).
 rewrite Zmod_def_small; auto with zarith.
 simpl; intros w4 s5 H2.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 intros H3; rewrite <- H2; rewrite H3; simpl.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 intros H4; rewrite H4; rewrite Z_mod_same; auto with zarith.
 intros H4; rewrite Zmod_def_small; auto with zarith.
 case (spec_to_Z op_spec s5); auto with zarith.
 rewrite H3 in H2; simpl in H2.
 generalize (ww_lsl_n_spec (WW w4 s5)); 
  case (ww_lsl_n (WW w4 s5)); auto with arith.
 simpl; rewrite H3; rewrite H2; simpl.
 intros H4 H5; contradict H5; apply Zle_not_gt.
 apply Zmult_le_reg_r with (2 ^ Z_of_N n); auto with zarith.
 rewrite Zmult_comm; rewrite <- H4; auto with zarith.
 apply ZAux.Zmult_lt_compat_bis.
 case (spec_to_Z op_spec w2); auto with zarith.
 case (spec_to_Z op_spec w3); auto with zarith.
 simpl; rewrite H3; rewrite Zmult_0_l; rewrite Zplus_0_l.
 intros w5 w6; simpl; intros H4 H5.
 match type of H4 with ?X -> ?Y =>
   assert (tmp: X); 
    [idtac | generalize (H4 tmp); clear tmp H4; intros H4]
 end.
 rewrite H2; apply ZAux.Zmult_lt_compat_bis.
 case (spec_to_Z op_spec w2); auto with zarith.
 case (spec_to_Z op_spec w3); auto with zarith.
 unfold w_div21; generalize (spec_div21 op_spec w5 w6 b2n);
   case (znz_div21 w_op w5 w6 b2n).
 intros w7 w8 H6; case H6.
 rewrite b2n_spec; case (n_spec); auto.
 rewrite b2n_spec.
 case (Zle_or_lt (2 ^ Z_of_N n * [|b|]) [|w5|]); auto; intros H7.
 match type of H4 with ?X = ?Y =>
    absurd (Y < X)
 end.
 apply Zle_not_lt; rewrite H4; auto with zarith.
 rewrite H2.
 match goal with |- ?X < ?Y + _ =>
    apply Zlt_le_trans with Y; auto with zarith
 end.
 rewrite Zmult_assoc; match goal with |- ?X * ?Y < _ =>
    apply Zle_lt_trans with ([|w5|] * Y); auto with zarith
 end.
 apply Zmult_le_compat_r; auto with zarith.
 case (spec_to_Z op_spec w3); auto with zarith.
 apply Zmult_lt_compat_l; auto with zarith.
 apply Zlt_le_trans with (2 := H7); auto with zarith.
 apply Zlt_trans with [|b|]; auto with zarith.
 case (spec_to_Z op_spec b); auto with zarith.
 case (spec_to_Z op_spec w6); auto with zarith.
 clear H6; rewrite b2n_spec; auto with zarith; intros H6 H7.
 rewrite w_lsr_n_spec; auto with zarith.
 rewrite H6 in H4.
 match type of H4 with ?X * (?Y * ?Z) + ?T = ?Y * ?U =>
   replace T with (Y * (U - X * Z))
 end; auto with zarith.
 rewrite Zmult_comm; rewrite Z_div_mult; auto with zarith.           
 match goal with |- ?X - ?Y = ?X mod ?T =>
  apply trans_equal with (((X - Y) + Y) mod T)
 end.
 rewrite Z_mod_plus; auto with zarith.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 split; auto with zarith.
 apply Zmult_le_reg_r with (2 ^ Z_of_N n); auto with zarith.
 rewrite Zmult_0_l; rewrite Zmult_comm.
 rewrite Zmult_minus_distr_l.
 rewrite <- H4; auto with zarith.
 match goal with |- 0 <= ?X =>
  replace X with [|w8|]; auto with zarith
 end; ring.
 apply Zmult_lt_reg_r with (2 ^ Z_of_N n); auto with zarith.
 repeat rewrite (fun x y => Zmult_comm x (2 ^y)).
 rewrite Zmult_minus_distr_l.
 rewrite <- H4; auto with zarith.
 match goal with |- ?X < _ =>
  replace X with [|w8|]; auto with zarith
 end; ring.
 eq_tac; auto with zarith.
 rewrite Zmult_minus_distr_l; rewrite <- H4; auto with zarith.
 ring.
 case (spec_to_Z op_spec w4); auto with zarith.
 intros H3.
 assert (F0: [[WW w4 s5]] < [|b|] * [|b|]).
 simpl; rewrite H2; apply ZAux.Zmult_lt_compat_bis.
 case (spec_to_Z op_spec w2); auto with zarith.
 case (spec_to_Z op_spec w3); auto with zarith.
 generalize (ww_lsl_n_spec (WW w4 s5) F0); clear F0;
  case (ww_lsl_n (WW w4 s5)); auto with arith.
 simpl.
 intros HH.
 match type of HH with ?Y = ?Z =>
    absurd (Y < Z)
 end.
 rewrite <- HH; auto with zarith.
 apply ZAux.Zmult_lt_0_compat; auto with zarith.
 match goal with |- ?X < ?Y + ?Z =>
    apply Zlt_le_trans with Y; auto with zarith
 end.
 apply ZAux.Zmult_lt_0_compat; auto with zarith.
 unfold base; apply ZPowerAux.Zpower_lt_0; auto with zarith.
 case (spec_to_Z op_spec s5); auto with zarith.
 intros w5 w6; simpl; intros H4.
 unfold w_div21; generalize (spec_div21 op_spec w5 w6 b2n);
   case (znz_div21 w_op w5 w6 b2n).
 intros w7 w8 H6; case H6.
 rewrite b2n_spec; case (n_spec); auto.
 rewrite b2n_spec.
 case (Zle_or_lt (2 ^ Z_of_N n * [|b|]) [|w5|]); auto; intros H7.
 match type of H4 with ?X = ?Y =>
    absurd (Y < X)
 end.
 apply Zle_not_lt; rewrite H4; auto with zarith.
 rewrite H2.
 match goal with |- ?X < ?Y + _ =>
    apply Zlt_le_trans with Y; auto with zarith
 end.
 rewrite Zmult_assoc; match goal with |- ?X * ?Y < _ =>
    apply Zle_lt_trans with ([|w5|] * Y); auto with zarith
 end.
 apply Zmult_le_compat_r; auto with zarith.
 case (spec_to_Z op_spec w3); auto with zarith.
 apply Zmult_lt_compat_l; auto with zarith.
 apply Zlt_le_trans with (2 := H7); auto with zarith.
 apply Zlt_trans with [|b|]; auto with zarith.
 case (spec_to_Z op_spec b); auto with zarith.
 case (spec_to_Z op_spec w6); auto with zarith.
 clear H6; rewrite b2n_spec; auto with zarith; intros H6 H7.
 rewrite w_lsr_n_spec; auto with zarith.
 rewrite H6 in H4.
 match type of H4 with ?X * (?Y * ?Z) + ?T = ?Y * ?U =>
   replace T with (Y * (U - X * Z))
 end; auto with zarith.
 rewrite Zmult_comm; rewrite Z_div_mult; auto with zarith.           
 rewrite <- H2;
 match goal with |- ?X - ?Y = ?X mod ?T =>
  apply trans_equal with (((X - Y) + Y) mod T)
 end.
 rewrite Z_mod_plus; auto with zarith.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 split; auto.
 apply Zmult_le_reg_r with (2 ^ Z_of_N n); auto with zarith.
 rewrite Zmult_0_l; rewrite Zmult_comm.
 rewrite Zmult_minus_distr_l.
 rewrite <- H4; auto with zarith.
 match goal with |- 0 <= ?X =>
  replace X with [|w8|]; auto with zarith
 end; ring.
 apply Zmult_lt_reg_r with (2 ^ Z_of_N n); auto with zarith.
 repeat rewrite (fun x y => Zmult_comm x (2 ^y)).
 rewrite Zmult_minus_distr_l.
 rewrite <- H4; auto with zarith.
 match goal with |- ?X < _ =>
  replace X with [|w8|]; auto with zarith
 end; ring.
 eq_tac; auto with zarith.
 rewrite Zmult_minus_distr_l; rewrite <- H4; auto with zarith.
 ring.
 Qed.

 Lemma _mul_mod_wf_spec: forall w1 w2, _wf w1 -> _wf w2 ->
   _wf (_mul_mod w1 w2).
 intros w2 w3 H H1.
 unfold _wf; rewrite _mul_mod_spec; auto.
 case (Z_mod_lt ([|w2|] * [|w3|]) [|b|]); auto with zarith.
 Qed.

 Let _square_mod x :=
  let x2 := w_square_c x in
  match ww_compare w_op x2 wwb with
  | Lt => snd (split x2)
  | Eq => w0
  | Gt =>
    let x2_2n := ww_lsl_n x2 in
    let (h,l) := split x2_2n in
    let (q,r) := w_div21 h l b2n in
    w_lsr_n r
  end.

 Lemma _square_mod_spec: forall w, _wf w ->
    [|_square_mod w|] = ([|w|] * [|w|]) mod [|b|].
 intros w2; unfold _wf, _square_mod, ww_compare, w_square_c.
 match goal with |- context[znz_square_c _ ?x] =>
   generalize (spec_square_c op_spec x); unfold interp_carry;
   case (znz_square_c w_op x); autorewrite with w_rewrite
 end; auto with zarith.
 simpl.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 match goal with |- context[znz_compare
 _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 intros H2 H3 H4 _; rewrite <- H4.
 rewrite Zmod_def_small; auto with zarith.
 simpl; intros w3 s4 H2.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 intros H3; rewrite <- H2; rewrite H3; simpl.
 match goal with |- context[znz_compare _ ?x ?y] =>
   generalize (spec_compare op_spec x y);
   case (znz_compare w_op x y); autorewrite with w_rewrite
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 intros H4 _; rewrite H4.
 rewrite Z_mod_same; auto with zarith.
 intros H4 _; rewrite Zmod_def_small; auto with zarith.
 case (spec_to_Z op_spec s4); auto with zarith.
 rewrite H3 in H2; simpl in H2.
 intros H4 H5.
 assert (F0: [[WW w3 s4]] < [|b|] * [|b|]).
 simpl; rewrite H3; simpl; rewrite H2.
 apply ZAux.Zmult_lt_compat_bis.
 case (spec_to_Z op_spec w2); auto with zarith.
 case (spec_to_Z op_spec w2); auto with zarith.
 generalize (ww_lsl_n_spec (WW w3 s4) F0); clear F0;
  case (ww_lsl_n (WW w3 s4)); auto with arith.
 simpl; rewrite H3; rewrite H2; simpl; rewrite H2 in H4.
 intros H6; contradict H4; apply Zle_not_gt.
 apply Zmult_le_reg_r with (2 ^ Z_of_N n); auto with zarith.
 rewrite Zmult_comm; rewrite <- H6; auto with zarith.
 simpl; rewrite H3; rewrite Zmult_0_l; rewrite Zplus_0_l.
 intros w4 w5; simpl; intros H6.
 unfold w_div21; generalize (spec_div21 op_spec w4 w5 b2n);
   case (znz_div21 w_op w4 w5 b2n).
 intros w6 w7 H7; case H7; clear H7.
 rewrite b2n_spec; case (n_spec); auto.
 rewrite b2n_spec.
 apply Zmult_lt_reg_r with (base (znz_digits w_op)); auto with zarith.
 unfold base; auto with zarith.
 match type of H6 with ?X = _ =>
   apply Zle_lt_trans with X
 end; auto with zarith.
 case (spec_to_Z op_spec w5); auto with zarith.
 rewrite H6. 
 rewrite <- Zmult_assoc; apply Zmult_lt_compat_l; auto with zarith.
 simpl; rewrite H2; apply ZAux.Zmult_lt_compat_bis.
 case (spec_to_Z op_spec w2); auto with zarith.
 case (spec_to_Z op_spec w2); auto with zarith.
 rewrite b2n_spec; auto with zarith; intros H7 H8.
 rewrite w_lsr_n_spec; auto with zarith.
 rewrite H7 in H6.
 match type of H6 with ?X * (?Y * ?Z) + ?T = ?Y * ?U =>
   replace T with (Y * (U - X * Z))
 end; auto with zarith.
 rewrite Zmult_comm; rewrite Z_div_mult; auto with zarith.           
 match goal with |- ?X - ?Y = ?X mod ?T =>
  apply trans_equal with (((X - Y) + Y) mod T)
 end.
 rewrite Z_mod_plus; auto with zarith.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 split; auto with zarith.
 apply Zmult_le_reg_r with (2 ^ Z_of_N n); auto with zarith.
 rewrite Zmult_0_l; rewrite Zmult_comm.
 rewrite Zmult_minus_distr_l.
 rewrite <- H6; auto with zarith.
 match goal with |- 0 <= ?X =>
  replace X with [|w7|]; auto with zarith
 end; ring.
 apply Zmult_lt_reg_r with (2 ^ Z_of_N n); auto with zarith.
 repeat rewrite (fun x y => Zmult_comm x (2 ^y)).
 rewrite Zmult_minus_distr_l.
 rewrite <- H6; auto with zarith.
 match goal with |- ?X < _ =>
  replace X with [|w7|]; auto with zarith
 end; ring.
 eq_tac; auto with zarith.
 rewrite Zmult_minus_distr_l; rewrite <- H6; auto with zarith.
 ring.
 case (spec_to_Z op_spec w3); auto with zarith.
 intros H3 H4.
 assert (F0: [[WW w3 s4]] < [|b|] * [|b|]).
 simpl; rewrite H2; apply ZAux.Zmult_lt_compat_bis.
 case (spec_to_Z op_spec w2); auto with zarith.
 case (spec_to_Z op_spec w2); auto with zarith.
 generalize (ww_lsl_n_spec (WW w3 s4) F0); clear F0;
  case (ww_lsl_n (WW w3 s4)); auto with arith.
 simpl.
 intros HH.
 match type of HH with ?Y = ?Z =>
    absurd (Y < Z)
 end.
 rewrite <- HH; auto with zarith.
 apply ZAux.Zmult_lt_0_compat; auto with zarith.
 match goal with |- ?X < ?Y + ?Z =>
    apply Zlt_le_trans with Y; auto with zarith
 end.
 apply ZAux.Zmult_lt_0_compat; auto with zarith.
 unfold base; apply ZPowerAux.Zpower_lt_0; auto with zarith.
 case (spec_to_Z op_spec s4); auto with zarith.
 intros w4 w5; simpl; intros H5.
 unfold w_div21; generalize (spec_div21 op_spec w4 w5 b2n);
   case (znz_div21 w_op w4 w5 b2n).
 intros w6 w7 H6; case H6.
 rewrite b2n_spec; case (n_spec); auto.
 rewrite b2n_spec.
 case (Zle_or_lt (2 ^ Z_of_N n * [|b|]) [|w4|]); auto; intros H7.
 match type of H5 with ?X = ?Y =>
    absurd (Y < X)
 end.
 apply Zle_not_lt; rewrite H5; auto with zarith.
 rewrite H2.
 match goal with |- ?X < ?Y + _ =>
    apply Zlt_le_trans with Y; auto with zarith
 end.
 rewrite Zmult_assoc; match goal with |- ?X * ?Y < _ =>
    apply Zle_lt_trans with ([|w4|] * Y); auto with zarith
 end.
 apply Zmult_le_compat_r; auto with zarith.
 case (spec_to_Z op_spec w2); auto with zarith.
 apply Zmult_lt_compat_l; auto with zarith.
 apply Zlt_le_trans with (2 := H7); auto with zarith.
 case (spec_to_Z op_spec w2); auto with zarith.
 case (spec_to_Z op_spec w5); auto with zarith.
 clear H6; rewrite b2n_spec; auto with zarith; intros H6 H7.
 rewrite w_lsr_n_spec; auto with zarith.
 rewrite H6 in H5.
 match type of H5 with ?X * (?Y * ?Z) + ?T = ?Y * ?U =>
   replace T with (Y * (U - X * Z))
 end; auto with zarith.
 rewrite Zmult_comm; rewrite Z_div_mult; auto with zarith.           
 rewrite <- H2;
 match goal with |- ?X - ?Y = ?X mod ?T =>
  apply trans_equal with (((X - Y) + Y) mod T)
 end.
 rewrite Z_mod_plus; auto with zarith.
 apply sym_equal; apply Zmod_def_small; auto with zarith.
 split; auto.
 apply Zmult_le_reg_r with (2 ^ Z_of_N n); auto with zarith.
 rewrite Zmult_0_l; rewrite Zmult_comm.
 rewrite Zmult_minus_distr_l.
 rewrite <- H5; auto with zarith.
 match goal with |- 0 <= ?X =>
  replace X with [|w7|]; auto with zarith
 end; ring.
 apply Zmult_lt_reg_r with (2 ^ Z_of_N n); auto with zarith.
 repeat rewrite (fun x y => Zmult_comm x (2 ^y)).
 rewrite Zmult_minus_distr_l.
 rewrite <- H5; auto with zarith.
 match goal with |- ?X < _ =>
  replace X with [|w7|]; auto with zarith
 end; ring.
 eq_tac; auto with zarith.
 rewrite Zmult_minus_distr_l; rewrite <- H5; auto with zarith.
 ring.
 Qed.

 Lemma _square_mod_wf_spec: forall w, _wf w ->
   _wf (_square_mod w).
 intros w2 H.
 unfold _wf; rewrite _square_mod_spec; auto.
 case (Z_mod_lt ([|w2|] * [|w2|]) [|b|]); auto with zarith.
 Qed.

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

 Lemma _power_mod_spec: forall w p, _wf w ->
   [|_power_mod w p|] = (Zpower_pos [|w|] p) mod [|b|].
 assert(aux: forall w p, _wf w ->
   [|_power_mod w p|] = (Zpower_pos [|w|] p) mod [|b|] /\ _wf (_power_mod w p)).
 intros w2 p; elim p; simpl; auto with zarith.
 intros p' Rec H. 
 case (Rec H); intros Rec1 Rec2; clear Rec.
 match goal with |- ?A /\ ?B =>
   assert A; try (split; auto)
 end.
 replace (xI p') with (p' + p' + 1)%positive.
 repeat rewrite Zpower_pos_is_exp; auto with zarith.
 rewrite _mul_mod_spec; auto with zarith.
 rewrite _square_mod_spec; auto with zarith.
 rewrite Rec1; auto with zarith.
 assert (tmp: forall p, Zpower_pos p 1 = p); try (rewrite tmp; clear tmp).
 intros p1; unfold Zpower_pos; simpl; ring.
 rewrite <- Zmod_mult; auto with zarith.
 rewrite Zmod_mult; auto with zarith.
 rewrite Zmod_mod; auto with zarith.
 rewrite <- Zmod_mult; auto with zarith.
 apply _square_mod_wf_spec; auto.
 rewrite xI_succ_xO; rewrite <- Pplus_diag.
 rewrite Pplus_one_succ_r; auto.
 apply _mul_mod_wf_spec; auto with zarith.
 apply _square_mod_wf_spec; auto with zarith.
 intros p' Rec H. 
 case (Rec H); intros Rec1 Rec2; clear Rec.
 match goal with |- ?A /\ ?B =>
   assert A; try (split; auto)
 end.
 replace (xO p') with (p' + p')%positive.
 repeat rewrite Zpower_pos_is_exp; auto with zarith.
 rewrite _square_mod_spec; auto with zarith.
 rewrite Rec1; auto with zarith.
 rewrite <- Zmod_mult; auto with zarith.
 rewrite <- Pplus_diag; auto.
 apply _square_mod_wf_spec; auto with zarith.
 intros H; split; auto.
 assert (tmp: forall p, Zpower_pos p 1 = p); try (rewrite tmp; clear tmp).
 intros p1; unfold Zpower_pos; simpl; ring.
 red in H; rewrite Zmod_def_small; auto with zarith.
 case (spec_to_Z op_spec w2); auto with zarith.
 intros w2 p H; case (aux w2 p); auto.
 Qed.

 Lemma _power_mod_wf_spec: forall w p, _wf w ->
   _wf (_power_mod w p).
 intros w2 p H.
 unfold _wf; rewrite _power_mod_spec; auto.
 case (Z_mod_lt (Zpower_pos [|w2|] p) [|b|]); auto with zarith.
 Qed.

(*
      shift_spec        :
              forall w p, wf w -> 
                          [|shift m_op w p|] = ([|w|] / (Zpower_pos 2 p)) mod [|b|];
      trunc_spec        :
              forall w p, wf w ->
                          [|power_mod m_op w p|] = ([|w1|] mod (Zpower_pos 2 p)) mod [|b|]
*)

 Definition make_mod_op := 
   mk_mod_op
     _w0_mod _w1_mod 
     _succ_mod _add_mod 
     _pred_mod _sub_mod
     _mul_mod _square_mod _power_mod.

  Definition new_mod_spec: mod_spec make_mod_op _wf.
  apply mk_mod_spec.
  exact _w0_wf.
  exact _w1_wf.
  exact _succ_mod_wf_spec.
  exact _add_mod_wf_spec.
  exact _pred_mod_wf_spec.
  exact _sub_mod_wf_spec.
  exact _mul_mod_wf_spec.
  exact _square_mod_wf_spec.
  exact _power_mod_wf_spec.
  rewrite _w0_is_0; apply Zmod_def_small; auto with zarith.
  rewrite _w1_is_1; apply Zmod_def_small; auto with zarith.
  exact _succ_mod_spec.
  exact _add_mod_spec.
  exact _pred_mod_spec.
  exact _sub_mod_spec.
  exact _mul_mod_spec.
  exact _square_mod_spec.
  exact _power_mod_spec.
  Defined.

End Mod_op.
    
