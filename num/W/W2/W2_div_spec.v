Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Require Import W2_basic_spec.
Open Local Scope w2_scope.
Require Import W2_div.


Require Import W2_compare.
Require Import W2_add.
Require Import W2_sub.
Require Import W2_compare_spec.
Require Import W2_succ_c_spec.
Require Import W2_add_c_spec.
Require Import W2_sub_spec.
Require Import W2_div_wB_spec.
Require Import ZDivModAux.
Open Local Scope Z_scope.
Lemma w2_div21_spec : forall a1 a2 b,
     w2_B/2 <= [|b|] ->
     let (q,r) := w2_div21 a1 a2 b in
     [|a1|] *w2_B+ [|a2|] = [+|q|] *  [|b|] + [|r|] /\ 0 <= [|r|] < [|b|].
Proof.
 intros a1 a2 b Hle.
 unfold w2_div21.
 assert (H := w2_div_wB_spec a1 b Hle);destruct (w2_div_wB a1 b).
 destruct H as (H,Hltb).
 assert (Hlt:0<[|b|]).
  unfold w2_B,Zdiv in Hle;simpl in Hle;omega.
 assert (Hle_a1 : [|a1|]*w2_B <= ((w2_B + (w2_B - 2)) * [|b|])).
  replace ((w2_B + (w2_B - 2)) * [|b|]) with ((w2_B -1)*(2*[|b|])).
  apply Zmult_le_compat.
  assert (H1 := w2_to_Z_spec a1);omega.
  change w2_B with (2*(w2_B/2)).
  apply Zmult_le_compat_l;trivial.
  intro H1;discriminate H1.
  destruct(w2_to_Z_spec a1);trivial.
  intro H1;discriminate H1.
  ring.
 assert ([+|c|] <= w2_B + (w2_B -2)).
  apply Zmult_le_reg_r with [|b|].
  omega.
  apply Zplus_le_reg_r with [|w|].
  rewrite <- H.
  apply Zle_trans with ((w2_B + (w2_B - 2)) * [|b|]).
  trivial.
  assert (H1 := w2_to_Z_spec w);omega.
 assert (H1 := w2_add_c_spec w a2);destruct (w2_add_c w a2) as [r|r].
 assert (H2 := w2_compare_spec r b);destruct (w2_compare r b).
 rewrite (w2_carry_succ_c_spec c H0);rewrite H.
 rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1;rewrite H2.
 simpl;split;[ring|omega].
 rewrite H;rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1.
 split;[trivial| assert (H3 := w2_to_Z_spec r);omega].
 rewrite (w2_carry_succ_c_spec c H0);rewrite H.
 rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1.
 rewrite (w2_sub_spec r b).
 assert (H3 := w2_to_Z_spec r);assert (H4 := w2_to_Z_spec b).
 change w2_B with (2*(w2_B/2)) in H3.
 rewrite Zmod_def_small.
 simpl;split;[ring|omega].  omega.
 unfold interp_carry in H1;rewrite Zmult_1_l in H1.
 assert ([|r|] < [|b|]).
  apply  Zplus_lt_reg_l with w2_B.
  rewrite H1;rewrite Zplus_comm;apply Zplus_lt_compat;trivial.
  assert (H2 := w2_to_Z_spec a2);omega.
 assert ([|w2_sub r b|] = w2_B + [|r|] - [|b|]).
  rewrite w2_sub_spec.
  replace (([|r|] - [|b|]) mod w2_B) with ((w2_B + ([|r|] - [|b|])) mod w2_B).
  rewrite Zmod_def_small. ring.
  assert (H3 := w2_to_Z_spec b); assert (H4 := w2_to_Z_spec r);omega.
  rewrite Zmod_plus. rewrite Z_mod_same. simpl;apply Zmod_mod.
  exact (refl_equal Lt). exact (refl_equal Gt). exact (refl_equal Lt).
 rewrite H;rewrite <- Zplus_assoc;rewrite <- H1.
 assert (H4 := w2_compare_spec (w2_sub r b) b);
   destruct (w2_compare (w2_sub r b) b).
 split;[idtac|simpl;auto with zarith].
 rewrite w2_0_spec;rewrite Zplus_0_r.
 rewrite w2_carry_succ_c_spec.
 rewrite (w2_carry_succ_c_spec c H0).
 replace (w2_B + [|r|]) with ([|b|] + [|b|]).
 ring. rewrite H4 in H3;pattern [|b|] at 1;rewrite H3;ring.
 rewrite (w2_carry_succ_c_spec c H0).
 destruct (Zle_lt_or_eq _ _ H0). omega.
 rewrite H5 in H.
 assert (H6:= w2_to_Z_spec r);assert (H7:= w2_to_Z_spec a2);
 assert (H8:= w2_to_Z_spec w);omega.
 split.
 rewrite H3;rewrite (w2_carry_succ_c_spec c H0);ring.
 assert (H5 := w2_to_Z_spec (w2_sub r b));omega.
 rewrite w2_carry_succ_c_spec.
 rewrite (w2_carry_succ_c_spec c H0).
 rewrite w2_sub_spec.
 rewrite Zmod_def_small.
 split. rewrite H3;ring.
 assert (H5 := w2_to_Z_spec (w2_sub r b)).
 change w2_B with (2*(w2_B/2)) in H5;omega.
 omega.
 rewrite (w2_carry_succ_c_spec c H0).
 destruct (Zle_lt_or_eq _ _ H0). omega.
 rewrite H5 in H.
 assert (H6:= w2_to_Z_spec r);assert (H7:= w2_to_Z_spec a2);
 assert (H8:= w2_to_Z_spec w);omega.
Qed.

