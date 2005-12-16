Require Import ZArith.
Open Local Scope Z_scope.
Require Import W8_basic.
Require Import W8_basic_spec.
Open Local Scope w8_scope.
Require Import W8_div.


Require Import W8_compare.
Require Import W8_add.
Require Import W8_sub.
Require Import W8_compare_spec.
Require Import W8_succ_c_spec.
Require Import W8_add_c_spec.
Require Import W8_sub_spec.
Require Import W8_div_wB_spec.
Require Import ZDivModAux.
Open Local Scope Z_scope.
Lemma w8_div21_spec : forall a1 a2 b,
     w8_B/2 <= [|b|] ->
     let (q,r) := w8_div21 a1 a2 b in
     [|a1|] *w8_B+ [|a2|] = [+|q|] *  [|b|] + [|r|] /\ 0 <= [|r|] < [|b|].
Proof.
 intros a1 a2 b Hle.
 unfold w8_div21.
 assert (H := w8_div_wB_spec a1 b Hle);destruct (w8_div_wB a1 b).
 destruct H as (H,Hltb).
 assert (Hlt:0<[|b|]).
  unfold w8_B,Zdiv in Hle;simpl in Hle;omega.
 assert (Hle_a1 : [|a1|]*w8_B <= ((w8_B + (w8_B - 2)) * [|b|])).
  replace ((w8_B + (w8_B - 2)) * [|b|]) with ((w8_B -1)*(2*[|b|])).
  apply Zmult_le_compat.
  assert (H1 := w8_to_Z_spec a1);omega.
  change w8_B with (2*(w8_B/2)).
  apply Zmult_le_compat_l;trivial.
  intro H1;discriminate H1.
  destruct(w8_to_Z_spec a1);trivial.
  intro H1;discriminate H1.
  ring.
 assert ([+|c|] <= w8_B + (w8_B -2)).
  apply Zmult_le_reg_r with [|b|].
  omega.
  apply Zplus_le_reg_r with [|w|].
  rewrite <- H.
  apply Zle_trans with ((w8_B + (w8_B - 2)) * [|b|]).
  trivial.
  assert (H1 := w8_to_Z_spec w);omega.
 assert (H1 := w8_add_c_spec w a2);destruct (w8_add_c w a2) as [r|r].
 assert (H2 := w8_compare_spec r b);destruct (w8_compare r b).
 rewrite (w8_carry_succ_c_spec c H0);rewrite H.
 rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1;rewrite H2.
 simpl;split;[ring|omega].
 rewrite H;rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1.
 split;[trivial| assert (H3 := w8_to_Z_spec r);omega].
 rewrite (w8_carry_succ_c_spec c H0);rewrite H.
 rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1.
 rewrite (w8_sub_spec r b).
 assert (H3 := w8_to_Z_spec r);assert (H4 := w8_to_Z_spec b).
 change w8_B with (2*(w8_B/2)) in H3.
 rewrite Zmod_def_small.
 simpl;split;[ring|omega].  omega.
 unfold interp_carry in H1;rewrite Zmult_1_l in H1.
 assert ([|r|] < [|b|]).
  apply  Zplus_lt_reg_l with w8_B.
  rewrite H1;rewrite Zplus_comm;apply Zplus_lt_compat;trivial.
  assert (H2 := w8_to_Z_spec a2);omega.
 assert ([|w8_sub r b|] = w8_B + [|r|] - [|b|]).
  rewrite w8_sub_spec.
  replace (([|r|] - [|b|]) mod w8_B) with ((w8_B + ([|r|] - [|b|])) mod w8_B).
  rewrite Zmod_def_small. ring.
  assert (H3 := w8_to_Z_spec b); assert (H4 := w8_to_Z_spec r);omega.
  rewrite Zmod_plus. rewrite Z_mod_same. simpl;apply Zmod_mod.
  exact (refl_equal Lt). exact (refl_equal Gt). exact (refl_equal Lt).
 rewrite H;rewrite <- Zplus_assoc;rewrite <- H1.
 assert (H4 := w8_compare_spec (w8_sub r b) b);
   destruct (w8_compare (w8_sub r b) b).
 split;[idtac|simpl;auto with zarith].
 rewrite w8_0_spec;rewrite Zplus_0_r.
 rewrite w8_carry_succ_c_spec.
 rewrite (w8_carry_succ_c_spec c H0).
 replace (w8_B + [|r|]) with ([|b|] + [|b|]).
 ring. rewrite H4 in H3;pattern [|b|] at 1;rewrite H3;ring.
 rewrite (w8_carry_succ_c_spec c H0).
 destruct (Zle_lt_or_eq _ _ H0). omega.
 rewrite H5 in H.
 assert (H6:= w8_to_Z_spec r);assert (H7:= w8_to_Z_spec a2);
 assert (H8:= w8_to_Z_spec w);omega.
 split.
 rewrite H3;rewrite (w8_carry_succ_c_spec c H0);ring.
 assert (H5 := w8_to_Z_spec (w8_sub r b));omega.
 rewrite w8_carry_succ_c_spec.
 rewrite (w8_carry_succ_c_spec c H0).
 rewrite w8_sub_spec.
 rewrite Zmod_def_small.
 split. rewrite H3;ring.
 assert (H5 := w8_to_Z_spec (w8_sub r b)).
 change w8_B with (2*(w8_B/2)) in H5;omega.
 omega.
 rewrite (w8_carry_succ_c_spec c H0).
 destruct (Zle_lt_or_eq _ _ H0). omega.
 rewrite H5 in H.
 assert (H6:= w8_to_Z_spec r);assert (H7:= w8_to_Z_spec a2);
 assert (H8:= w8_to_Z_spec w);omega.
Qed.

