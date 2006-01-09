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
Require Import W8_add_mul_div_spec.
Require Import W8_head0_spec.
Require Import ZDivModAux.
Require Import ZnZDivn1.
Open Local Scope Z_scope.
Lemma w8_div21_spec : forall a1 a2 b,
     w8_B/2 <= [|b|] ->
     [|a1|] < [|b|] ->
     let (q,r) := w8_div21 a1 a2 b in
     [|a1|] *w8_B+ [|a2|] = [|q|] *  [|b|] + [|r|] /\ 0 <= [|r|] < [|b|].
Proof.
 intros a1 a2 b Hle Hlta1b.
 unfold w8_div21.
 assert (H := w8_div_wB_spec a1 b Hle Hlta1b);
   destruct (w8_div_wB a1 b) as (q,s).
 destruct H as (H,Hltb).
 assert (Hlt:0<[|b|]).
  unfold w8_B,Zdiv in Hle;simpl in Hle;omega.
 assert (Ha1 := w8_to_Z_spec a1).
 assert (Hb := w8_to_Z_spec b).
 assert (Hs := w8_to_Z_spec s).
 assert (Hq := w8_to_Z_spec q).
 assert (Hqle2: [|q|] <= w8_B - 2).
  assert (Hqle1: [|q|] <= w8_B - 1). omega.
  destruct (Zle_lt_or_eq _ _ Hqle1). omega.
  rewrite H0 in H.
  assert (w8_B *[|b|] - [|b|]+ [|s|] <= w8_B*[|b|] - w8_B). 2:omega.
   replace (w8_B *[|b|] - [|b|]+ [|s|]) with
     ((w8_B -1)*[|b|] + [|s|]);try ring.
   replace (w8_B*[|b|] - w8_B) with
     (([|b|] - 1)*w8_B);try ring.
   rewrite <- H.
   apply Zmult_le_compat; omega. 
 assert (H1 := w8_add_c_spec s a2);destruct (w8_add_c s a2) as [r|r].
 assert (H2 := w8_compare_spec r b);destruct (w8_compare r b).
 rewrite (w8_succ_spec q);rewrite H.
 rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1;rewrite H2.
 rewrite Zmod_def_small;try omega.
 simpl;split;[ring|omega].
 rewrite H;rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1.
 split;[trivial| assert (H3 := w8_to_Z_spec r);omega].
 rewrite (w8_succ_spec q);rewrite H.
 rewrite Zmod_def_small;try omega.
 rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1.
 rewrite (w8_sub_spec r b).
 assert (H3 := w8_to_Z_spec r); change w8_B with (2*(w8_B/2)) in H3.
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
 assert (Ha2 := w8_to_Z_spec a2).
 assert (H4 := w8_compare_spec (w8_sub r b) b);
   destruct (w8_compare (w8_sub r b) b).
 split;[idtac|simpl;auto with zarith].
 rewrite w8_0_spec;rewrite Zplus_0_r.
 rewrite w8_succ_spec.
 rewrite w8_succ_spec.
 rewrite (Zmod_def_small ([|q|]+1));try omega.
 assert (w8_B + [|r|] =[|b|] + [|b|]).
 rewrite H4 in H2;pattern [|b|] at 1;rewrite H2;ring.
 assert ([|q|] < w8_B - 2).
   destruct (Zle_lt_or_eq _ _ Hqle2);trivial.
   assert (w8_B*[|b|] - (w8_B + [|r|]) + [|s|] <= w8_B*[|b|] - w8_B).
   rewrite H3.
   replace (w8_B * [|b|] - ([|b|] + [|b|]) + [|s|]) with
     ((w8_B - 2)*[|b|] + [|s|]);try ring.
   replace (w8_B * [|b|] - w8_B) with
           (([|b|] - 1) * w8_B);try ring.
   rewrite <- H5;rewrite <- H.
   apply Zmult_le_compat;omega.
   omega.
 rewrite Zmod_def_small;try omega.
 rewrite H3;ring.
 split.
 rewrite H2;rewrite w8_succ_spec;rewrite Zmod_def_small;try omega. ring.
 assert (H5 := w8_to_Z_spec (w8_sub r b));omega.
 rewrite w8_succ_spec.
 rewrite w8_succ_spec.
 rewrite (Zmod_def_small ([|q|]+1));try omega.
 assert (w8_B + [|r|] > [|b|] + [|b|]). omega.
 assert ([|q|] < w8_B - 2).
   destruct (Zle_lt_or_eq _ _ Hqle2);trivial.
   assert (w8_B*[|b|] - (w8_B + [|r|]) + [|s|] <= w8_B*[|b|] - w8_B).
   apply Zle_trans with (w8_B * [|b|] - ([|b|] + [|b|]) + [|s|]);try omega.
   replace (w8_B * [|b|] - ([|b|] + [|b|]) + [|s|]) with
     ((w8_B - 2)*[|b|] + [|s|]);try ring.
   replace (w8_B * [|b|] - w8_B) with
           (([|b|] - 1) * w8_B);try ring.
   rewrite <- H5;rewrite <- H.
   apply Zmult_le_compat;omega.
   omega.
 rewrite Zmod_def_small;try omega.
 rewrite w8_sub_spec.
 rewrite Zmod_def_small;try omega.
 split. rewrite H2;ring.
 assert (H6 := w8_to_Z_spec (w8_sub r b)).
 change w8_B with (2*(w8_B/2)) in H6;omega.
Qed.

Lemma w8_divn1_spec : forall n x y, 0<[|y|] ->
    let (q,r) := w8_divn1 n x y in
    gen_to_Z 8 w8_to_Z n (word_of_word_tr w8 n x) =
      gen_to_Z 8 w8_to_Z n q * w8_to_Z y + w8_to_Z r /\ 
    0 <= [|r|] < [|y|].
Proof
fun n x y (H:0<[|y|]) =>
  @spec_gen_divn1 w8 8
     OOOOOOOO w8_WW
 w8_head0 w8_add_mul_div w8_div21 w8_to_Z
     w8_to_Z_spec (refl_equal 0)
     w8_WW_spec w8_head0_spec
     w8_add_mul_div_spec w8_div21_spec
     n (word_of_word_tr w8 n x) y H.

Lemma w8_modn1_spec : forall n x y, 0 < [|y|] ->
    [|w8_modn1 n x y|] = (gen_to_Z 8 w8_to_Z n (word_of_word_tr w8 n x)) mod [|y|].
Proof
fun n x y (H:0<[|y|]) =>
  @spec_gen_modn1 w8 8
     OOOOOOOO w8_WW
 w8_head0 w8_add_mul_div w8_div21 w8_to_Z
     w8_to_Z_spec (refl_equal 0)
     w8_WW_spec w8_head0_spec
     w8_add_mul_div_spec w8_div21_spec
     n (word_of_word_tr w8 n x) y H.

