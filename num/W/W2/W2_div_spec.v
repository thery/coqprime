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
Require Import W2_add_mul_div_spec.
Require Import W2_head0_spec.
Require Import ZDivModAux.
Require Import ZnZDivn1.
Open Local Scope Z_scope.
Lemma w2_div21_spec : forall a1 a2 b,
     w2_B/2 <= [|b|] ->
     [|a1|] < [|b|] ->
     let (q,r) := w2_div21 a1 a2 b in
     [|a1|] *w2_B+ [|a2|] = [|q|] *  [|b|] + [|r|] /\ 0 <= [|r|] < [|b|].
Proof.
 intros a1 a2 b Hle Hlta1b.
 unfold w2_div21.
 assert (H := w2_div_wB_spec a1 b Hle Hlta1b);
   destruct (w2_div_wB a1 b) as (q,s).
 destruct H as (H,Hltb).
 assert (Hlt:0<[|b|]).
  unfold w2_B,Zdiv in Hle;simpl in Hle;omega.
 assert (Ha1 := w2_to_Z_spec a1).
 assert (Hb := w2_to_Z_spec b).
 assert (Hs := w2_to_Z_spec s).
 assert (Hq := w2_to_Z_spec q).
 assert (Hqle2: [|q|] <= w2_B - 2).
  assert (Hqle1: [|q|] <= w2_B - 1). omega.
  destruct (Zle_lt_or_eq _ _ Hqle1). omega.
  rewrite H0 in H.
  assert (w2_B *[|b|] - [|b|]+ [|s|] <= w2_B*[|b|] - w2_B). 2:omega.
   replace (w2_B *[|b|] - [|b|]+ [|s|]) with
     ((w2_B -1)*[|b|] + [|s|]);try ring.
   replace (w2_B*[|b|] - w2_B) with
     (([|b|] - 1)*w2_B);try ring.
   rewrite <- H.
   apply Zmult_le_compat; omega. 
 assert (H1 := w2_add_c_spec s a2);destruct (w2_add_c s a2) as [r|r].
 assert (H2 := w2_compare_spec r b);destruct (w2_compare r b).
 rewrite (w2_succ_spec q);rewrite H.
 rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1;rewrite H2.
 rewrite Zmod_def_small;try omega.
 simpl;split;[ring|omega].
 rewrite H;rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1.
 split;[trivial| assert (H3 := w2_to_Z_spec r);omega].
 rewrite (w2_succ_spec q);rewrite H.
 rewrite Zmod_def_small;try omega.
 rewrite <- Zplus_assoc;simpl in H1;rewrite <- H1.
 rewrite (w2_sub_spec r b).
 assert (H3 := w2_to_Z_spec r); change w2_B with (2*(w2_B/2)) in H3.
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
 assert (Ha2 := w2_to_Z_spec a2).
 assert (H4 := w2_compare_spec (w2_sub r b) b);
   destruct (w2_compare (w2_sub r b) b).
 split;[idtac|simpl;auto with zarith].
 rewrite w2_0_spec;rewrite Zplus_0_r.
 rewrite w2_succ_spec.
 rewrite w2_succ_spec.
 rewrite (Zmod_def_small ([|q|]+1));try omega.
 assert (w2_B + [|r|] =[|b|] + [|b|]).
 rewrite H4 in H2;pattern [|b|] at 1;rewrite H2;ring.
 assert ([|q|] < w2_B - 2).
   destruct (Zle_lt_or_eq _ _ Hqle2);trivial.
   assert (w2_B*[|b|] - (w2_B + [|r|]) + [|s|] <= w2_B*[|b|] - w2_B).
   rewrite H3.
   replace (w2_B * [|b|] - ([|b|] + [|b|]) + [|s|]) with
     ((w2_B - 2)*[|b|] + [|s|]);try ring.
   replace (w2_B * [|b|] - w2_B) with
           (([|b|] - 1) * w2_B);try ring.
   rewrite <- H5;rewrite <- H.
   apply Zmult_le_compat;omega.
   omega.
 rewrite Zmod_def_small;try omega.
 rewrite H3;ring.
 split.
 rewrite H2;rewrite w2_succ_spec;rewrite Zmod_def_small;try omega. ring.
 assert (H5 := w2_to_Z_spec (w2_sub r b));omega.
 rewrite w2_succ_spec.
 rewrite w2_succ_spec.
 rewrite (Zmod_def_small ([|q|]+1));try omega.
 assert (w2_B + [|r|] > [|b|] + [|b|]). omega.
 assert ([|q|] < w2_B - 2).
   destruct (Zle_lt_or_eq _ _ Hqle2);trivial.
   assert (w2_B*[|b|] - (w2_B + [|r|]) + [|s|] <= w2_B*[|b|] - w2_B).
   apply Zle_trans with (w2_B * [|b|] - ([|b|] + [|b|]) + [|s|]);try omega.
   replace (w2_B * [|b|] - ([|b|] + [|b|]) + [|s|]) with
     ((w2_B - 2)*[|b|] + [|s|]);try ring.
   replace (w2_B * [|b|] - w2_B) with
           (([|b|] - 1) * w2_B);try ring.
   rewrite <- H5;rewrite <- H.
   apply Zmult_le_compat;omega.
   omega.
 rewrite Zmod_def_small;try omega.
 rewrite w2_sub_spec.
 rewrite Zmod_def_small;try omega.
 split. rewrite H2;ring.
 assert (H6 := w2_to_Z_spec (w2_sub r b)).
 change w2_B with (2*(w2_B/2)) in H6;omega.
Qed.

Lemma w2_divn1_spec : forall n x y, 0<[|y|] ->
    let (q,r) := w2_divn1 n x y in
    gen_to_Z 2 w2_to_Z n (word_of_word_tr w2 n x) =
      gen_to_Z 2 w2_to_Z n q * w2_to_Z y + w2_to_Z r /\ 
    0 <= [|r|] < [|y|].
Proof
fun n x y (H:0<[|y|]) =>
  @spec_gen_divn1 w2 2
     OO w2_WW
 w2_head0 w2_add_mul_div w2_div21 w2_to_Z
     w2_to_Z_spec (refl_equal 0)
     w2_WW_spec w2_head0_spec
     w2_add_mul_div_spec w2_div21_spec
     n (word_of_word_tr w2 n x) y H.

Lemma w2_modn1_spec : forall n x y, 0 < [|y|] ->
    [|w2_modn1 n x y|] = (gen_to_Z 2 w2_to_Z n (word_of_word_tr w2 n x)) mod [|y|].
Proof
fun n x y (H:0<[|y|]) =>
  @spec_gen_modn1 w2 2
     OO w2_WW
 w2_head0 w2_add_mul_div w2_div21 w2_to_Z
     w2_to_Z_spec (refl_equal 0)
     w2_WW_spec w2_head0_spec
     w2_add_mul_div_spec w2_div21_spec
     n (word_of_word_tr w2 n x) y H.

