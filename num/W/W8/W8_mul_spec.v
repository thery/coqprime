Require Import ZArith.
Open Local Scope Z_scope.
Require Import W8_basic.
Require Import W8_basic_spec.
Open Local Scope w8_scope.
Require Import W8_mul.


Require Import ZDivModAux.
Require Import W8_mul_c_spec.
Open Local Scope Z_scope.


Lemma w8_mul_spec : forall x y, [|w8_mul x y|] = ([|x|] * [|y|]) mod w8_B.
Proof.
 assert (H1: 0 < w8_B). exact (refl_equal Lt).
 assert (H2: w8_B > 0). exact (refl_equal Gt).
 unfold w8_mul;intros x y.
 assert (H := w8_mul_c_spec x y); destruct (w8_mul_c x y).
 rewrite <- H; reflexivity.
 rewrite <- H; simpl.
 rewrite Zmod_plus;trivial.
 rewrite Zmod_mult;trivial.
 rewrite Z_mod_same;trivial.
 rewrite Zmult_0_r; rewrite (Zmod_def_small 0).
 simpl; rewrite Zmod_mod;trivial.
 rewrite Zmod_def_small;trivial.
 apply w8_to_Z_spec.
 split;[intro Heq;discriminate Heq | exact (refl_equal Lt)].
Qed.

