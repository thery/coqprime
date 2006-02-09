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
Admitted.

Lemma w2_divn1_spec : forall n x y, 0<[|y|] ->
    let (q,r) := w2_divn1 n x y in
    gen_to_Z 2 w2_to_Z n (word_of_word_tr w2 n x) =
      gen_to_Z 2 w2_to_Z n q * w2_to_Z y + w2_to_Z r /\ 
    0 <= [|r|] < [|y|].
Proof
.
Admitted.

Lemma w2_modn1_spec : forall n x y, 0 < [|y|] ->
    [|w2_modn1 n x y|] = (gen_to_Z 2 w2_to_Z n (word_of_word_tr w2 n x)) mod [|y|].
Proof
.
Admitted.

