Require Import ZArith.
Open Local Scope Z_scope.
Require Import W8_basic.
Open Local Scope w8_scope.
Require Import W8_lift.


Require Import W8_head0_spec.
Require Import W8_add_mul_div_1_spec.
Require Import W8_add_mul_div_2_spec.
Require Import W8_add_mul_div_3_spec.
Require Import W8_add_mul_div_4_spec.
Require Import W8_add_mul_div_5_spec.
Require Import W8_add_mul_div_6_spec.
Require Import W8_add_mul_div_7_spec.
Lemma w8_add_mul_div_spec : forall x y p, 0 < Zpos p < Zpos 8 -> [| w8_add_mul_div p x y|] = ([|x|] * (Zpower 2 (Zpos p)) + [|y|] / (Zpower 2 ((Zpos 8) - (Zpos p)))) mod w8_B.
Proof.
 intros x y p H.
 assert (H7:Zpos p <= 7). omega.
 destruct (Zle_lt_or_eq _ _ H7) as [Hlt7|Heq7].
 assert (H6:Zpos p <= 6). omega.
 destruct (Zle_lt_or_eq _ _ H6) as [Hlt6|Heq6].
 assert (H5:Zpos p <= 5). omega.
 destruct (Zle_lt_or_eq _ _ H5) as [Hlt5|Heq5].
 assert (H4:Zpos p <= 4). omega.
 destruct (Zle_lt_or_eq _ _ H4) as [Hlt4|Heq4].
 assert (H3:Zpos p <= 3). omega.
 destruct (Zle_lt_or_eq _ _ H3) as [Hlt3|Heq3].
 assert (H2:Zpos p <= 2). omega.
 destruct (Zle_lt_or_eq _ _ H2) as [Hlt2|Heq2].
 assert (H1:Zpos p <= 1). omega.
 destruct (Zle_lt_or_eq _ _ H1) as [Hlt1|Heq1].
 elimtype False;omega.
 inversion Heq1.
 exact (w8_add_mul_div1_spec x y).
 inversion Heq2.
 exact (w8_add_mul_div2_spec x y).
 inversion Heq3.
 exact (w8_add_mul_div3_spec x y).
 inversion Heq4.
 exact (w8_add_mul_div4_spec x y).
 inversion Heq5.
 exact (w8_add_mul_div5_spec x y).
 inversion Heq6.
 exact (w8_add_mul_div6_spec x y).
 inversion Heq7.
 exact (w8_add_mul_div7_spec x y).
Qed.

