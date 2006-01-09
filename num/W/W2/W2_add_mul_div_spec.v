Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_lift.


Require Import W2_head0_spec.
Require Import W2_add_mul_div_1_spec.
Lemma w2_add_mul_div_spec : forall x y p, 0 < Zpos p < Zpos 2 -> [| w2_add_mul_div p x y|] = ([|x|] * (Zpower 2 (Zpos p)) + [|y|] / (Zpower 2 ((Zpos 2) - (Zpos p)))) mod w2_B.
Proof.
 intros x y p H.
 assert (H1:Zpos p <= 1). omega.
 destruct (Zle_lt_or_eq _ _ H1) as [Hlt1|Heq1].
 elimtype False;omega.
 inversion Heq1.
 exact (w2_add_mul_div1_spec x y).
Qed.

