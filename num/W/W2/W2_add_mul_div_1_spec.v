Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_lift.


Lemma w2_add_mul_div1_spec : forall x y, [| w2_add_mul_div1 x y|] = ([|x|] * (Zpower 2 (Zpos 1)) + [|y|] / (Zpower 2 ((Zpos 2) - (Zpos 1)))) mod w2_B.
Proof
.
Admitted.

