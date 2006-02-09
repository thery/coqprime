Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_add.


Lemma w2_add_carry_spec : forall x y, [|w2_add_carry x y|] = ([|x|] + [|y|] + 1) mod w2_B.
Proof
.
Admitted.

