Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_add.


Lemma w2_add_spec : forall x y, [|w2_add x y|] = ([|x|] + [|y|]) mod w2_B.
Proof
.
Admitted.

