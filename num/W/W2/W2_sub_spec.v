Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_sub.


Lemma w2_sub_spec : forall x y, [|w2_sub x y|] = ([|x|] - [|y|]) mod w2_B.
Proof
.
Admitted.

