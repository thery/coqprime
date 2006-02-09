Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_sub.


Lemma w2_pred_c_spec : forall x,  [-|w2_pred_c x|] = [|x|] - 1.
Proof
.
Admitted.

Lemma w2_pred_spec : forall x,  [|w2_pred x|] = ([|x|] - 1) mod w2_B.
Proof
.
Admitted.

