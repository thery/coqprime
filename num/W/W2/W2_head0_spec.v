Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_lift.


Lemma Eq_not_Gt : Eq <> Gt.
Admitted.

Lemma Lt_not_Gt : Lt <> Gt.
Admitted.

Lemma w2_head0_spec : forall x, 0 < [|x|] -> w2_B/ 2 <= 2 ^ (Z_of_N (w2_head0 x)) * [|x|] < w2_B.
Proof
.
Admitted.

