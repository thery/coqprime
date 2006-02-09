Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_add.


Lemma w2_succ_c_spec : forall x, [+|w2_succ_c x|] = [|x|] + 1.
Proof
.
Admitted.

Lemma w2_succ_spec : forall x, [|w2_succ x|] = ([|x|] + 1) mod w2_B.
Proof
.
Admitted.

Lemma w2_carry_succ_c_spec : forall c, [+|c|] <= w2_B + (w2_B - 2) -> [+|w2_carry_succ_c c|] = [+|c|] + 1.
Proof
.
Admitted.

