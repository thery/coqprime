Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Require Import W2_basic_spec.
Open Local Scope w2_scope.
Require Import W2_opp.


Lemma w2_opp_c_spec : forall x, [-|w2_opp_c x|] = -[|x|].
Proof
.
Admitted.

Lemma w2_opp_spec : forall x, [|w2_opp x|] = (-[|x|]) mod w2_B.
Proof
.
Admitted.

Lemma w2_opp_carry_spec : forall x, [|w2_opp_carry x|] = w2_B - [|x|] - 1.
Proof
.
Admitted.

