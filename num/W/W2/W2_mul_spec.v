Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Require Import W2_basic_spec.
Open Local Scope w2_scope.
Require Import W2_mul.


Require Import ZDivModAux.
Require Import W2_mul_c_spec.
Open Local Scope Z_scope.


Lemma w2_mul_spec : forall x y, [|w2_mul x y|] = ([|x|] * [|y|]) mod w2_B.
Proof.
Admitted.

