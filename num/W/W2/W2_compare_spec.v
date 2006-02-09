Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Require Import W2_basic_spec.
Open Local Scope w2_scope.
Require Import W2_compare.


Lemma w2_compare_spec : forall x y, match w2_compare x y return Prop with  | Eq => [|x|] = [|y|] | Lt => [|x|] < [|y|] | Gt => [|x|] > [|y|] end.
Proof
.
Admitted.

