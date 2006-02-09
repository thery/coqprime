Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_mul.


Lemma w2_square_c_spec : forall x, [|| w2_square_c x||] = [|x|] * [|x|].
Proof
.
Admitted.

