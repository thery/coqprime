Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_mul.


Lemma w2_square_c_spec : forall x, [|| w2_square_c x||] = [|x|] * [|x|].
Proof
fun x =>
 match x as x return [|| w2_square_c x||] = [|x|] * [|x|] with
 | OO => refl_equal 0
 | OI => refl_equal 1
 | IO => refl_equal 4
 | II => refl_equal 9
 end.

