Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_sub.


Lemma w2_pred_c_spec : forall x,  [-|w2_pred_c x|] = [|x|] - 1.
Proof
fun x =>
 match x as x return  [-|w2_pred_c x|] = [|x|] - 1 with
 | OO => refl_equal (-1)
 | OI => refl_equal (0)
 | IO => refl_equal (1)
 | II => refl_equal (2)
 end.

