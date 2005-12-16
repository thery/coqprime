Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Require Import W2_basic_spec.
Open Local Scope w2_scope.
Require Import W2_opp.


Lemma w2_opp_c_spec : forall x, [-|w2_opp_c x|] = -[|x|].
Proof
fun x =>
 match x as x return [-|w2_opp_c x|] = -[|x|] with
 | OO => refl_equal (-0)
 | OI => refl_equal (-1)
 | IO => refl_equal (-2)
 | II => refl_equal (-3)
 end.

Lemma w2_opp_carry_spec : forall x, [|w2_opp_carry x|] = w2_B - [|x|] - 1.
Proof
fun x =>
 match x as x return [|w2_opp_carry x|] = w2_B - [|x|] - 1 with
 | OO => refl_equal 3
 | OI => refl_equal 2
 | IO => refl_equal 1
 | II => refl_equal 0
 end.

