Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_sub.


Lemma w2_sub_carry_spec : forall x y, [|w2_sub_carry x y|] = ([|x|] - [|y|] - 1) mod w2_B.
Proof
fun x y =>
 match y as y return [|w2_sub_carry x y|] = ([|x|] - [|y|] - 1) mod w2_B with
 | OO =>
    match x as x return [|w2_sub_carry x OO|] = ([|x|] - [|OO|] - 1) mod w2_B with
    | OO => refl_equal 3
    | OI => refl_equal 0
    | IO => refl_equal 1
    | II => refl_equal 2
   end
 | OI =>
    match x as x return [|w2_sub_carry x OI|] = ([|x|] - [|OI|] - 1) mod w2_B with
    | OO => refl_equal 2
    | OI => refl_equal 3
    | IO => refl_equal 0
    | II => refl_equal 1
   end
 | IO =>
    match x as x return [|w2_sub_carry x IO|] = ([|x|] - [|IO|] - 1) mod w2_B with
    | OO => refl_equal 1
    | OI => refl_equal 2
    | IO => refl_equal 3
    | II => refl_equal 0
   end
 | II =>
    match x as x return [|w2_sub_carry x II|] = ([|x|] - [|II|] - 1) mod w2_B with
    | OO => refl_equal 0
    | OI => refl_equal 1
    | IO => refl_equal 2
    | II => refl_equal 3
   end
 end.

