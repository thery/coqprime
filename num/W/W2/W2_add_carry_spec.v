Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_add.


Lemma w2_add_carry_spec : forall x y, [|w2_add_carry x y|] = ([|x|] + [|y|] + 1) mod w2_B.
Proof
fun x y =>
 match x as x return [|w2_add_carry x y|] = ([|x|] + [|y|] + 1) mod w2_B with
 | OO => 
    match y as y return [|w2_add_carry OO y|] = ([|OO|] + [|y|] + 1) mod w2_B with
    | OO => refl_equal 1
    | OI => refl_equal 2
    | IO => refl_equal 3
    | II => refl_equal 0
    end
 | OI => 
    match y as y return [|w2_add_carry OI y|] = ([|OI|] + [|y|] + 1) mod w2_B with
    | OO => refl_equal 2
    | OI => refl_equal 3
    | IO => refl_equal 0
    | II => refl_equal 1
    end
 | IO => 
    match y as y return [|w2_add_carry IO y|] = ([|IO|] + [|y|] + 1) mod w2_B with
    | OO => refl_equal 3
    | OI => refl_equal 0
    | IO => refl_equal 1
    | II => refl_equal 2
    end
 | II => 
    match y as y return [|w2_add_carry II y|] = ([|II|] + [|y|] + 1) mod w2_B with
    | OO => refl_equal 0
    | OI => refl_equal 1
    | IO => refl_equal 2
    | II => refl_equal 3
    end
 end.

