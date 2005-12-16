Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_lift.


Lemma w2_add_mul_div1_spec : forall x y, [| w2_add_mul_div1 x y|] = ([|x|] * (Zpower 2 (Zpos 1)) + [|y|] / (Zpower 2 ((Zpos 2) - (Zpos 1)))) mod w2_B.
Proof
fun x y =>
 match x as x return [| w2_add_mul_div1 x y|] = ([|x|] * (Zpower 2 (Zpos 1)) + [|y|] / (Zpower 2 ((Zpos 2) - (Zpos 1)))) mod w2_B with
 | OO =>
    match y as y return [| w2_add_mul_div1 OO y|] = ([|OO|] * (Zpower 2 (Zpos 1)) + [|y|] / (Zpower 2 ((Zpos 2) - (Zpos 1)))) mod w2_B with
    | OO => refl_equal 0
    | OI => refl_equal 0
    | IO => refl_equal 1
    | II => refl_equal 1
    end
 | OI =>
    match y as y return [| w2_add_mul_div1 OI y|] = ([|OI|] * (Zpower 2 (Zpos 1)) + [|y|] / (Zpower 2 ((Zpos 2) - (Zpos 1)))) mod w2_B with
    | OO => refl_equal 2
    | OI => refl_equal 2
    | IO => refl_equal 3
    | II => refl_equal 3
    end
 | IO =>
    match y as y return [| w2_add_mul_div1 IO y|] = ([|IO|] * (Zpower 2 (Zpos 1)) + [|y|] / (Zpower 2 ((Zpos 2) - (Zpos 1)))) mod w2_B with
    | OO => refl_equal 0
    | OI => refl_equal 0
    | IO => refl_equal 1
    | II => refl_equal 1
    end
 | II =>
    match y as y return [| w2_add_mul_div1 II y|] = ([|II|] * (Zpower 2 (Zpos 1)) + [|y|] / (Zpower 2 ((Zpos 2) - (Zpos 1)))) mod w2_B with
    | OO => refl_equal 2
    | OI => refl_equal 2
    | IO => refl_equal 3
    | II => refl_equal 3
    end
 end.

