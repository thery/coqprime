Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_add.


Lemma w2_add_spec : forall x y, [|w2_add x y|] = ([|x|] + [|y|]) mod w2_B.
Proof
fun x y =>
 match x as x return [|w2_add x y|] = ([|x|] + [|y|]) mod w2_B with
 | OO => 
    match y as y return [|w2_add OO y|] = ([|OO|] + [|y|]) mod w2_B with
    | OO => refl_equal 0
    | OI => refl_equal 1
    | IO => refl_equal 2
    | II => refl_equal 3
    end
 | OI => 
    match y as y return [|w2_add OI y|] = ([|OI|] + [|y|]) mod w2_B with
    | OO => refl_equal 1
    | OI => refl_equal 2
    | IO => refl_equal 3
    | II => refl_equal 0
    end
 | IO => 
    match y as y return [|w2_add IO y|] = ([|IO|] + [|y|]) mod w2_B with
    | OO => refl_equal 2
    | OI => refl_equal 3
    | IO => refl_equal 0
    | II => refl_equal 1
    end
 | II => 
    match y as y return [|w2_add II y|] = ([|II|] + [|y|]) mod w2_B with
    | OO => refl_equal 3
    | OI => refl_equal 0
    | IO => refl_equal 1
    | II => refl_equal 2
    end
 end.

