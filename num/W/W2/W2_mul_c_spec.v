Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_mul.


Lemma w2_mul_c_spec : forall x y, [||w2_mul_c x y||] = [|x|] * [|y|].
Proof
fun x y =>
 match x as x return [||w2_mul_c x y||] = [|x|] * [|y|] with
 | OO => refl_equal 0
 | OI =>
    match y as y return [||w2_mul_c OI y||] = [|OI|] * [|y|] with
    | OO => refl_equal 0
    | OI => refl_equal 1
    | IO => refl_equal 2
    | II => refl_equal 3
    end
 | IO =>
    match y as y return [||w2_mul_c IO y||] = [|IO|] * [|y|] with
    | OO => refl_equal 0
    | OI => refl_equal 2
    | IO => refl_equal 4
    | II => refl_equal 6
    end
 | II =>
    match y as y return [||w2_mul_c II y||] = [|II|] * [|y|] with
    | OO => refl_equal 0
    | OI => refl_equal 3
    | IO => refl_equal 6
    | II => refl_equal 9
    end
 end.

