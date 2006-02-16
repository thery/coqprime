Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_sub.


Lemma w2_sub_c_spec : forall x y, [-|w2_sub_c x y|] = [|x|] - [|y|].
Proof
fun x y =>
 match y as y return [-|w2_sub_c x y|] = [|x|] - [|y|] with
 | OO =>
    match x as x return [-|w2_sub_c x OO|] = [|x|] - [|OO|] with
    | OO => refl_equal (0)
    | OI => refl_equal (1)
    | IO => refl_equal (2)
    | II => refl_equal (3)
   end
 | OI =>
    match x as x return [-|w2_sub_c x OI|] = [|x|] - [|OI|] with
    | OO => refl_equal (-1)
    | OI => refl_equal (0)
    | IO => refl_equal (1)
    | II => refl_equal (2)
   end
 | IO =>
    match x as x return [-|w2_sub_c x IO|] = [|x|] - [|IO|] with
    | OO => refl_equal (-2)
    | OI => refl_equal (-1)
    | IO => refl_equal (0)
    | II => refl_equal (1)
   end
 | II =>
    match x as x return [-|w2_sub_c x II|] = [|x|] - [|II|] with
    | OO => refl_equal (-3)
    | OI => refl_equal (-2)
    | IO => refl_equal (-1)
    | II => refl_equal (0)
   end
 end.

