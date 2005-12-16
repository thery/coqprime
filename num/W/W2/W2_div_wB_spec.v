Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_div.


Lemma w2_div_wB_spec : forall x y, w2_B/2 <= [|y|] -> match w2_div_wB x y return Prop with (q,r) => [|x|] * w2_B = [+|q|]*[|y|] + [|r|] /\ [|r|] < [|y|] end.
Proof
fun x y =>
 match y as y return w2_B/2 <= [|y|] -> match w2_div_wB x y return Prop with (q,r) => [|x|] * w2_B = [+|q|]*[|y|] + [|r|] /\ [|r|] < [|y|] end with
 | OO =>
   fun (H:w2_B/2 <= [|OO|]) => 
     False_ind
       (match w2_div_wB x OO return Prop with (q,r) => [|x|] * w2_B = [+|q|]*[|OO|] + [|r|] /\ [|r|] < [|OO|] end)
       (H (refl_equal Gt))
 | OI =>
   fun (H:w2_B/2 <= [|OI|]) => 
     False_ind
       (match w2_div_wB x OI return Prop with (q,r) => [|x|] * w2_B = [+|q|]*[|OI|] + [|r|] /\ [|r|] < [|OI|] end)
       (H (refl_equal Gt))
 | IO =>
   fun (H:w2_B/2 <= [|IO|]) => 
     match x as x return match w2_div_wB x IO return Prop with (q,r) => [|x|] * w2_B = [+|q|]*[|IO|] + [|r|] /\ [|r|] < [|IO|] end with
     | OO => conj (refl_equal 0) (refl_equal Lt)
     | OI => conj (refl_equal 4) (refl_equal Lt)
     | IO => conj (refl_equal 8) (refl_equal Lt)
     | II => conj (refl_equal 12) (refl_equal Lt)
     end
 | II =>
   fun (H:w2_B/2 <= [|II|]) => 
     match x as x return match w2_div_wB x II return Prop with (q,r) => [|x|] * w2_B = [+|q|]*[|II|] + [|r|] /\ [|r|] < [|II|] end with
     | OO => conj (refl_equal 0) (refl_equal Lt)
     | OI => conj (refl_equal 4) (refl_equal Lt)
     | IO => conj (refl_equal 8) (refl_equal Lt)
     | II => conj (refl_equal 12) (refl_equal Lt)
     end
 end.

