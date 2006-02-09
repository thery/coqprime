Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_div.


Lemma Eq_not_Lt : Eq <> Lt.
Admitted.

Lemma Gt_not_Lt : Gt <> Lt.
Admitted.

Lemma w2_div_wB_spec : forall x y, w2_B/2 <= [|y|] -> [|x|] < [|y|] -> match w2_div_wB x y return Prop with (q,r) => [|x|] * w2_B = [|q|]*[|y|] + [|r|] /\ [|r|] < [|y|] end.
Proof
.
Admitted.

Lemma w2_mod_spec : forall x y, 0 < [|y|] -> [|w2_mod x y|] = Zmod [|x|] [|y|].
Proof
.
Admitted.

Lemma w2_mod_gt_spec : forall x y, [|x|] > [|y|] -> 0 < [|y|] -> [|w2_mod x y|] = Zmod [|x|] [|y|].
Proof
.
Admitted.

Lemma w2_div_eq : forall x y, (match w2_div x y return Prop with  (q,r) => ([|q|],[|r|]) = Zdiv_eucl [|x|] [|y|] end).
Admitted.

Require Import Znumtheory.
Require Import Pmod.

Lemma w2_gcd_eq : forall x y, [|w2_gcd x y|] = Zgcd [|x|] [|y|].
Admitted.
Lemma w2_gcd_spec : forall x y, Zis_gcd [|x|] [|y|] [|w2_gcd x y|].
Admitted.

Lemma w2_gcd_gt_spec : forall x y, [|x|] > [|y|] ->Zis_gcd [|x|] [|y|] [|w2_gcd x y|].
Admitted.

Open Scope Z_scope.
Lemma w2_div_spec : forall a b, 0 < [|b|] ->
      let (q,r) := w2_div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\ 
      0 <= [|r|] < [|b|].
Admitted.

Open Scope Z_scope.
Lemma w2_div_gt_spec : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := w2_div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\ 
      0 <= [|r|] < [|b|].
Admitted.

