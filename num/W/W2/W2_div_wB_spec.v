Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_div.


Lemma Eq_not_Lt : Eq <> Lt.
Proof. intro H;discriminate H. Qed.

Lemma Gt_not_Lt : Gt <> Lt.
Proof. intro H;discriminate H. Qed.

Lemma w2_div_wB_spec : forall x y, w2_B/2 <= [|y|] -> [|x|] < [|y|] -> match w2_div_wB x y return Prop with (q,r) => [|x|] * w2_B = [|q|]*[|y|] + [|r|] /\ [|r|] < [|y|] end.
Proof
fun x y =>
 match y as y return w2_B/2 <= [|y|] -> [|x|] < [|y|] -> match w2_div_wB x y return Prop with (q,r) => [|x|] * w2_B = [|q|]*[|y|] + [|r|] /\ [|r|] < [|y|] end with
 | OO =>
   fun (H:w2_B/2 <= [|OO|]) => 
     False_ind
       ([|x|] < [|OO|] -> match w2_div_wB x OO return Prop with (q,r) => [|x|] * w2_B = [|q|]*[|OO|] + [|r|] /\ [|r|] < [|OO|] end)
       (H (refl_equal Gt))
 | OI =>
   fun (H:w2_B/2 <= [|OI|]) => 
     False_ind
       ([|x|] < [|OI|] -> match w2_div_wB x OI return Prop with (q,r) => [|x|] * w2_B = [|q|]*[|OI|] + [|r|] /\ [|r|] < [|OI|] end)
       (H (refl_equal Gt))
 | IO =>
   fun (H1:w2_B/2 <= [|IO|]) => 
     match x as x return [|x|] < [|IO|] -> match w2_div_wB x IO return Prop with (q,r) => [|x|] * w2_B = [|q|]*[|IO|] + [|r|] /\ [|r|] < [|IO|] end with
     | OO =>
       fun (H2:[|OO|] < [|IO|]) =>
         conj (refl_equal 0) (refl_equal Lt)
     | OI =>
       fun (H2:[|OI|] < [|IO|]) =>
         conj (refl_equal 4) (refl_equal Lt)
     | IO =>
       fun (H2:[|IO|] < [|IO|]) =>
       False_ind
          (match w2_div_wB IO IO return Prop with (q,r) => [|IO|] * w2_B = [|q|]*[|IO|] + [|r|] /\ [|r|] < [|IO|] end)
        (Eq_not_Lt H2)
     | II =>
       fun (H2:[|II|] < [|IO|]) =>
       False_ind
          (match w2_div_wB II IO return Prop with (q,r) => [|II|] * w2_B = [|q|]*[|IO|] + [|r|] /\ [|r|] < [|IO|] end)
        (Gt_not_Lt H2)
     end
 | II =>
   fun (H1:w2_B/2 <= [|II|]) => 
     match x as x return [|x|] < [|II|] -> match w2_div_wB x II return Prop with (q,r) => [|x|] * w2_B = [|q|]*[|II|] + [|r|] /\ [|r|] < [|II|] end with
     | OO =>
       fun (H2:[|OO|] < [|II|]) =>
         conj (refl_equal 0) (refl_equal Lt)
     | OI =>
       fun (H2:[|OI|] < [|II|]) =>
         conj (refl_equal 4) (refl_equal Lt)
     | IO =>
       fun (H2:[|IO|] < [|II|]) =>
         conj (refl_equal 8) (refl_equal Lt)
     | II =>
       fun (H2:[|II|] < [|II|]) =>
       False_ind
          (match w2_div_wB II II return Prop with (q,r) => [|II|] * w2_B = [|q|]*[|II|] + [|r|] /\ [|r|] < [|II|] end)
        (Eq_not_Lt H2)
     end
 end.

Lemma w2_mod_spec : forall x y, 0 < [|y|] -> [|w2_mod x y|] = Zmod [|x|] [|y|].
Proof
fun x y (H:0<[|y|]) =>
 match y as y return [|w2_mod x y|] = Zmod [|x|] [|y|] with
 | OO => 
    match x as x return [|w2_mod x OO|] = Zmod [|x|] [|OO|] with
   | OO => refl_equal 0
   | OI => refl_equal 0
   | IO => refl_equal 0
   | II => refl_equal 0
   end
 | OI => 
    match x as x return [|w2_mod x OI|] = Zmod [|x|] [|OI|] with
   | OO => refl_equal 0
   | OI => refl_equal 0
   | IO => refl_equal 0
   | II => refl_equal 0
   end
 | IO => 
    match x as x return [|w2_mod x IO|] = Zmod [|x|] [|IO|] with
   | OO => refl_equal 0
   | OI => refl_equal 1
   | IO => refl_equal 0
   | II => refl_equal 1
   end
 | II => 
    match x as x return [|w2_mod x II|] = Zmod [|x|] [|II|] with
   | OO => refl_equal 0
   | OI => refl_equal 1
   | IO => refl_equal 2
   | II => refl_equal 0
   end
 end.

Lemma w2_mod_gt_spec : forall x y, [|x|] > [|y|] -> 0 < [|y|] -> [|w2_mod x y|] = Zmod [|x|] [|y|].
Proof
fun x y (H1:[|x|] > [|y|]) (H2:0<[|y|]) =>
w2_mod_spec x y H2.

Lemma w2_div_eq : forall x y, (match w2_div x y return Prop with  (q,r) => ([|q|],[|r|]) = Zdiv_eucl [|x|] [|y|] end).
Proof fun x y =>
 match y as y return (match w2_div x y return Prop with  (q,r) => ([|q|],[|r|]) = Zdiv_eucl [|x|] [|y|] end) with
 | OO => 
    match x as x return (match w2_div x OO return Prop with  (q,r) => ([|q|],[|r|]) = Zdiv_eucl [|x|] [|OO|] end) with
   | OO => refl_equal (0, 0)
   | OI => refl_equal (0, 0)
   | IO => refl_equal (0, 0)
   | II => refl_equal (0, 0)
   end
 | OI => 
    match x as x return (match w2_div x OI return Prop with  (q,r) => ([|q|],[|r|]) = Zdiv_eucl [|x|] [|OI|] end) with
   | OO => refl_equal (0, 0)
   | OI => refl_equal (1, 0)
   | IO => refl_equal (2, 0)
   | II => refl_equal (3, 0)
   end
 | IO => 
    match x as x return (match w2_div x IO return Prop with  (q,r) => ([|q|],[|r|]) = Zdiv_eucl [|x|] [|IO|] end) with
   | OO => refl_equal (0, 0)
   | OI => refl_equal (0, 1)
   | IO => refl_equal (1, 0)
   | II => refl_equal (1, 1)
   end
 | II => 
    match x as x return (match w2_div x II return Prop with  (q,r) => ([|q|],[|r|]) = Zdiv_eucl [|x|] [|II|] end) with
   | OO => refl_equal (0, 0)
   | OI => refl_equal (0, 1)
   | IO => refl_equal (0, 2)
   | II => refl_equal (1, 0)
   end
 end.

Require Import Znumtheory.
Require Import Pmod.

Lemma w2_gcd_eq : forall x y, [|w2_gcd x y|] = Zgcd [|x|] [|y|].
Proof fun x y =>
 match x as x return [|w2_gcd x y|] = Zgcd [|x|] [|y|] with
 | OO =>
    match y as y return [|w2_gcd OO y|] = Zgcd [|OO|] [|y|] with
    | OO => refl_equal 0
    | OI => refl_equal 1
    | IO => refl_equal 2
    | II => refl_equal 3
    end
 | OI =>
    match y as y return [|w2_gcd OI y|] = Zgcd [|OI|] [|y|] with
    | OO => refl_equal 1
    | OI => refl_equal 1
    | IO => refl_equal 1
    | II => refl_equal 1
    end
 | IO =>
    match y as y return [|w2_gcd IO y|] = Zgcd [|IO|] [|y|] with
    | OO => refl_equal 2
    | OI => refl_equal 1
    | IO => refl_equal 2
    | II => refl_equal 1
    end
 | II =>
    match y as y return [|w2_gcd II y|] = Zgcd [|II|] [|y|] with
    | OO => refl_equal 3
    | OI => refl_equal 1
    | IO => refl_equal 1
    | II => refl_equal 3
    end
 end.
Lemma w2_gcd_spec : forall x y, Zis_gcd [|x|] [|y|] [|w2_gcd x y|].
Proof.
 intros x y; rewrite (w2_gcd_eq x y).
 apply Zgcd_is_gcd.
Qed.

Lemma w2_gcd_gt_spec : forall x y, [|x|] > [|y|] ->Zis_gcd [|x|] [|y|] [|w2_gcd x y|].
Proof.
 intros x y H; apply w2_gcd_spec.
Qed.

Open Scope Z_scope.
Lemma w2_div_spec : forall a b, 0 < [|b|] ->
      let (q,r) := w2_div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\ 
      0 <= [|r|] < [|b|].
Proof.
 intros a b Hpos;assert (Heq := w2_div_eq a b).
 assert (Hde := Z_div_mod [|a|] [|b|] (Zlt_gt _ _ Hpos)).
 destruct (w2_div a b).
 destruct (Zdiv_eucl [|a|] [|b|]).
 inversion Heq;subst;rewrite Zmult_comm;trivial.
Qed.

Open Scope Z_scope.
Lemma w2_div_gt_spec : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := w2_div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\ 
      0 <= [|r|] < [|b|].
Proof.
 intros a b Hgt Hpos;exact (w2_div_spec a b Hpos).
Qed.

