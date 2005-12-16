Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_lift.


Lemma Eq_not_Gt : Eq <> Gt.
Proof. intro H;discriminate H. Qed.

Lemma Eq_not_Lt : Eq <> Lt.
Proof. intro H;discriminate H. Qed.

Lemma Lt_not_Gt : Lt <> Gt.
Proof. intro H;discriminate H. Qed.

Lemma Gt_not_Lt : Gt <> Lt.
Proof. intro H;discriminate H. Qed.

Lemma w2_head0_spec : forall x, 0 < [|x|] -> w2_B/ 2 <= 2 ^ (Z_of_N (w2_head0 x)) * [|x|] < w2_B.
Proof
fun x =>
 match x as x return 0 < [|x|] -> w2_B/ 2 <= 2 ^ (Z_of_N (w2_head0 x)) * [|x|] < w2_B with
 | OO =>    fun (H:0 < [|OO|]) =>
    eq_ind Eq
      (fun ee : comparison =>
       match ee with
       | Eq => True
       | Lt => w2_B/ 2 <= 2 ^ (Z_of_N (w2_head0 OO)) * [|OO|] < w2_B
       | Gt => False
       end) I Lt H
 | OI =>    fun (H:0 < [|OI|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | IO =>    fun (H:0 < [|IO|]) => 
     conj (Eq_not_Gt) (refl_equal Lt)
 | II =>    fun (H:0 < [|II|]) => 
     conj (Lt_not_Gt) (refl_equal Lt)
 end.

