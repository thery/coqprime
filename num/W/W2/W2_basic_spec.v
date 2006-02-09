Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Proof that the basic functions are correct ** *)

Lemma w2_to_Z_spec : forall x, 0 <= [|x|] < w2_B.
Proof
.
Admitted.

Lemma w2_of_pos_spec : forall p, Zpos p = (Z_of_N (fst (w2_of_pos p)))*w2_B + [|snd (w2_of_pos p)|].
Proof
.
Admitted.

Lemma w2_0_spec : [|OO|] = 0.
Proof
.
Admitted.

Lemma w2_1_spec : [|OI|] = 1.
Proof
.
Admitted.

Lemma w2_Bm1_spec : [|II|] = w2_B - 1.
Proof
.
Admitted.

Lemma w2_WW_spec : forall h l, [||w2_WW h l||] = [|h|] * w2_B + [|l|].
Proof
.
Admitted.

Lemma w2_CW_spec : forall sign c l, interp_carry sign (w2_B*w2_B) (zn2z_to_Z w2_B w2_to_Z) (w2_CW c l) = (interp_carry sign w2_B w2_to_Z c)*w2_B + [|l|].
Proof.
Admitted.

