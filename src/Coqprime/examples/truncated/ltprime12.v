From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list12E : ltprime_list12 = next 10 11 ltprime_list11.
Proof. now vm_cast_no_check (refl_equal ltprime_list12). Qed.

Compute (12, ltprime_list12, length ltprime_list12).

Lemma ltprime_list12_ltprime i : In i ltprime_list12 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

