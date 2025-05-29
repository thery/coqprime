From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list10E : ltprime_list10 = next 10 9 ltprime_list9.
Proof. now vm_cast_no_check (refl_equal ltprime_list10). Qed.

Compute (10, ltprime_list10, length ltprime_list10).

Lemma ltprime_list10_ltprime i : In i ltprime_list10 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

