From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list22E : ltprime_list22 = lnext 10 21 ltprime_list21.
Proof. now vm_cast_no_check (refl_equal ltprime_list22). Qed.

Compute (22, ltprime_list22, length ltprime_list22).

Lemma ltprime_list22_ltprime i : In i ltprime_list22 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

