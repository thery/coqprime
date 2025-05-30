From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list5E : ltprime_list5 = lnext 10 4 ltprime_list4.
Proof. now vm_cast_no_check (refl_equal ltprime_list5). Qed.

Compute (5, ltprime_list5, length ltprime_list5).

Lemma ltprime_list5_ltprime i : In i ltprime_list5 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

