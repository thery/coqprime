From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list4E : ltprime_list4 = lnext 10 3 ltprime_list3.
Proof. now vm_cast_no_check (refl_equal ltprime_list4). Qed.

Compute (4, ltprime_list4, length ltprime_list4).

Lemma ltprime_list4_ltprime i : In i ltprime_list4 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

