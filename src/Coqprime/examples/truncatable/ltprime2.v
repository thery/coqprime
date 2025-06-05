From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list2E : ltprime_list2 = lnext 10 1 ltprime_list1.
Proof. now vm_cast_no_check (refl_equal ltprime_list2). Qed.

Compute (2, ltprime_list2, length ltprime_list2).

Lemma ltprime_list2_ltprime i : In i ltprime_list2 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.
