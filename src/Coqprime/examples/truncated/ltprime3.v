From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list3E : ltprime_list3 = lnext 10 2 ltprime_list2.
Proof. now vm_cast_no_check (refl_equal ltprime_list3). Qed.

Compute (3, ltprime_list3, length ltprime_list3).

Lemma ltprime_list3_ltprime i : In i ltprime_list3 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

