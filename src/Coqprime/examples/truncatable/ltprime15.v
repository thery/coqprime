From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list15E : ltprime_list15 = lnext 10 14 ltprime_list14.
Proof. now vm_cast_no_check (refl_equal ltprime_list15). Qed.

Compute (15, ltprime_list15, length ltprime_list15).

Lemma ltprime_list15_ltprime i : In i ltprime_list15 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

