From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list16E : ltprime_list16 = lnext 10 15 ltprime_list15.
Proof. now vm_cast_no_check (refl_equal ltprime_list16). Qed.

Compute (16, ltprime_list16, length ltprime_list16).

Lemma ltprime_list16_ltprime i : In i ltprime_list16 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

