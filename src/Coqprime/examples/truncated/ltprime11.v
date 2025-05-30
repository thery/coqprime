From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list11E : ltprime_list11 = lnext 10 10 ltprime_list10.
Proof. now vm_cast_no_check (refl_equal ltprime_list11). Qed.

Compute (11, ltprime_list11, length ltprime_list11).

Lemma ltprime_list11_ltprime i : In i ltprime_list11 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.


