From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list9E : ltprime_list9 = lnext 10 8 ltprime_list8.
Proof. now vm_cast_no_check (refl_equal ltprime_list9). Qed.

Compute (9, ltprime_list9, length ltprime_list9).

Lemma ltprime_list9_ltprime i : In i ltprime_list9 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

