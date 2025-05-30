From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list8E : ltprime_list8 = lnext 10 7 ltprime_list7.
Proof. now vm_cast_no_check (refl_equal ltprime_list8). Qed.

Compute (8, ltprime_list8, length ltprime_list8).

Lemma ltprime_list8_ltprime i : In i ltprime_list8 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

