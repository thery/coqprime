From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list7E : ltprime_list7 = lnext 10 6 ltprime_list6.
Proof. now vm_cast_no_check (refl_equal ltprime_list7). Qed.

Compute (7, ltprime_list7, length ltprime_list7).

Lemma ltprime_list7_ltprime i : In i ltprime_list7 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

