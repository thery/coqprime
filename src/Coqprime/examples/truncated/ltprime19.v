From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list19E : ltprime_list19 = lnext 10 18 ltprime_list18.
Proof. now vm_cast_no_check (refl_equal ltprime_list19). Qed.

Compute (19, ltprime_list19, length ltprime_list19).

Lemma ltprime_list19_ltprime i : In i ltprime_list19 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

