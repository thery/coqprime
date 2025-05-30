From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list18E : ltprime_list18 = lnext 10 17 ltprime_list17.
Proof. now vm_cast_no_check (refl_equal ltprime_list18). Qed.

Compute (18, ltprime_list18, length ltprime_list18).

Lemma ltprime_list18_ltprime i : In i ltprime_list18 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

