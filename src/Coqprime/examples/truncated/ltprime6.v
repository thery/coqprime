From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list6E : ltprime_list6 = next 10 5 ltprime_list5.
Proof. now vm_cast_no_check (refl_equal ltprime_list6). Qed.

Compute (6, ltprime_list6, length ltprime_list6).

Lemma ltprime_list6_ltprime i : In i ltprime_list6 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

