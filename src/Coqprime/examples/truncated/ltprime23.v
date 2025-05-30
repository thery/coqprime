From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list23E : ltprime_list23 = lnext 10 22 ltprime_list22.
Proof. now vm_cast_no_check (refl_equal ltprime_list23). Qed.

Compute (23, ltprime_list23, length ltprime_list23).

Lemma ltprime_list23_ltprime i : In i ltprime_list23 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

