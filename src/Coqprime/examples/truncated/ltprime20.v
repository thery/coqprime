From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list20E : ltprime_list20 = next 10 19 ltprime_list19.
Proof. now vm_cast_no_check (refl_equal ltprime_list20). Qed.

Compute (20, ltprime_list20, length ltprime_list20).

Lemma ltprime_list20_ltprime i : In i ltprime_list20 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

