From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list17E : ltprime_list17 = next 10 16 ltprime_list16.
Proof. now vm_cast_no_check (refl_equal ltprime_list17). Qed.

Compute (17, ltprime_list17, length ltprime_list17).

Lemma ltprime_list17_ltprime i : In i ltprime_list17 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

