From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list21E : ltprime_list21 = next 10 20 ltprime_list20.
Proof. now vm_cast_no_check (refl_equal ltprime_list21). Qed.

Compute (21, ltprime_list21, length ltprime_list21).

Lemma ltprime_list21_ltprime i : In i ltprime_list21 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

