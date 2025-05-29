
From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list13E : ltprime_list13 = next 10 12 ltprime_list12.
Proof. now vm_cast_no_check (refl_equal ltprime_list13). Qed.

Compute (13, ltprime_list13, length ltprime_list13).

Lemma ltprime_list13_ltprime i : In i ltprime_list13 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.
