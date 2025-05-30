From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list14E : ltprime_list14 = lnext 10 13 ltprime_list13.
Proof. now vm_cast_no_check (refl_equal ltprime_list14). Qed.

Compute (14, ltprime_list14, length ltprime_list14).

Lemma ltprime_list14_ltprime i : In i ltprime_list14 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.


