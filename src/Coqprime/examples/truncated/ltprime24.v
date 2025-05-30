From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Lemma ltprime_list24E : ltprime_list24 = lnext 10 23 ltprime_list23.
Proof. now vm_cast_no_check (refl_equal ltprime_list24). Qed.

Compute (24, ltprime_list24, length ltprime_list24).

Lemma ltprime_list24_ltprime i : In i ltprime_list24 -> ltprime 10 i.
Proof.
intros H; 
repeat (inversion_clear H as [|H1];
 [now subst; ltprime_tac 10| rename H1 into H]).
inversion H.
Qed.

