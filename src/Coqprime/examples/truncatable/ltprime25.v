From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.

Lemma ltprime_list25E : ltprime_list25 = lnext 10 24 ltprime_list24.
Proof. now vm_cast_no_check (refl_equal ltprime_list25). Qed.

Compute (25, ltprime_list25, length ltprime_list25).

Lemma ltprime_list25_ltprime i : In i ltprime_list25 -> ltprime 10 i.
Proof.
intros H; inversion H.
Qed.

