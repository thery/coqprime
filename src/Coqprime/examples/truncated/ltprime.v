From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_lprime ltprime_init.
From Coqprime Require Import ltprime1 ltprime2 ltprime3 ltprime4 ltprime5.
From Coqprime Require Import ltprime6 ltprime7 ltprime8 ltprime9 ltprime10.
From Coqprime Require Import ltprime11 ltprime12 ltprime13 ltprime14 ltprime15.
From Coqprime Require Import ltprime16 ltprime17 ltprime18 ltprime19 ltprime20.
From Coqprime Require Import ltprime21 ltprime22 ltprime23 ltprime24 ltprime25.

Lemma ltprime_list1_correct k :
  ltprime 10 k -> 1 <= k < 10 -> In k ltprime_list1.
Proof.
intros kLT kB.
assert (kPr : prime k) by now apply (ltprime_prime 10).
assert (H : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/
        k = 7 \/ k = 8 \/ k = 9) by lia.
unfold ltprime_list1.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; subst k; auto with datatypes.
- now assert (2 <= 1); [apply prime_ge_2|lia].
- case (prime_divisors _ kPr 2); try lia.
  exists 2; lia.
- case (prime_divisors _ kPr 2); try lia.
  exists 3; lia.
- case (prime_divisors _ kPr 2); try lia.
  exists 4; lia.
- case (prime_divisors _ kPr 3); try lia.
  exists 3; lia.
Qed.

Lemma ltprime_list2_correct k :
  ltprime 10 k -> 10 <= k < 100 -> In k ltprime_list2.
Proof.
intros kLT kB.
rewrite ltprime_list2E.
apply (lnext_correct 10 (refl_equal _) 0); try lia; auto.
exact ltprime_list1_correct.
Qed.

Lemma ltprime_list3_correct k :
  ltprime 10 k -> 10 ^ 2 <= k < 10 ^ 3 -> In k ltprime_list3.
Proof.
intros kLT kB.
rewrite ltprime_list3E.
apply (lnext_correct 10 (refl_equal _) 1); try lia; auto.
exact ltprime_list2_correct.
Qed.

Lemma ltprime_list4_correct k :
  ltprime 10 k -> 10 ^ 3 <= k < 10 ^ 4 -> In k ltprime_list4.
Proof.
intros kLT kB.
rewrite ltprime_list4E.
apply (lnext_correct 10 (refl_equal _) 2); try lia; auto.
exact ltprime_list3_correct.
Qed.

Lemma ltprime_list5_correct k :
  ltprime 10 k -> 10 ^ 4 <= k < 10 ^ 5 -> In k ltprime_list5.
Proof.
intros kLT kB.
rewrite ltprime_list5E.
apply (lnext_correct 10 (refl_equal _) 3); try lia; auto.
exact ltprime_list4_correct.
Qed.

Lemma ltprime_list6_correct k :
  ltprime 10 k -> 10 ^ 5 <= k < 10 ^ 6 -> In k ltprime_list6.
Proof.
intros kLT kB.
rewrite ltprime_list6E.
apply (lnext_correct 10 (refl_equal _) 4); try lia; auto.
exact ltprime_list5_correct.
Qed.

Lemma ltprime_list7_correct k :
  ltprime 10 k -> 10 ^ 6 <= k < 10 ^ 7 -> In k ltprime_list7.
Proof.
intros kLT kB.
rewrite ltprime_list7E.
apply (lnext_correct 10 (refl_equal _) 5); try lia; auto.
exact ltprime_list6_correct.
Qed.

Lemma ltprime_list8_correct k :
  ltprime 10 k -> 10 ^ 7 <= k < 10 ^ 8 -> In k ltprime_list8.
Proof.
intros kLT kB.
rewrite ltprime_list8E.
apply (lnext_correct 10 (refl_equal _) 6); try lia; auto.
exact ltprime_list7_correct.
Qed.

Lemma ltprime_list9_correct k :
  ltprime 10 k -> 10 ^ 8 <= k < 10 ^ 9 -> In k ltprime_list9.
Proof.
intros kLT kB.
rewrite ltprime_list9E.
apply (lnext_correct 10 (refl_equal _) 7); try lia; auto.
exact ltprime_list8_correct.
Qed.

Lemma ltprime_list10_correct k :
  ltprime 10 k -> 10 ^ 9 <= k < 10 ^ 10 -> In k ltprime_list10.
Proof.
intros kLT kB.
rewrite ltprime_list10E.
apply (lnext_correct 10 (refl_equal _) 8); try lia; auto.
exact ltprime_list9_correct.
Qed.

Lemma ltprime_list11_correct k :
  ltprime 10 k -> 10 ^ 10 <= k < 10 ^ 11 -> In k ltprime_list11.
Proof.
intros kLT kB.
rewrite ltprime_list11E.
apply (lnext_correct 10 (refl_equal _) 9); try lia; auto.
exact ltprime_list10_correct.
Qed.

Lemma ltprime_list12_correct k :
  ltprime 10 k -> 10 ^ 11 <= k < 10 ^ 12 -> In k ltprime_list12.
Proof.
intros kLT kB.
rewrite ltprime_list12E.
apply (lnext_correct 10 (refl_equal _) 10); try lia; auto.
exact ltprime_list11_correct.
Qed.

Lemma ltprime_list13_correct k :
  ltprime 10 k -> 10 ^ 12 <= k < 10 ^ 13 -> In k ltprime_list13.
Proof.
intros kLT kB.
rewrite ltprime_list13E.
apply (lnext_correct 10 (refl_equal _) 11); try lia; auto.
exact ltprime_list12_correct.
Qed.

Lemma ltprime_list14_correct k :
  ltprime 10 k -> 10 ^ 13 <= k < 10 ^ 14 -> In k ltprime_list14.
Proof.
intros kLT kB.
rewrite ltprime_list14E.
apply (lnext_correct 10 (refl_equal _) 12); try lia; auto.
exact ltprime_list13_correct.
Qed.

Lemma ltprime_list15_correct k :
  ltprime 10 k -> 10 ^ 14 <= k < 10 ^ 15 -> In k ltprime_list15.
Proof.
intros kLT kB.
rewrite ltprime_list15E.
apply (lnext_correct 10 (refl_equal _) 13); try lia; auto.
exact ltprime_list14_correct.
Qed.

Lemma ltprime_list16_correct k :
  ltprime 10 k -> 10 ^ 15 <= k < 10 ^ 16 -> In k ltprime_list16.
Proof.
intros kLT kB.
rewrite ltprime_list16E.
apply (lnext_correct 10 (refl_equal _) 14); try lia; auto.
exact ltprime_list15_correct.
Qed.

Lemma ltprime_list17_correct k :
  ltprime 10 k -> 10 ^ 16 <= k < 10 ^ 17 -> In k ltprime_list17.
Proof.
intros kLT kB.
rewrite ltprime_list17E.
apply (lnext_correct 10 (refl_equal _) 15); try lia; auto.
exact ltprime_list16_correct.
Qed.

Lemma ltprime_list18_correct k :
  ltprime 10 k -> 10 ^ 17 <= k < 10 ^ 18 -> In k ltprime_list18.
Proof.
intros kLT kB.
rewrite ltprime_list18E.
apply (lnext_correct 10 (refl_equal _) 16); try lia; auto.
exact ltprime_list17_correct.
Qed.

Lemma ltprime_list19_correct k :
  ltprime 10 k -> 10 ^ 18 <= k < 10 ^ 19 -> In k ltprime_list19.
Proof.
intros kLT kB.
rewrite ltprime_list19E.
apply (lnext_correct 10 (refl_equal _) 17); try lia; auto.
exact ltprime_list18_correct.
Qed.

Lemma ltprime_list20_correct k :
  ltprime 10 k -> 10 ^ 19 <= k < 10 ^ 20 -> In k ltprime_list20.
Proof.
intros kLT kB.
rewrite ltprime_list20E.
apply (lnext_correct 10 (refl_equal _) 18); try lia; auto.
exact ltprime_list19_correct.
Qed.

Lemma ltprime_list21_correct k :
  ltprime 10 k -> 10 ^ 20 <= k < 10 ^ 21 -> In k ltprime_list21.
Proof.
intros kLT kB.
rewrite ltprime_list21E.
apply (lnext_correct 10 (refl_equal _) 19); try lia; auto.
exact ltprime_list20_correct.
Qed.

Lemma ltprime_list22_correct k :
  ltprime 10 k -> 10 ^ 21 <= k < 10 ^ 22 -> In k ltprime_list22.
Proof.
intros kLT kB.
rewrite ltprime_list22E.
apply (lnext_correct 10 (refl_equal _) 20); try lia; auto.
exact ltprime_list21_correct.
Qed.

Lemma ltprime_list23_correct k :
  ltprime 10 k -> 10 ^ 22 <= k < 10 ^ 23 -> In k ltprime_list23.
Proof.
intros kLT kB.
rewrite ltprime_list23E.
apply (lnext_correct 10 (refl_equal _) 21); try lia; auto.
exact ltprime_list22_correct.
Qed.

Lemma ltprime_list24_correct k :
  ltprime 10 k -> 10 ^ 23 <= k < 10 ^ 24 -> k = 357686312646216567629137.
Proof.
intros kLT kB.
assert (H : In k ltprime_list24); [|inversion H as [|H1]; auto; inversion H1].
rewrite ltprime_list24E.
apply (lnext_correct 10 (refl_equal _) 22); try lia; auto.
exact ltprime_list23_correct.
Qed.

Lemma ltprime_list25_correct k : 10 ^ 24 <= k < 10 ^ 25 -> ~ ltprime 10 k.
Proof.
intros kLT kB.
assert (H : In k ltprime_list25); [|inversion H].
rewrite ltprime_list25E.
apply (lnext_correct 10 (refl_equal _) 23); try lia; auto.
intros k1 Hk1 k1B.
rewrite ltprime_list24E.
apply (lnext_correct 10 (refl_equal _) 22); try lia; auto.
exact ltprime_list23_correct.
Qed.

Lemma ltprime_main : 
  ltprime 10 357686312646216567629137 /\ 
  forall k, 357686312646216567629137 < k -> ~ ltprime 10 k.
Proof.
split.
  now ltprime_tac 10.
intros k kL kLT.
assert (H : k < 10 ^ 24 \/ 10 ^ 24 <= k) by lia.
destruct H as [H1|H1].
  assert (k = 357686312646216567629137); [|lia].
  now apply ltprime_list24_correct; auto; lia.
assert (Hv : ltprime 10 (k mod 10 ^ 25)).
  now apply ltprime_mod; try lia; auto. 
case (ltprime_list25_correct (k mod 10 ^ 25)); auto.
replace 25 with (24 + 1) by lia.
replace 24 with (log 10 (k mod 10 ^ 25)) at 1 4.
  apply log_correct; try lia.
  now apply GZnZ.p_pos, (ltprime_prime 10).
replace 25 with (24 + 1) by lia.
apply no_zero_digit_log; try lia; [|case kLT; auto].
assert (log 10 (10 ^ 24) <= log 10 k) by now apply log_incr; lia.
split; [lia|].
change 24 with (log 10 (10 ^ 24)); lia.
Qed.
