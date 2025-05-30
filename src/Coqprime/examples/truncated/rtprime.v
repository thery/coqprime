From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime ltprime_init.

Declare Scope seq_scope.
Open Scope seq_scope.
Open Scope Z_scope.

Section Digits.

Variable b : Z.
Hypotheses b_pos : 1 < b.

Lemma log_0 : log b 0 = 0.
Proof. now auto. Qed.

Lemma log_neg v : v <= 0 -> log b v = 0.
Proof. now case v; auto; lia. Qed.

Lemma log_div n k : 
  0 <= k <= log b n -> log b (n / b ^ k) = log b n - k.
Proof.
intros kP.
assert (Hn : n <= 0 \/ 0 < n); [lia|destruct Hn as [nE|nP1]].
  rewrite !log_neg in kP; try lia.
  rewrite !log_neg; try lia.
  now apply Z.div_le_upper_bound; lia.
apply log_inv; try lia; auto.
assert (nB : b ^ log b n <= n < b ^ (log b n + 1)).
apply log_correct; try lia.
split.
  apply Z.div_le_lower_bound; try lia.
  rewrite <- Z.pow_add_r; try lia.
  now replace (k + (log b n - k)) with (log b n); lia.
apply Z.div_lt_upper_bound; try lia.
rewrite <- Z.pow_add_r; try lia.
now replace (k + (log b n - k + 1)) with (log b n + 1); lia.
Qed.

Lemma digit_div n k1 k2 : 
  0 <= k1 -> 0 <= k2 -> digit b (n / b ^ k1) k2 = digit b n (k1 + k2).
Proof.
intros k1P k2P.
now unfold digit; rewrite Zdiv_Zdiv, <- Z.pow_add_r; lia.
Qed.

Lemma no_zero_digit_rdecompose n m : 
  0 < m < b  -> no_zero_digit b n -> no_zero_digit b (n * b + m).
Proof.
intros mB nNZ.
replace b with (b ^ (log b m + 1)) at 2.
  apply no_zero_digit_decompose; auto.
    now apply (no_zero_digit_pos b).
  now apply no_zero_digit_small; lia.
replace (log b m) with 0; [lia|].
now apply sym_equal, log_inv; lia.
Qed.

Lemma no_zero_digit_div n k : 
  0 <= k <= log b n -> no_zero_digit b n -> no_zero_digit b (n / b ^ k).
Proof.
intros kP [Hn Hnl]; split.
- assert (H : 0 <= n / b ^ k) by now apply Z_div_nonneg_nonneg; lia.
  assert (n / b ^ k <> 0); [|lia].
  assert (LP := log_pos n).
  intros Hnb; assert (0 <= n < b ^ k \/ b ^ k < n <= 0).
    now apply Z.div_small_iff; lia.
  assert (b ^ log b n <= n < b ^ (log b n + 1)).
    now apply log_correct; lia.
  assert (b ^ k <= b ^ (log b n)); [|lia].
  now apply Z.pow_le_mono_r; lia.
- intros k1 k1P Hm.
  rewrite log_div; auto.
  assert (log b n < k + k1); [|lia].
  apply Hnl; try lia.
  now rewrite <- digit_div; lia.
Qed.

Definition rtprime n := 
  no_zero_digit b n /\ forall k, 0 <= k <= log b n -> prime (n / b ^ k).

Lemma rtprime_small p : prime p -> p < b -> rtprime p.
Proof.
intros pP pB.
assert (H : 0 < p) by now apply GZnZ.p_pos.
split.
  now apply no_zero_digit_small; lia.
intros k.
replace (log b p) with 0.
  intros kE; replace k with 0 by lia.
  now rewrite Z.div_1_r.
now apply sym_equal, log_inv; lia.
Qed.

Lemma rtprime_prime p : rtprime p -> prime p.
Proof.
intros [pNZ Hp].
replace p with (p / b ^ 0).
  now apply Hp; split; [lia | apply log_pos].
now rewrite Z.div_1_r.
Qed.

Lemma rtprime_decompose n m : 
  0 < m < b -> rtprime n -> prime (n * b + m) -> rtprime (n * b + m).
Proof.
intros mB  [nNZ nM] mnP; split.
  now apply no_zero_digit_rdecompose; try lia; auto.
assert (nPr : prime n) by now apply rtprime_prime.
assert (nP : 0 < n) by now apply GZnZ.p_pos.
intros k kP.
assert (Hl := log_correct b b_pos n nP).
assert (lP := log_pos b n).
assert (H : (k <= log b n \/ log b n < k)) by lia.
destruct H as [Hkn | Hkn].
- assert (b ^ k <= n).
    assert (b ^ k <= b ^ (log b n)); [|lia].
    now apply Z.pow_le_mono_r; lia.
  assert (Hk : k = 0 \/ 1 <= k) by lia.
  destruct Hk as [kE|kP1]; [now rewrite kE, Z.div_1_r|].
  replace k with (1 + (k - 1)) by lia.
  rewrite Z.pow_add_r, Z.pow_1_r; try lia; auto.
  rewrite <- Zdiv_Zdiv; try lia.
  rewrite Z.div_add_l; try lia.
  rewrite (Z.div_small _ b), Z.add_0_r; try lia.
  now apply nM; lia.
- replace k with (1 + (k - 1)) by lia.
  rewrite Z.pow_add_r, Z.pow_1_r; try lia; auto.
  rewrite <- Zdiv_Zdiv; try lia.
  rewrite Z.div_add_l; try lia.
  rewrite (Z.div_small _ b), Z.add_0_r; try lia.
  replace b with (b ^ (log b m + 1)) in kP at 2.
    rewrite log_add in kP; try lia.
    replace (log b m) with 0 in kP.
      replace (k - 1) with (log b n) by lia.
      now apply nM; lia.
    now apply sym_equal, log_inv; lia.
  replace (log b m) with 0; [lia|].
  now apply sym_equal, log_inv; lia.
Qed.

Lemma rtprime_div n k :
   0 <= k <= log b n  -> rtprime n -> rtprime (n / b ^ k).
Proof.
intros kP [Hn Hnl]; split; [now apply no_zero_digit_div|].
intros k1 k1P.
rewrite Zdiv_Zdiv; try lia.
rewrite <- Z.pow_add_r; try lia.
apply Hnl.
now rewrite log_div in k1P; lia.
Qed.

Notation "[ :: ]" := nil (format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::]) (format "[ ::  x1 ]") : seq_scope.


Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.

Definition add_rtlist i l l1 := 
  fold_left (fun l z => 
               let v := z * b + i in 
               if is_pseudo_prime v then lZ_insert v l else l) l l1.

Lemma add_rtlist_subset i l l1 k : In k l1 -> In k (add_rtlist i l l1).
Proof.
generalize l1; elim l; simpl; auto.
intros a l2 IH l3 Il3.
case is_pseudo_prime; apply IH; auto.
now apply lZ_insert_consr.
Qed.

Lemma add_rtlist_correct i l l1 k : 
  0 <= b -> 0 <= i -> 0 <= k ->
  In k l -> prime(k * b + i) -> In (k * b + i) (add_rtlist i l l1).
Proof.
intros bP iP.
generalize l1 k; elim l; simpl; [intros _ _ _ []| intros z l2 IH l3 k3 k3P Ik3 inkP].
destruct Ik3 as [zE | Ink3l2].
  subst z.
  apply add_rtlist_subset.
  generalize (is_pseudo_prime_correct (k3 * b + i)); case is_pseudo_prime.
    now intros; apply lZ_insert_consl.
  now intros H; case H; auto; lia.
now apply IH; auto.
Qed.

Definition rnext (l1 : list Z) := 
  let l := ldigit b in 
  fold_left (fun l i => add_rtlist i l1 l) l [::].

Lemma rnext_correct n l1 k : 
  0 <= n ->
  (forall k, rtprime k -> b ^ n <= k < b ^ (n + 1) -> In k l1) ->
  rtprime k  -> b ^ (n + 1) <= k < b ^ (n + 2) -> In k (rnext l1).
Proof.
intros nP Hl Hlt Hk.
assert (Le : log b k = n + 1).
  apply log_inv; try lia; replace (n + 1 + 1) with (n + 2); lia.
pose (k1 := k / b).
pose (m := k mod b).
assert (mE : m = digit b k 0).
  now rewrite digitE, Z.div_1_r, Z.pow_1_r; lia.
assert (mB : 0 < m < b).
  assert (0 <= m < b) by now rewrite mE; apply Z.mod_pos_bound; lia.
  assert (m <> 0); [|lia]; intros mZ.
  assert (n + 1 < 0); [|lia].
  now case Hlt; intros [_ Hv] _; rewrite <- Le; apply Hv; lia.
assert (kE : k = k1 * b + m).
  now rewrite (Z_div_mod_eq_full k b); lia.
rewrite kE.
assert (k1Lt : rtprime k1).
  unfold k1; replace b with (b ^ 1) by lia.
  now apply rtprime_div; try lia.
assert (k1P : 0 < k1) by now apply GZnZ.p_pos, rtprime_prime.
fold k1; fold m.
assert (Hk1 : In k1 l1).
  apply Hl.
    unfold k1; replace b with (b ^ 1) by lia.
    now apply rtprime_div; try lia; auto.
  replace n with (log b k1).
    now apply log_correct; try lia.
  unfold k1.
  replace b with (b ^ 1) at 2 by lia.
  now rewrite log_div; try lia.
unfold rnext.
assert (mI : In m (ldigit b)).
  now apply ldigit_correct.
revert mI; generalize ([::] : list Z); elim ldigit; simpl; auto.
  now intros l [].
intros a l2 IH l [aE|mIl].
  subst a.
  assert (In (k1 * b + m) (add_rtlist m l1 l)).
    apply add_rtlist_correct; try lia; auto.
    now rewrite <- kE; apply rtprime_prime; try lia; auto.
  revert H; generalize (add_rtlist m l1 l).
  elim l2; simpl; auto.
  intros a1 ll1 IH1 ll2 Inll2.
  apply IH1.
  now apply add_rtlist_subset.
now apply IH.
Qed.

End Digits.

Ltac rtprime_tac b := 
repeat (match goal with
  |- rtprime _ ?a => 
       let a' := eval compute in a in 
       let v1 := constr: (a' mod b) in
       let v2 := constr: (a' / b) in
       let v2' := eval compute in v2 in 
       apply (rtprime_decompose b (refl_equal _) v2' v1); [compute; auto| | ]
|  |- prime ?a => 
      solve [compute; auto with prime]
end);
try (apply rtprime_small; [lia|auto with prime|lia]).

Notation "[ :: ]" := nil (format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::]) (format "[ ::  x1 ]") : seq_scope.


Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.



Definition rt3prime_list1 := [:: 2; 3; 5; 7]%Z.
Compute (1, rt3prime_list1, length rt3prime_list1).
Definition rt3prime_list2 := Eval compute in rnext 3 rt3prime_list1.
Compute (2, rt3prime_list2, length rt3prime_list2).
Definition rt3prime_list3 := Eval compute in rnext 3 rt3prime_list2.
Compute (3, rt3prime_list3, length rt3prime_list3).
Definition rt3prime_list4 := Eval compute in rnext 3 rt3prime_list3.
Compute (4, rt3prime_list4, length rt3prime_list4).
Definition rt3prime_list5 := Eval compute in rnext 3 rt3prime_list4.

Definition rtprime_list1 := [:: 2; 3; 5; 7]%Z.
Compute (1, rtprime_list1, length rtprime_list1).
Definition rtprime_list2 := Eval compute in rnext 10 rtprime_list1.
Compute (2, rtprime_list2, length rtprime_list2).
Definition rtprime_list3 := Eval compute in rnext 10 rtprime_list2.
Compute (3, rtprime_list3, length rtprime_list3).
Definition rtprime_list4 := Eval compute in rnext 10 rtprime_list3.
Compute (4, rtprime_list4, length rtprime_list4).
Definition rtprime_list5 := Eval compute in rnext 10 rtprime_list4.
Compute (5, rtprime_list5, length rtprime_list5).
Definition rtprime_list6 := Eval compute in rnext 10 rtprime_list5.
Compute (6, rtprime_list6, length rtprime_list6).
Definition rtprime_list7 := Eval compute in rnext 10 rtprime_list6.
Compute (7, rtprime_list7, length rtprime_list7).
Definition rtprime_list8 := Eval compute in rnext 10 rtprime_list7.
Compute (8, rtprime_list8, length rtprime_list8).
Definition rtprime_list9 := Eval compute in rnext 10 rtprime_list8.
Compute (9, rtprime_list9, length rtprime_list9).
Compute (length rtprime_list1 + length rtprime_list2 + length rtprime_list3 + 
         length rtprime_list4 + length rtprime_list5 + length rtprime_list6 + 
         length rtprime_list7 + length rtprime_list8 + length rtprime_list9)%nat.


