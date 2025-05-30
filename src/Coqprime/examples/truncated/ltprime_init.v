From Stdlib Require Import ZArith List Lia.
From Coqprime Require Import PocklingtonRefl all_prime.

Declare Scope seq_scope.
Open Scope seq_scope.
Open Scope Z_scope.

Section Digits.

Variable b : Z.
Hypotheses b_pos : 1 < b.

Fixpoint plength h := 
  match h with
  | xH => 1 
  | xI h1 => plength h1 + 1 
  | xO h1 => plength h1 + 1 
  end.

Lemma plength_pos p : 0 <= plength p.
Proof. now elim p; simpl; lia. Qed.

Lemma plength_pow p : Z.pos p < b ^ plength p.
Proof.
elim p; simpl; [intros p1 IH|intros p1 IH|].
- assert (H := plength_pos p1). 
  rewrite Z.pow_add_r, Z.pow_1_r; nia.
- assert (H := plength_pos p1). 
  rewrite Z.pow_add_r, Z.pow_1_r; nia.
- lia.
Qed.

Fixpoint log_aux p v h := 
  if v <? (b ^ (p + 1)) then p else 
  match h with 
  | xH => 0 
  | xI h1 => log_aux (p + 1) v h1 
  | xO h1 => log_aux (p + 1) v h1 
  end.

Lemma log_aux_correct p v h :
  0 <= p -> b ^ p <= v < b ^ (p + plength h) -> 
  b ^ (log_aux p v h) <= v < b ^ (log_aux p v h + 1).
Proof.
generalize p; elim h; simpl; auto; clear p.
- intros p IH p1 p1P HB.
  case Z.ltb_spec0; try lia.
  intros H1; apply IH; try split; try lia.
  replace (p1 + 1 + plength p) with (p1 + (plength p + 1)) by lia.
  lia.
- intros p IH p1 p1P HB.
  case Z.ltb_spec0; try lia.
  intros H1; apply IH; try split; try lia.
  replace (p1 + 1 + plength p) with (p1 + (plength p + 1)) by lia.
  lia.
- intros p pP HB.
  case Z.ltb_spec0; try lia.
Qed.

Lemma log_aux_pos p v h : 0 <= p-> 0 <= log_aux p v h.
Proof.
generalize p; elim h; simpl; auto; clear p.
- intros p IH p1 p1P.
  case Z.ltb_spec0; try lia.
  intros H1; apply IH; lia.
- intros p IH p1 p1P.
  case Z.ltb_spec0; try lia.
  intros H1; apply IH; lia.
- intros p IH; case Z.ltb_spec0; lia.
Qed.

(* log in base b                                                              *)
Definition log v := 
match v with Zpos h => log_aux 0 v h | _ => 0 end.

Lemma log_neg v : v <= 0 -> log v = 0.
Proof. now destruct v; simpl; lia. Qed.

Lemma log_correct v : 
  0 < v -> b ^ (log v) <= v < b ^ (log v + 1).
Proof.
case v; [idtac|intros p H|idtac]; simpl; try lia.
apply log_aux_correct; try lia.
split; [lia|].
now apply plength_pow.
Qed.

Lemma log_pos v : 0 <= log v.
Proof.
now case v; intros; simpl; try lia; apply log_aux_pos; lia.
Qed.

Lemma log_inv v p : 
  0 <= p -> b ^ p <= v < b ^ (p + 1) -> log v = p.
Proof.
intros pP vB.
assert (vP : 0 < v) by now assert (0 < b ^ p); try apply Z.pow_pos_nonneg; lia.
assert (HB := log_correct v vP).
assert (Hp : p = log v \/ p + 1 <= log v \/ log v + 1 <= p) by lia.
destruct Hp as [Hp|[Hp | Hp]]; auto.
- assert (b ^ (p + 1) <= b ^ log v); [|lia].
  now apply Z.pow_le_mono_r; lia.
- assert (b ^ (log v + 1) <= b ^ p); [|lia].
  now apply Z.pow_le_mono_r; lia.
Qed.

Lemma log_pow k : 0 <= k -> log (b ^ k) = k.
Proof.
intros kP; apply log_inv; try lia.
rewrite Z.pow_add_r; nia.
Qed.

Lemma log_pow_lt v k : 0 < k -> 0 <= v < b ^ k -> log v < k.
Proof.
intros kP vB.
assert (vC : v = 0 \/ 0 < v); [lia| destruct vC as [vE|vP]].
  now rewrite vE.
assert (H := log_correct _ vP).
assert (b ^ log v < b ^ k) by lia.
apply (Z.pow_lt_mono_r_iff b); lia.
Qed.

Lemma log_incr v1 v2 : v1 <= v2 -> log v1 <= log v2.
Proof.
intros vB.
assert (v1C : v1 <= 0 \/ 0 < v1); [lia| destruct v1C as [v1N|v1P]].
  now rewrite log_neg; auto; apply log_pos.
assert (Hv1 : b ^ log v1 <= v1 < b ^ (log v1 + 1)). 
  now apply log_correct; lia.
assert (Hv2 : b ^ log v2 <= v2 < b ^ (log v2 + 1)). 
  now apply log_correct; lia.
assert (Hv : log v1 = log v2 \/ log v1 + 1 <= log v2 \/ log v2 + 1 <= log v1).
  now lia.
destruct Hv as [Hv|[Hv | Hv]]; try lia.
assert (b ^ (log v2 + 1) <= b ^ log v1); [|lia].
apply Z.pow_le_mono_r; lia.
Qed.

Lemma log_add m n k : 
  0 < m -> 0 < n -> log n < k -> log (m * b ^ k + n) = log m + k.
Proof.
intros mP nP lnLk.
assert(mB := log_correct _ mP).
assert(nB := log_correct _ nP).
assert (pmB : 0 <= log m) by now apply log_pos.
assert (pnB : 0 <= log n) by now apply log_pos.
assert(nkB: b ^ (log n + 1) <= b ^ k) by now apply Z.pow_le_mono_r; lia.
rewrite Z.pow_add_r in mB, nB, nkB; try lia.
apply log_inv; [nia|]; rewrite !Z.pow_add_r; try lia.
split; nia.
Qed.

Lemma log_mod v k : 0 <= v -> 0 < k -> log (v mod b ^ k) < k.
Proof.
intros vP kP; rewrite <- (log_pow k) at 2; try lia.
rewrite log_pow; [| lia].
assert (Hv1 : 0 <= v mod b ^ k) by now apply Z_mod_nonneg_nonneg; lia.
assert (Hv2 : v mod b ^ k = 0 \/ 0 < v mod b ^ k); 
    [lia| destruct Hv2 as [vE | vP1]].
  now rewrite vE.
apply log_pow_lt; auto.
assert (0 <= v mod b ^ k < b ^ k) by now apply Z.mod_pos_bound; lia.
lia.
Qed.

Lemma log_0 : log 0 = 0.
Proof. now auto. Qed.

Lemma log_div n k : 
  0 <= k <= log n -> log (n / b ^ k) = log n - k.
Proof.
intros kP.
assert (Hn : n <= 0 \/ 0 < n); [lia|destruct Hn as [nE|nP1]].
  rewrite !log_neg in kP; try lia.
  rewrite !log_neg; try lia.
  now apply Z.div_le_upper_bound; lia.
apply log_inv; try lia; auto.
assert (nB : b ^ log n <= n < b ^ (log n + 1)).
apply log_correct; try lia.
split.
  apply Z.div_le_lower_bound; try lia.
  rewrite <- Z.pow_add_r; try lia.
  now replace (k + (log n - k)) with (log n); lia.
apply Z.div_lt_upper_bound; try lia.
rewrite <- Z.pow_add_r; try lia.
now replace (k + (log n - k + 1)) with (log n + 1); lia.
Qed.

(* kth digit in base b                                                        *)
Definition digit n k := (n / b ^ k) mod b.

Lemma digitE n k : 0 <= k -> 0 <= n -> digit n k = n mod b ^ (k + 1) / b ^ k.
Proof.
intros kP nP.
unfold digit; rewrite (Z_div_mod_eq_full n (b ^ (k + 1))) at 1.
replace (b ^ (k + 1) * (n / b ^ (k + 1)) + n mod b ^ (k + 1)) with
        (n mod b ^ (k + 1) + (b * (n / b ^ (k + 1))) * b ^ k);
    [|rewrite Z.pow_add_r, Z.pow_1_r; lia].
rewrite Z_div_plus_full; try lia.
rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small; try lia.
split.
  apply Z.div_pos; try lia.
  now apply Z_mod_nonneg_nonneg; lia.
apply Z.div_lt_upper_bound; try lia.
assert (H : 0 <= n mod b ^ (k + 1) < b ^ (k + 1)).
  now apply Z.mod_pos_bound; lia.
now rewrite Z.pow_add_r in H at 3; lia.
Qed.

Lemma digit_div n k1 k2 : 
  0 <= k1 -> 0 <= k2 -> digit (n / b ^ k1) k2 = digit n (k1 + k2).
Proof.
intros k1P k2P.
now unfold digit; rewrite Zdiv_Zdiv, <- Z.pow_add_r; lia.
Qed.

(* Not having zero digit in base b                                            *)
Definition no_zero_digit n :=
  0 < n /\ forall k, 0 <= k -> digit n k = 0 -> log n < k.

Lemma no_zero_digit_pos n : no_zero_digit n -> 0 < n.
Proof. now intros []. Qed.

Lemma no_zero_digit0 : ~ no_zero_digit 0.
Proof. now intros [H]; contradict H; auto with zarith. Qed.

Lemma no_zero_digit_small n : 0 < n < b -> no_zero_digit n.
Proof.
intros nB; split; auto with zarith.
intros k Hk.
replace (log n) with 0; [|apply sym_equal, log_inv; lia].
assert (H1 : k = 0 \/ 1 <= k) by lia .
destruct H1 as [->|]; [|lia].
unfold digit; rewrite Zdiv_1_r, Zmod_small; auto with zarith.
Qed.

Lemma no_zero_digit_decompose n m : 
  0 < m -> no_zero_digit m -> no_zero_digit n ->
  no_zero_digit (m * b ^ (log n +1) + n).
Proof.
intros mP [H1m H2m] [H1n H2n]; split; [lia|].
intros k1 k1P.
assert (Hl := log_correct n H1n).
assert (lP := log_pos n).
assert (H : (k1 <= log n \/ log n < k1)) by lia.
destruct H as [Hk1k | Hkk1].
- assert (b ^ k1 <= n).
    assert (b ^ k1 <= b ^ (log n)); [|lia].
    now apply Z.pow_le_mono_r; lia.
  replace (m * b ^ (log n + 1)) with 
          (m * b ^ (log n - k1) * b * b ^ k1).
    unfold digit; rewrite Z.div_add_l; [|lia].
    rewrite Zplus_comm, Z_mod_plus_full; intros H1.
    assert (H2 : log n < k1) by (apply H2n; [lia|auto]).
    assert (b ^ k1 <= b ^ log n); [|lia].
    now apply Z.pow_le_mono_r; lia.
  replace b with (b ^ 1) at 2; [|lia].
  rewrite <- !Z.mul_assoc, <- !Z.pow_add_r; try lia.
  now replace (log n - k1 + (1 + k1)) with (log n +1 ); lia.
- unfold digit. 
  replace ((m * b ^ (log n + 1) + n) / b ^ k1) with 
           (m / b ^ (k1 - (log n + 1))).
    intros H3; assert (H4 : log m < k1 - (log n + 1)).
      now apply H2m; try lia.
    now rewrite log_add; lia.
  replace (b ^ k1) with (b ^ (log n + 1) * b ^ (k1 - (log n + 1))).
    rewrite <- Zdiv_Zdiv; [|lia|lia].
    rewrite Z.div_add_l; [|lia].
    rewrite (Zdiv_small _ (b ^ (log n + 1))); [|lia].
    now rewrite Zplus_0_r.
  rewrite <- Z.pow_add_r; try lia.
  replace (log n + 1 + (k1 - (log n + 1))) with k1; lia.
Qed.

Lemma no_zero_digit_ldecompose n m : 
  0 < m < b  -> no_zero_digit n -> no_zero_digit (m * b ^ (log n +1) + n).
Proof.
intros mB nB; apply no_zero_digit_decompose; auto; [lia|].
now apply no_zero_digit_small.
Qed.

Lemma no_zero_digit_mod n k : 
  0 < k -> no_zero_digit n -> no_zero_digit (n mod b ^ k).
Proof.
intros kP [Hn Hnl]; split.
- assert (H : 0 <= n mod b ^ k) by now apply Z_mod_nonneg_nonneg; lia.
  assert (n mod b ^ k <> 0); [|lia].
  assert (LP := log_pos n).
  intros Hk; assert (En0 : log n < 0); [|lia].
  apply Hnl; try lia.
  unfold digit.
  rewrite Z.pow_0_r, Z.div_1_r, <- (Z.mod_mod_divide n (b ^ k) b); try lia.
    now rewrite Hk, Z.mod_0_l; lia.
  now apply Zpow_facts.Zpower_divide.
- intros k1 k1P Hm.
  assert (Hk : k <= k1 \/ k1 < k) by lia.
  destruct Hk as [Hk|Hk].
    assert (log (n mod b ^ k) < k); [|lia].
    apply log_pow_lt; try lia.
    now apply Z.mod_pos_bound; try lia.
  assert (H1 : (n mod b ^ k / b ^ k1) mod b = (n / b ^ k1) mod b).
    replace (n mod b ^ k) with
       (n + (- (n / b ^ k)) * b ^ (k - k1 - 1) * b * b ^ k1).
      rewrite Z_div_plus_full; try lia.
      now rewrite Z_mod_plus_full; lia.
    rewrite <- !Z.mul_assoc.
    replace b with (b ^ 1) at 3; [|lia].
    rewrite <- !Z.pow_add_r; try lia.
    replace (k - k1 - 1 + (1 + k1)) with k; [|lia].
    now rewrite (Z_div_mod_eq_full n (b ^ k)) at 1; lia.
  unfold digit in Hm; rewrite H1 in Hm.
  assert (H2 : log n < k1) by now apply Hnl; auto; lia.
  assert (log (n mod b ^ k) <= log n); [|lia].
  now apply log_incr, Z.mod_le; lia.
Qed.

Lemma no_zero_digit_log_mod n k : 
  0 <= n -> 0 <= k -> n mod b ^ (k + 1) < b ^ k -> digit n k = 0.
Proof.
intros nP kP H; rewrite digitE, Zdiv_small; auto; split; auto.
apply Z_mod_nonneg_nonneg; lia.
Qed.

Lemma no_zero_digit_log n k : 
  0 <= k <= log n -> no_zero_digit n -> log (n mod b ^ (k + 1)) = k.
Proof.
intros kP [Hn Hnl].
apply log_inv; [lia|].
split.
  assert (H : n mod b ^ (k + 1) < b ^ k \/ b ^ k <= n mod b ^ (k + 1)) by lia.
  destruct H; [|lia].
  assert (log n < k); [|lia].
  apply Hnl; try lia.
  now apply no_zero_digit_log_mod; lia.
assert (0 <= n mod b ^ (k + 1) < b ^ (k + 1)); [|lia].
now apply Z.mod_pos_bound; lia.
Qed.

Lemma logtop_digit n : 0 < n -> 0 < n / b ^ log n < b.
Proof.
intros nPos.
assert (H := log_correct n nPos).
assert (H1 : 0 < b ^ log n).
  apply Z.pow_pos_nonneg; try lia.
  now apply log_pos.
assert (1 <=  n / b ^ log n < b); [|lia].
split.
  now apply Z.div_le_lower_bound; lia.
apply Z.div_lt_upper_bound; try lia.
replace b with (b ^ 1) at 2; [|lia].
rewrite <- Z.pow_add_r; try lia.
now apply log_pos.
Qed.


Lemma no_zero_digit_rdecompose n m : 
  0 < m < b  -> no_zero_digit n -> no_zero_digit (n * b + m).
Proof.
intros mB nNZ.
replace b with (b ^ (log m + 1)).
  apply no_zero_digit_decompose; auto.
    now apply no_zero_digit_pos.
  now apply no_zero_digit_small; lia.
replace (log m) with 0; [lia|].
now apply sym_equal, log_inv; lia.
Qed.

Lemma no_zero_digit_div n k : 
  0 <= k <= log n -> no_zero_digit n -> no_zero_digit (n / b ^ k).
Proof.
intros kP [Hn Hnl]; split.
- assert (H : 0 <= n / b ^ k) by now apply Z_div_nonneg_nonneg; lia.
  assert (n / b ^ k <> 0); [|lia].
  assert (LP := log_pos n).
  intros Hnb; assert (0 <= n < b ^ k \/ b ^ k < n <= 0).
    now apply Z.div_small_iff; lia.
  assert (b ^ log n <= n < b ^ (log n + 1)).
    now apply log_correct; lia.
  assert (b ^ k <= b ^ (log n)); [|lia].
  now apply Z.pow_le_mono_r; lia.
- intros k1 k1P Hm.
  rewrite log_div; auto.
  assert (log n < k + k1); [|lia].
  apply Hnl; try lia.
  now rewrite <- digit_div; lia.
Qed.

(* left truncated prime                                                       *)
Definition ltprime n := 
  no_zero_digit n /\ forall k, 0 < k -> prime (n mod b ^ k).

Lemma ltprime_small p : prime p -> p < b -> ltprime p.
Proof.
intros pP pB.
assert (H : 0 < p) by now apply GZnZ.p_pos.
split.
  now apply no_zero_digit_small; lia.
intros k kP; rewrite Z.mod_small; auto.
assert (b <= b ^ k); [|lia].
replace b with (b ^ 1) at 1; [|lia].
now apply Z.pow_le_mono_r; lia.
Qed.

Lemma ltprime_prime p : ltprime p -> prime p.
Proof.
intros [pNZ Hp].
replace p with (p mod b ^(log p + 1)).
  now apply Hp; assert (H := log_pos p); lia.
apply Z.mod_small.
assert (pP :=  no_zero_digit_pos _ pNZ).
assert (pB := log_correct _ pP).
lia.
Qed.

Lemma ltprime_ldecompose n m : 
  0 < m < b -> ltprime n -> 
  prime (m * b ^ (log n + 1) + n) -> ltprime (m * b ^ (log n + 1) + n).
Proof.
intros mB  [nNZ nM] mnP; split.
  now apply no_zero_digit_ldecompose.
assert (nPr : prime n) by now apply ltprime_prime.
assert (nP : 0 < n) by now apply GZnZ.p_pos.
intros k kP.
assert (Hl := log_correct n nP).
assert (lP := log_pos n).
assert (H : (k <= log n \/ log n < k)) by lia.
destruct H as [Hkn | Hkn].
- assert (b ^ k <= n).
    assert (b ^ k <= b ^ (log n)); [|lia].
    now apply Z.pow_le_mono_r; lia.
  replace (m * b ^ (log n + 1)) with 
          (m * b ^ (log n - k) * b * b ^ k).
    rewrite Zplus_comm, Z_mod_plus_full.
    now apply nM.
  replace b with (b ^ 1) at 2; [|lia].
  rewrite <- !Z.mul_assoc, <- !Z.pow_add_r; try lia.
  replace (log n - k + (1 + k)) with (log n + 1); lia.
- replace ((m * b ^ (log n + 1) + n) / b ^ k) with 
           (m / b ^ (k - (log n + 1))).
    replace (b ^ k) with (b ^ (log n + 1) * b ^ (k - (log n + 1))).
      rewrite Z.rem_mul_r; try lia.
      rewrite (Zplus_comm _ n), Z_mod_plus_full, (Zplus_comm n).
      rewrite  Z.div_add_l; try lia.
      rewrite Zdiv_small, Z.add_0_r; try lia.
      rewrite Zmod_small; try lia.
      assert (Hk : k = log n + 1 \/ log n + 1 < k) by lia.
      destruct Hk as [kE | Hk1].
        now rewrite kE, Z.sub_diag, Z.mod_1_r, Z.mul_0_r, Z.add_0_r.
      rewrite Zmod_small.
        now rewrite Z.add_comm, Z.mul_comm.
      assert (b ^1 <=  b ^ (k - (log n + 1))).
        now apply Z.pow_le_mono_r; lia.
      now lia.
    rewrite <- Z.pow_add_r; try lia.
    now replace (log n + 1 + (k - (log n + 1))) with k; lia.
  replace (b ^ k) with (b ^ (log n + 1) * b ^ (k - (log n + 1))).
    rewrite <- Zdiv_Zdiv; [|lia|lia].
    rewrite Z.div_add_l; [|lia].
    rewrite (Zdiv_small _ (b ^ (log n + 1))); [|lia].
    now rewrite Zplus_0_r.
  rewrite <- Z.pow_add_r; try lia.
  now replace (log n + 1 + (k - (log n + 1))) with k; lia.
Qed.

Lemma ltprime_mod n k : 0 < k -> ltprime n -> ltprime (n mod b ^ k).
Proof.
intros kP [Hn Hnl]; split; [now apply no_zero_digit_mod|].
intros k1 k1P.
assert (H : k1 <= k \/ k < k1) by lia.
destruct H.
  rewrite Z.mod_mod_divide; [now apply Hnl|].
  replace k with (k1 + (k - k1)) by lia.
  now exists (b ^ (k - k1)); rewrite Z.pow_add_r; lia.
rewrite Z.mod_small; try lia.
  now apply Hnl.
assert (0 <= n mod b ^ k < b ^ k) by now apply Z.mod_pos_bound; lia.
assert (b ^ k <= b ^ k1); [|lia].
now apply Z.pow_le_mono_r; lia.
Qed.

Notation "[ :: ]" := nil (format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::]) (format "[ ::  x1 ]") : seq_scope.


Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.

Fixpoint iota n := match n with O => [::] | S n1 => n :: iota n1 end.

Definition ldigit := map Z.of_nat (iota (Z.to_nat (b - 1))).

Lemma ldigit_correct i : 0 < i < b -> In i ldigit.
Proof.
intros Hi; assert (bP : 0 <= b) by lia.
unfold ldigit; revert Hi; rewrite <- (Z2Nat.id _ bP).
case (Z.to_nat b); [simpl; lia|].
intros n.
replace (Z.to_nat (Z.of_nat (S n) - 1)) with n; [|lia].
replace (Z.of_nat (S n)) with (Z.of_nat n + 1); [|lia].
elim n; [simpl; lia|]; intros m IH H.
simpl.
replace (Z.pos (PosDef.Pos.of_succ_nat m)) with (Z.of_nat (S m)) by lia.
assert (H1 : 0 < i < Z.of_nat m + 1 \/ i  = Z.of_nat (S m)) by lia.
now destruct H1; auto.
Qed.

(*  593 933399 = 11941 × 49739 *)
Definition primes := [::
2;3;5;7;11;13;17;19;23;29;31;
37;41;43;47;53;59;61;67;71;
73;79;83;89;97;101;103;107;109;113;
127;131;137;139;149;151;157;163;167;173;
179;181;191;193;197;199;211;223;227;229;
233;239;241;251;257;263;269;271;277;281;
283;293;307;311;313;317;331;337;347;349;
353;359;367;373;379;383;389;397;401;409;
419;421;431;433;439;443;449;457;461;463;
467;479;487;491;499;503;509;521;523;541;
547;557;563;569;571;577;587;593;599;601;
607;613;617;619;631;641;643;647;653;659;
661;673;677;683;691;701;709;719;727;733;
739;743;751;757;761;769;773;787;797;809;
811;821;823;827;829;839;853;857;859;863;
877;881;883;887;907;911;919;929;937;941;
947;953;967;971;977;983;991;997;1009;1013;
1019;1021;1031;1033;1039;1049;1051;1061;1063;1069;
1087;1091;1093;1097;1103;1109;1117;1123;1129;1151;
1153;1163;1171;1181;1187;1193;1201;1213;1217;1223;
1229;1231;1237;1249;1259;1277;1279;1283;1289;1291;
1297;1301;1303;1307;1319;1321;1327;1361;1367;1373;
1381;1399;1409;1423;1427;1429;1433;1439;1447;1451;
1453;1459;1471;1481;1483;1487;1489;1493;1499;1511;
1523;1531;1543;1549;1553;1559;1567;1571;1579;1583;
1597;1601;1607;1609;1613;1619;1621;1627;1637;1657;
1663;1667;1669;1693;1697;1699;1709;1721;1723;1733;
1741;1747;1753;1759;1777;1783;1787;1789;1801;1811;
1823;1831;1847;1861;1867;1871;1873;1877;1879;1889;
1901;1907;1913;1931;1933;1949;1951;1973;1979;1987;
1993;1997;1999;2003;2011;2017;2027;2029;2039;2053;
2063;2069;2081;2083;2087;2089;2099;2111;2113;2129;
2131;2137;2141;2143;2153;2161;2179;2203;2207;2213;
2221;2237;2239;2243;2251;2267;2269;2273;2281;2287;
2293;2297;2309;2311;2333;2339;2341;2347;2351;2357;
2371;2377;2381;2383;2389;2393;2399;2411;2417;2423;
2437;2441;2447;2459;2467;2473;2477;2503;2521;2531;
2539;2543;2549;2551;2557;2579;2591;2593;2609;2617;
2621;2633;2647;2657;2659;2663;2671;2677;2683;2687;
2689;2693;2699;2707;2711;2713;2719;2729;2731;2741;
2749;2753;2767;2777;2789;2791;2797;2801;2803;2819;
2833;2837;2843;2851;2857;2861;2879;2887;2897;2903;
2909;2917;2927;2939;2953;2957;2963;2969;2971;2999;
3001;3011;3019;3023;3037;3041;3049;3061;3067;3079;
3083;3089;3109;3119;3121;3137;3163;3167;3169;3181;
3187;3191;3203;3209;3217;3221;3229;3251;3253;3257;
3259;3271;3299;3301;3307;3313;3319;3323;3329;3331;
3343;3347;3359;3361;3371;3373;3389;3391;3407;3413;
3433;3449;3457;3461;3463;3467;3469;3491;3499;3511;
3517;3527;3529;3533;3539;3541;3547;3557;3559;3571;
3581;3583;3593;3607;3613;3617;3623;3631;3637;3643;
3659;3671;3673;3677;3691;3697;3701;3709;3719;3727;
3733;3739;3761;3767;3769;3779;3793;3797;3803;3821;
3823;3833;3847;3851;3853;3863;3877;3881;3889;3907;
3911;3917;3919;3923;3929;3931;3943;3947;3967;3989;
4001;4003;4007;4013;4019;4021;4027;4049;4051;4057;
4073;4079;4091;4093;4099;4111;4127;4129;4133;4139;
4153;4157;4159;4177;4201;4211;4217;4219;4229;4231;
4241;4243;4253;4259;4261;4271;4273;4283;4289;4297;
4327;4337;4339;4349;4357;4363;4373;4391;4397;4409;
4421;4423;4441;4447;4451;4457;4463;4481;4483;4493;
4507;4513;4517;4519;4523;4547;4549;4561;4567;4583;
4591;4597;4603;4621;4637;4639;4643;4649;4651;4657;
4663;4673;4679;4691;4703;4721;4723;4729;4733;4751;
4759;4783;4787;4789;4793;4799;4801;4813;4817;4831;
4861;4871;4877;4889;4903;4909;4919;4931;4933;4937;
4943;4951;4957;4967;4969;4973;4987;4993;4999;5003;
5009;5011;5021;5023;5039;5051;5059;5077;5081;5087;
5099;5101;5107;5113;5119;5147;5153;5167;5171;5179;
5189;5197;5209;5227;5231;5233;5237;5261;5273;5279;
5281;5297;5303;5309;5323;5333;5347;5351;5381;5387;
5393;5399;5407;5413;5417;5419;5431;5437;5441;5443;
5449;5471;5477;5479;5483;5501;5503;5507;5519;5521;
5527;5531;5557;5563;5569;5573;5581;5591;5623;5639;
5641;5647;5651;5653;5657;5659;5669;5683;5689;5693;
5701;5711;5717;5737;5741;5743;5749;5779;5783;5791;
5801;5807;5813;5821;5827;5839;5843;5849;5851;5857;
5861;5867;5869;5879;5881;5897;5903;5923;5927;5939;
5953;5981;5987;6007;6011;6029;6037;6043;6047;6053;
6067;6073;6079;6089;6091;6101;6113;6121;6131;6133;
6143;6151;6163;6173;6197;6199;6203;6211;6217;6221;
6229;6247;6257;6263;6269;6271;6277;6287;6299;6301;
6311;6317;6323;6329;6337;6343;6353;6359;6361;6367;
6373;6379;6389;6397;6421;6427;6449;6451;6469;6473;
6481;6491;6521;6529;6547;6551;6553;6563;6569;6571;
6577;6581;6599;6607;6619;6637;6653;6659;6661;6673;
6679;6689;6691;6701;6703;6709;6719;6733;6737;6761;
6763;6779;6781;6791;6793;6803;6823;6827;6829;6833;
6841;6857;6863;6869;6871;6883;6899;6907;6911;6917;
6947;6949;6959;6961;6967;6971;6977;6983;6991;6997;
7001;7013;7019;7027;7039;7043;7057;7069;7079;7103;
7109;7121;7127;7129;7151;7159;7177;7187;7193;7207;
7211;7213;7219;7229;7237;7243;7247;7253;7283;7297;
7307;7309;7321;7331;7333;7349;7351;7369;7393;7411;
7417;7433;7451;7457;7459;7477;7481;7487;7489;7499;
7507;7517;7523;7529;7537;7541;7547;7549;7559;7561;
7573;7577;7583;7589;7591;7603;7607;7621;7639;7643;
7649;7669;7673;7681;7687;7691;7699;7703;7717;7723;
7727;7741;7753;7757;7759;7789;7793;7817;7823;7829;
7841;7853;7867;7873;7877;7879;7883;7901;7907;7919;
7927;7933;7937;7949;7951;7963;7993;8009;8011;8017;
8039;8053;8059;8069;8081;8087;8089;8093;8101;8111;
8117;8123;8147;8161;8167;8171;8179;8191;8209;8219;
8221;8231;8233;8237;8243;8263;8269;8273;8287;8291;
8293;8297;8311;8317;8329;8353;8363;8369;8377;8387;
8389;8419;8423;8429;8431;8443;8447;8461;8467;8501;
8513;8521;8527;8537;8539;8543;8563;8573;8581;8597;
8599;8609;8623;8627;8629;8641;8647;8663;8669;8677;
8681;8689;8693;8699;8707;8713;8719;8731;8737;8741;
8747;8753;8761;8779;8783;8803;8807;8819;8821;8831;
8837;8839;8849;8861;8863;8867;8887;8893;8923;8929;
8933;8941;8951;8963;8969;8971;8999;9001;9007;9011;
9013;9029;9041;9043;9049;9059;9067;9091;9103;9109;
9127;9133;9137;9151;9157;9161;9173;9181;9187;9199;
9203;9209;9221;9227;9239;9241;9257;9277;9281;9283;
9293;9311;9319;9323;9337;9341;9343;9349;9371;9377;
9391;9397;9403;9413;9419;9421;9431;9433;9437;9439;
9461;9463;9467;9473;9479;9491;9497;9511;9521;9533;
9539;9547;9551;9587;9601;9613;9619;9623;9629;9631;
9643;9649;9661;9677;9679;9689;9697;9719;9721;9733;
9739;9743;9749;9767;9769;9781;9787;9791;9803;9811;
9817;9829;9833;9839;9851;9857;9859;9871;9883;9887;
9901;9907;9923;9929;9931;9941;9949;9967;9973;10007;
10009; 10061; 10067; 10069; 10091; 10099; 10139; 10141; 
10159; 10163; 10177; 10253; 10313; 10343; 10477; 10487; 
10601; 10627; 10639; 10651; 10667; 10709; 10723; 10733; 
10753; 10771; 10853; 10861; 10867; 10883; 10937; 10957; 
10973; 11047; 11059; 11087; 11093; 11197; 11243; 11251; 
11257; 11317; 11321; 11329; 11351; 11411; 11443; 11447; 
11489; 11491; 11519; 11519; 11549; 11587; 11617; 11657; 
11777; 11779; 11789; 11807; 11813; 11833; 11839; 11887; 
11933; 11941; 11953; 11971; 11981; 12007; 12011; 12097; 12107; 
12149; 12157; 12227; 12263; 12347; 12373; 12421; 12433; 
12451; 12497; 12503; 12539; 12553; 12583; 12619; 12653; 
12659; 12697; 12757; 12763; 12809; 12853; 12899; 12923; 
12959; 12973; 13003; 13007; 13049; 13103; 13127; 13177; 
13187; 13229; 13291; 13297; 13327; 13397; 13463; 13553; 
13577; 13613; 13709; 13723; 13751; 13763; 13789; 13877; 
13963; 14083; 14083; 14107; 14173; 14177; 14207; 14281; 
14303; 14321; 14323; 14401; 14431; 14437; 14447; 14503; 
14537; 14557; 14593; 14633; 14699; 14717; 14723; 14747; 
14771; 14827; 14879; 14923; 14951; 15091; 15101; 15121; 
15139; 15161; 15173; 15227; 15227; 15277; 15307; 15329; 
15373; 15383; 15391; 15451; 15493; 15581; 15601; 15619; 
15641; 15649; 15727; 15859; 15881; 15907; 15991; 16001; 
16033; 16061; 16087; 16091; 16097; 16111; 16217; 16229; 
16339; 16361; 16369; 16421; 16427; 16481; 16573; 16603; 
16631; 16633; 16649; 16661; 16699; 16759; 16811; 16831; 
16883; 16903; 16927; 16937; 17011; 17027; 17033; 17041; 
17123; 17203; 17207; 17257; 17299; 17317; 17321; 17417; 
17483; 17551; 17597; 17669; 17683; 17747; 17783; 17827; 
17929; 17981; 18043; 18049; 18149; 18199; 18229; 18401; 
18433; 18451; 18461; 18587; 18617; 18701; 18713; 18869; 
18979; 19001; 19141; 19213; 19273; 19387; 19447; 19457; 
19477; 19531; 19541; 19553; 19559; 19577; 19727; 19813; 
19853; 19889; 19963; 19979; 19993; 20011; 20113; 20353; 
20393; 20521; 20549; 20593; 20611; 20693; 20771; 20809; 
20849; 20873; 21017; 21169; 21191; 21317; 21341; 21563; 
21613; 21751; 21851; 21859; 21863; 21937; 21943; 21991; 
21997; 22003; 22153; 22159; 22279; 22349; 22483; 22531; 
22573; 22621; 22691; 22811; 22861; 22907; 23003; 23041; 
23117; 23197; 23269; 23297; 23339; 23417; 23417; 23459; 
23473; 23531; 23537; 23563; 23599; 23633; 23719; 23761; 
23827; 23869; 23879; 23899; 23909; 24023; 24049; 24223; 
24371; 24631; 24677; 24847; 24859; 24919; 25121; 25127; 
25147; 25301; 25391; 25523; 25561; 25847; 25873; 25939; 
26003; 26021; 26119; 26119; 26189; 26237; 26297; 26309; 
26347; 26399; 26459; 26479; 26557; 26597; 26683; 26711; 
26833; 26891; 26893; 26903; 27017; 27143; 27271; 27361; 
27479; 27481; 27749; 27799; 27803; 27817; 27997; 28027; 
28087; 28109; 28111; 28283; 28307; 28387; 28439; 28493; 
28541; 28621; 28621; 28643; 28649; 28663; 28687; 28837; 
29027; 29311; 29339; 29611; 29683; 29753; 29789; 29867; 
29873; 29879; 30091; 30097; 30139; 30259; 30403; 30493; 
30559; 30661; 30707; 30817; 30859; 31079; 31181; 31307; 
31541; 31601; 31649; 31699; 31963; 32119; 32257; 32429; 
32443; 32531; 32609; 32621; 32633; 32801; 32803; 32887; 
33029; 33113; 33161; 33191; 33199; 33203; 33211; 33359; 
33577; 33589; 33601; 33629; 33647; 33703; 33739; 33811; 
33829; 33911; 33941; 34157; 34231; 34337; 34591; 34841; 
35023; 35129; 35393; 35527; 35593; 35747; 35797; 35809; 
35837; 35851; 35869; 35993; 35999; 36209; 36251; 36523; 
36529; 36629; 36653; 36913; 37117; 37223; 37507; 37693; 
37783; 37831; 37889; 38053; 38237; 38327; 38329; 38447; 
38567; 38669; 38677; 38749; 39023; 39227; 39293; 39451; 
39511; 39607; 39749; 40087; 40423; 40529; 40697; 40699; 
40759; 40771; 40829; 40961; 41017; 41081; 41117; 41183; 
41357; 41453; 41641; 41681; 41863; 42169; 42181; 42223; 
42227; 42331; 42349; 42379; 42463; 42611; 42641; 42719; 
42727; 42793; 43133; 43403; 43441; 43651; 43717; 43783; 
43913; 44129; 44839; 44887; 44953; 45077; 45389; 46073; 
46099; 46133; 46141; 46219; 46307; 46619; 46877; 47701; 
47791; 48017; 48023; 48121; 48163; 48299; 48523; 48541; 
48677; 49177; 49201; 49789; 49927; 50077; 50123; 50387; 
50683; 50849; 51131; 51193; 51257; 51607; 51767; 51827; 
51869; 51971; 52027; 52721; 53233; 53239; 53359; 53719; 
53731; 53951; 54001; 54251; 54319; 54409; 54541; 54577; 
54629; 54709; 54779; 55109; 55313; 55399; 55439; 55487; 
55661; 55667; 55901; 56009; 56311; 56519; 56843; 56929; 
57223; 57347; 57529; 57653; 58049; 58073; 58727; 58741; 
58901; 58921; 58963; 59419; 59621; 59723; 60901; 61441; 
62311; 62497; 62659; 62683; 62897; 62971; 63113; 63377; 
63601; 63799; 63839; 63913; 64151; 64381; 64663; 64709; 
64919; 65129; 65203; 65497; 65657; 65731; 65839; 66239; 
66361; 66403; 66617; 66653; 67273; 67601; 68311; 68443; 
68447; 68489; 68491; 68501; 68683; 69019; 69073; 69463; 
69833; 69857; 70949; 70991; 71081; 71147; 71161; 71171; 
71257; 71353; 71807; 71881; 72091; 72221; 72767; 72889; 
73237; 73673; 74093; 74149; 74279; 74353; 74687; 74713; 
74719; 74797; 74857; 74903; 74929; 74941; 76213; 76541; 
77023; 77047; 77191; 77761; 77863; 78007; 78317; 78511; 
78539; 78569; 79427; 79621; 79777; 80071; 80147; 80429; 
80491; 80687; 80831; 82237; 83437; 83591; 83701; 83869; 
83969; 84389; 84481; 85109; 85159; 85223; 85829; 85847; 
86501; 86783; 86923; 86959; 88169; 88469; 88721; 88729; 
88919; 89153; 89657; 89897; 90019; 90617; 90677; 92269; 
92791; 92801; 93077; 93187; 93629; 93703; 93787; 94079; 
94273; 94513; 94873; 96149; 96223; 96269; 97649; 97919; 
98491; 99017; 99131; 99829; 99901; 100361; 100519; 
101281; 102433; 102551; 102667; 102929; 103217; 104009; 
104239; 104369; 104593; 104693; 105499; 106019; 106163; 
106207; 106213; 107269; 107473; 108571; 108803; 108907; 
110939; 110951; 111271; 111487; 111781; 112289; 112859; 
112967; 113081; 113539; 114487; 115733; 115849; 115903; 
115933; 116131; 116593; 117811; 118213; 119159; 120049; 
120767; 121607; 123049; 123379; 124339; 124793; 125243; 
125789; 126751; 128257; 128347; 128693; 128833; 130253; 
130303; 131113; 131249; 132527; 133277; 133303; 133337; 
135589; 137447; 137659; 138577; 139021; 142157; 142217; 
142231; 142711; 143291; 143807; 144311; 144917; 144983; 
145463; 145823; 146023; 146953; 149503; 149531; 153733; 
154159; 155777; 156253; 156631; 157901; 157907; 158357; 
159553; 161753; 162053; 164627; 164881; 167017; 168451; 
169003; 169243; 169489; 170873; 171023; 171167; 172933; 
173183; 173491; 173819; 174917; 175543; 175781; 175853; 
175993; 176977; 177533; 178361; 178613; 179281; 179909; 
180337; 181219; 181499; 182639; 182999; 186247; 186671; 
186757; 188687; 189011; 189307; 189929; 192629; 193243; 
193379; 195407; 195931; 196177; 196993; 197539; 198347; 
203207; 203387; 204161; 205319; 206233; 208291; 208469; 
210247; 212837; 213349; 213557; 213637; 214561; 215183; 
215801; 217681; 218737; 218839; 220019; 220469; 221077; 
222941; 223129; 223303; 224041; 224909; 225461; 225581; 
226769; 227789; 228307; 229561; 229813; 235849; 239597; 
241259; 243391; 243953; 247073; 247781; 250753; 252881; 
253229; 253919; 257069; 260569; 260573; 265541; 266977; 
267139; 269419; 270719; 276869; 277273; 279481; 279967; 
280967; 283583; 284747; 284803; 285101; 289469; 289477; 
293339; 294013; 294053; 296987; 301907; 302723; 309317; 
319321; 320431; 320627; 322901; 325537; 327647; 330821; 
334057; 336223; 338573; 342803; 342889; 347591; 348011; 
353137; 353173; 357661; 357859; 360421; 362203; 371237; 
371321; 371633; 374177; 374293; 379663; 381949; 383549; 
383723; 387587; 398821; 399911; 400949; 401309; 402601; 
402761; 403049; 404449; 406579; 407501; 410833; 415979; 
417719; 429361; 430279; 431441; 435679; 435923; 436627; 
441787; 446389; 446441; 451177; 460697; 460981; 467633; 
470179; 472469; 472543; 473381; 473503; 482017; 485701; 
490577; 492511; 493211; 494519; 496669; 498611; 499801; 
504527; 504857; 506993; 513131; 515153; 522289; 525353; 
526037; 534007; 534403; 534799; 539039; 541577; 545131; 
549817; 553837; 568189; 571399; 573007; 580409; 582767; 
594397; 599477; 602929; 605401; 608347; 608383; 614893; 
623477; 624803; 630737; 639091; 645419; 652237; 655021; 
659231; 662693; 662947; 670037; 674953; 685613; 687931; 
700307; 701299; 703169; 712561; 715417; 715811; 723113; 
723893; 729719; 738383; 739369; 747457; 747871; 761213; 
775861; 792941; 803053; 814013; 814379; 815317; 815621; 
818249; 851041; 853481; 872281; 878413; 882701; 884693; 
888659; 907759; 911903; 914461; 915659; 921197; 932357; 
935423; 970421; 985799; 990841; 1002569; 1014127; 1046053; 
1061287; 1081133; 1121179; 1126831; 1130281; 1148857; 
1179499; 1180631; 1181437; 1188409; 1239751; 1245863; 
1263079; 1265729; 1267183; 1270471; 1292309; 1313839; 
1315231; 1315673; 1348393; 1363099; 1368793; 1371263; 
1389281; 1390703; 1444687; 1445749; 1450231; 1450819; 
1476961; 1511779; 1539997; 1546261; 1557239; 1615963; 
1647497; 1658479; 1688143; 1699679; 1721927; 1759553; 
1760659; 1764089; 1806877; 1808167; 1849723; 1850837; 
1862317; 1877177; 1899377; 1913477; 1967671; 1974659; 
2036009; 2073941; 2152433; 2173747; 2189843; 2254531; 
2266633; 2316331; 2355289; 2372963; 2425043; 2487923; 
2522911; 2549299; 2587997; 2598779; 2619049; 2623279; 
2631071; 2655047; 2662193; 2706787; 2718553; 2742041; 
2883887; 2930747; 2937167; 3053783; 3075881; 3091463; 
3118183; 3134671; 3216233; 3313571; 3331463; 3433273; 
3436403; 3531343; 3643609; 3671119; 3682891; 3843253; 
3876979; 3966871; 4004267; 4016689; 4099699; 4178963; 
4193909; 4250287; 4277443; 4514681; 4619623; 4626203; 
4803119; 5012101; 5044129; 5433287; 5649451; 5734733; 
5975819; 6081013; 6140807; 6333293; 6453023; 6519209; 
6604973; 6633091; 6860929; 7034669; 7348001; 7476467; 
8087333; 8477431; 8535413; 8953859; 9029093; 9241213; 
10032277; 10074763; 11032537; 11164463; 11947531; 12300703;
13168651; 13380937; 13678447; 13864219; 14101613; 14306987; 
15567259; 15614351; 16203931; 16898971; 16967777; 17089109; 
18025589; 18094333; 18243013; 18424487; 18981841; 19548379; 
21063169; 21186677; 21346109; 21827647; 21981319; 22028921; 
23468227; 23618269; 26381071; 26782739; 26981299; 30024301; 
36322193; 50210623; 53661379; 56447371; 56461861; 57314057; 
58365113; 59283979; 63629051; 66123703; 75553553; 76220341; 
77093167; 79243049; 83483419; 84061631; 109494947; 119897951; 
141280949; 151397041; 162137303; 171538231; 182362211; 199168157; 
236097871; 240906709; 255948239; 521797973; 561614303; 645859217; 
706303519; 954281567; 1557996689; 1782464191; 1940328329; 6542016319]%Z.

Definition primes2 := map (fun i => (i, i * i)%Z) primes.

Fixpoint is_pseudo_lprime (n : Z) (l : list (Z * Z)) :=
  match l with 
  | (p, m) :: l1 => 
    if (n <? m)%Z then true else 
    if ((n mod p) =? 0)%Z then false else is_pseudo_lprime n l1
  | _ => true
  end.

Lemma is_pseudo_lprime_correct n l : 
  0 <= n -> (forall i j, In (i, j) l -> 1 < i /\ j = i * i) ->
  is_pseudo_lprime n l = false ->  ~ prime n.
Proof.
intros nP; elim l; simpl; [discriminate| intros [p m] l1 IH Hl].
assert (H : 1 < p /\ m = p * p) by now apply Hl; auto.
destruct H as [pP mSp]; subst m.
case Z.ltb_spec0; [discriminate|].
case Z.eqb_spec.
  intros Hn nLm _ Hp.
  assert (pDn : (p | n)) by now apply Zmod_divide; lia.
  assert (H1 := prime_divisors _ Hp _ pDn).
  assert (p < n) by nia; lia.
intros _ _; apply IH; intros i j H; apply Hl; auto.
Qed.

Fixpoint check_list l := 
  match l with (i, j) :: l1 => 
    if (1 <? i) then if (j =? (i * i)) then check_list l1 else false else false 
  | [::] => true end.

Lemma checklist_ok i j l :
  check_list l = true -> In (i, j) l -> 1 < i /\ j = i * i.
Proof.
revert i j; elim l; simpl; [intros ? ? ? []| intros [i1 j1] l1 IH i j].
case Z.ltb_spec0; try discriminate.
case Z.eqb_spec; try discriminate.
intros H1 H2 H3 [H4|H4].
  now inversion H4; subst; auto.
now apply IH.
Qed.

Definition is_pseudo_prime n := is_pseudo_lprime n primes2.

Lemma is_pseudo_prime_correct n : 
  0 <= n -> is_pseudo_prime n = false ->  ~ prime n.
Proof.
intros nP nPP; apply (is_pseudo_lprime_correct n primes2); auto.
intros i j; apply checklist_ok; compute; auto.
Qed.

Fixpoint lZ_insert (a : Z) (l : list Z) :=
  match l with 
  | b :: l1 => if (a <=? b)%Z then a :: l else b :: lZ_insert a l1
  | _ => [::a]
  end.

Lemma lZ_insert_consr a p l : In a l -> In a (lZ_insert p l).
Proof.
now elim l; [intros H; case H| simpl; intros c l1 IH [Hca|]]; 
    case Z.leb; simpl; auto.
Qed.

Lemma lZ_insert_consl p l : In p (lZ_insert p l).
Proof.
now elim l; simpl; [auto | intros c l1 IH]; case Z.leb; simpl; auto.
Qed.

Lemma lZ_insert_cons a p l : In a (lZ_insert p l) -> a = p \/ In a l.
Proof.
elim l; [intros H; case H; auto| simpl; intros c l1 IH].
case Z.leb; simpl; auto.
- intros [|[|]]; auto.
- intros [|]; auto; case (IH H); auto.
Qed.

Definition add_ltlist i n l l1 := 
  fold_left (fun l z => 
               let v := i * b ^ n + z in 
               if is_pseudo_prime v then lZ_insert v l else l) l l1.

Lemma add_ltlist_subset i n l l1 k : In k l1 -> In k (add_ltlist i n l l1).
Proof.
generalize l1; elim l; simpl; auto.
intros a l2 IH l3 Il3.
case is_pseudo_prime; apply IH; auto.
now apply lZ_insert_consr.
Qed.

Lemma add_ltlist_correct i n l l1 k : 
  0 <= b -> 0 <= i -> 0 <= k ->
  In k l -> prime(i * b ^ n + k) -> In (i * b ^ n + k) (add_ltlist i n l l1).
Proof.
intros bP iP.
generalize l1 k; elim l; simpl; [intros _ _ _ []| intros z l2 IH l3 k3 k3P Ik3 inkP].
destruct Ik3 as [zE | Ink3l2].
  subst z.
  apply add_ltlist_subset.
  generalize (is_pseudo_prime_correct (i * b ^ n + k3)); case is_pseudo_prime.
    now intros; apply lZ_insert_consl.
  now intros H; case H; auto; lia.
now apply IH; auto.
Qed.

Definition lnext (n : Z) (l1 : list Z) := 
  let l := ldigit in 
  fold_left (fun l i => add_ltlist i n l1 l) l [::].

Lemma lnext_correct n l1 k : 
  0 <= n ->
  (forall k, ltprime k -> b ^ n <= k < b ^ (n + 1) -> In k l1) ->
  ltprime k  -> b ^ (n + 1) <= k < b ^ (n + 2) -> In k (lnext (n + 1) l1).
Proof.
intros nP Hl Hlt Hk.
assert (Le : log k = n + 1).
  apply log_inv; try lia; replace (n + 1 + 1) with (n + 2); lia.
pose (k1 := k mod (b ^ (n + 1))).
pose (m := k / (b ^ (n + 1))).
assert (mE : m = digit k (n + 1)).
  unfold digit; rewrite Z.mod_small; auto.
  assert (0 < k).
    now apply GZnZ.p_pos, ltprime_prime.
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; try lia.
  replace b with (b ^ 1) at 2 by lia.
  rewrite <- Z.pow_add_r; try lia.
  now replace (n + 1 + 1) with (n + 2); lia.
assert (mB : 0 < m < b).
  assert (0 <= m < b) by now rewrite mE; apply Z.mod_pos_bound; lia.
  assert (m <> 0); [|lia]; intros mZ.
  assert (n + 1 < log k); [|lia].
  case Hlt; intros [_ Hv] _; rewrite <- Le; apply Hv; try lia.
  now rewrite Le, <- mE.
assert (kE : k = m * b ^ (n + 1) + k1).
  rewrite (Z_div_mod_eq_full k (b ^ (n + 1))).
  now fold m; fold k1; lia.
rewrite kE.
assert (k1Lt : ltprime k1) by now apply ltprime_mod; try lia; auto.
assert (k1P : 0 < k1) by now apply GZnZ.p_pos, ltprime_prime.
fold k1; fold m.
assert (Hk1 : In k1 l1).
  apply Hl.
    now apply ltprime_mod; try lia; auto.
  replace n with (log k1).
    now apply log_correct; try lia.
  unfold k1.
  apply no_zero_digit_log; try lia.
  now case Hlt; auto.
unfold lnext.
assert (mI : In m ldigit).
  now apply ldigit_correct.
revert mI; generalize ([::] : list Z); elim ldigit; simpl; auto.
  now intros l [].
intros a l2 IH l [aE|mIl].
  subst a.
  assert (In (m * b ^ (n + 1) + k1) (add_ltlist m (n + 1) l1 l)).
    apply add_ltlist_correct; try lia; auto.
    now rewrite <- kE; apply ltprime_prime; try lia; auto.
  revert H; generalize (add_ltlist m (n + 1) l1 l).
  elim l2; simpl; auto.
  intros a1 ll1 IH1 ll2 Inll2.
  apply IH1.
  now apply add_ltlist_subset.
now apply IH.
Qed.

End Digits.


Ltac ltprime_tac b := 
repeat (match goal with
  |- ltprime _ ?a => 
       let a' := eval compute in a in 
       let v := constr: (log b a') in 
       let v1 := constr: (a' mod (b ^ v)) in
       let v2 := constr: (a' / (b ^ v)) in
       let v1' := eval compute in v1 in 
       apply (ltprime_ldecompose b (refl_equal _) v1' v2); [compute; auto| | ]
|  |- prime ?a => 
      solve [compute; auto with lprime]
end);
try (apply ltprime_small; [lia|auto with lprime|lia]).

Notation "[ :: ]" := nil (format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::]) (format "[ ::  x1 ]") : seq_scope.


Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.


Definition ltprime_list1 := [:: 2; 3; 5; 7]%Z.

Definition ltprime_list2 := 
  [:: 13;  17;  23;  37;  43;  47;  53;  67;  73;  83;  97].

Definition ltprime_list3 := 
  [:: 113;  137;  167;  173;  197;  223;  283;  313;  317;  337;  347;  353;  
  367;  373;  383;  397;  443;  467;  523; 547;  613;  617;  643;  647;  653;  
  673;  683;  743;  773;  797;  823;  853;  883;  937;  947;  953;  967;  983;
  997].

Definition ltprime_list4 := 
  [:: 1223;  1283;  1367;  1373;  1523;  1613;  1823;  1997;  2113;  2137;
      2347;  2383;  2467;  2617;  2647;  2683;  2797;  2953;  3137;  3167;
      3313;  3347;  3373;  3467;  3547;  3613;  3617;  3643;  3673;  3797;
      3823;  3853;  3947;  3967;  4283;  4337;  4373;  4397;  4523;  4547;
      4643;  4673;  4937;  4967;  5113;  5167;  5197;  5347;  5443;  5647;
      5653;  5683;  5743;  5953;  6113;  6173;  6197;  6317;  6337;  6353;
      6367;  6373;  6397;  6547;  6653;  6673;  6823;  6883;  6947;  6967;
      6983;  6997;  7283;  7523;  7547;  7643;  7673;  7823;  7853;  7883;
      7937;  8167;  8317;  8353;  8443;  8467;  8647;  9137;  9173;  9283;
      9337;  9397;  9467;  9547;  9613;  9643;  9743;  9883;  9967].

Definition ltprime_list5 := 
  [:: 12113;  12347;  12647;  12953;  13313;  13613;  13967;  15443;  15647;
      15683;  16547;  16673;  16823;  16883;  18353;  18443;  21283;  21523;
      21613;  21997;  23167;  24337;  24373;  24547;  24967;  26113;  26317;
      26947;  27283;  27673;  27823;  27883;  29137;  29173;  31223;  32467;
      32647;  32797;  33347;  33547;  33613;  33617;  33797;  33967;  34283;
      34337;  34673;  36353;  36373;  36653;  36947;  36997;  37547;  37643;
      37853;  38167;  38317;  39397;  39883;  42467;  42683;  42797;  42953;
      43313;  43613;  43853;  45197;  45953;  46337;  46997;  48353;  48647;
      49547;  49613;  51283;  51613;  53617;  54547;  54673;  56113;  56197;
      56983;  57283;  57853;  59467;  59743;  61223;  61283;  61613;  62137;
      62347;  62383;  62467;  62617;  62683;  63313;  63347;  63467;  63617;
      63823;  63853;  64283;  64373;  64937;  65167;  65647;  66173;  66337;
      66373;  66653;  66883;  66947;  67523;  67547;  67853;  67883;  68443;
      69337;  69467;  72383;  72467;  72617;  72647;  72797;  72953;  73547;
      73613;  73643;  73673;  73823;  75167;  75347;  75653;  75683;  75743;
      76367;  76673;  76883;  78167;  78317;  78467;  79283;  79337;  79397;
      79613;  79967;  81223;  81283;  81373;  83137;  83617;  84523;  84673;
      84967;  86113;  86197;  86353;  87523;  87547;  87643;  87853;  89137;
      91283;  91367;  91373;  91823;  91997;  92347;  92383;  92467;  92647;
      92683;  93967;  94397;  94547;  95443;  96337;  96353;  96823;  96997;
      97283;  97523;  97547;  97673;  97883;  98317;  98443;  98467;  99137;
      99173;  99397;  99643].

Definition ltprime_list6 := 
[:: 121283;  121523;  121997;  124337;  126317;  132647;  133967;  136373;
    139397;  139883;  162683;  163853;  181283;  184523;  184967;  186113;
    187547;  192347;  192383;  195443;  196337;  213613;  215443;  231223;
    233347;  233617;  234673;  236653;  236947;  237547;  242467;  242797;
    243613;  261223;  264283;  266947;  267523;  272383;  273613;  273643;
    275167;  276673;  276883;  279337;  279397;  279613;  279967;  291367;
    291373;  291997;  294397;  296353;  297523;  299137;  313613;  318443;
    326113;  326947;  327673;  327823;  332467;  336353;  336373;  336653;
    336997;  337853;  338167;  342467;  343313;  345953;  346337;  348353;
    356113;  356197;  357283;  361223;  362137;  362347;  363313;  364373;
    364937;  366173;  367547;  367853;  367883;  368443;  372797;  373613;
    373823;  375743;  378167;  378317;  378467;  379283;  379397;  381223;
    381373;  384673;  387853;  391283;  391367;  391373;  391823;  392347;
    392383;  392467;  392647;  395443;  396353;  396997;  397283;  397547;
    397673;  398467;  399137;  399173;  399643;  421997;  424547;  424967;
    427283;  427883;  429137;  432797;  433967;  439883;  453617;  454547;
    454673;  459467;  462467;  463313;  463823;  465167;  466373;  481373;  
    492467;  492647;  493967;  496997;  498467;  499397;  513313;  516673;
    516883;  534283;  536353;  536947;  537547;  537853;  542467;  542683;
    542797;  543313;  543853;  549547;  563467;  564373;  564937;  566173;
    566653;  566947;  567883;  573673;  576883;  578167;  578317;  578467;
    579283;  579613;  579967;  594397;  597523;  597673;  612113;  613967;
    616547;  616673;  621997;  626113;  626317;  626947;  627673;  629137;
    631223;  632647;  633613;  633797;  633967;  636353;  636653;  636947;
    636997;  638317;  642683;  642797;  642953;  649613;  653617;  656113;
    659467;  661613;  662617;  663823;  663853;  666173;  667547;  667883;
    672953;  673613;  673643;  675347;  675743;  676883;  686197;  686353;
    687523;  691997;  692347;  692467;  692647;  693967;  696823;  697523;
    697673;  721283;  721613;  721997;  723167;  724547;  724967;  727673;
    727823;  729173;  732467;  738317;  739397;  751613;  753617;  759467;
    763823;  766373;  781283;  783137;  786197;  787547;  789137;  792383;
    792647;  793967;  796337;  798443;  812347;  813613;  816547;  816883;
    818353;  833347;  833617;  834283;  837853;  843613;  845197;  846997;
    848647;  861613;  866653;  867547;  869467;  872383;  872647;  872953;
    873643;  875683;  878167;  878467;  879283;  891823;  891997;  894547;
    896353;  912647;  912953;  915683;  918353;  918443;  921523;  924337;
    924967;  926113;  932647;  933613;  933797;  933967;  934673;  946997;
    951283;  956113;  959467;  961283;  961613;  962617;  962683;  964283;
    964373;  965647;  966337;  966373;  966653;  966883;  969467;  973547;
    973823;  975743;  976883;  979283;  979337;  981283;  981373;  983617;
    986113;  986197;  987523;  995443;  997547;  998443].

Definition ltprime_list7 := 
 [:: 1237547;  1261223;  1279337;  1297523;  1326947;  1327673;
 1332467;  1336997;  1338167;  1356197;  1368443;  1384673;
 1516883;  1537853;  1549547;  1563467;  1564373;  1629137;
 1632647;  1633967;  1636997;  1686197;  1686353;  1812347;
 1813613;  1818353;  1833347;  1872953;  1875683;  1891997;
 1896353;  1965647;  1966337;  1987523;  1998443;  2126317;
 2184967;  2186113;  2195443;  2313613;  2336353;  2345953;
 2364937;  2366173;  2373823;  2375743;  2379283;  2379397;
 2396353;  2421997;  2424547;  2424967;  2427883;  2433967;
 2463313;  2465167;  2616673;  2636353;  2642797;  2649613;
 2667883;  2675347;  2723167;  2729173;  2738317;  2759467;
 2763823;  2796337;  2912953;  2961613;  2969467;  2973547;
 2979337;  3136373;  3192347;  3233617;  3243613;  3272383;
 3276883;  3279337;  3291367;  3291373;  3294397;  3299137;
 3327673;  3348353;  3364937;  3372797;  3378317;  3381223;
 3396353;  3396997;  3398467;  3399173;  3433967;  3454673;
 3513313;  3549547;  3563467;  3564937;  3573673;  3578167;
 3578467;  3579613;  3597673;  3616673;  3626113;  3626947;
 3633797;  3636947;  3673613;  3675743;  3692347;  3692467;
 3724967;  3732467;  3739397;  3751613;  3786197;  3787547;
 3834283;  3837853;  3872647;  3879283;  3912647;  3915683;
 3918353;  3918443;  3924337;  3926113;  3932647;  3946997;
 3961283;  3964283;  3966883;  3969467;  3986113;  3987523;
 3995443;  3997547;  4215443;  4233347;  4234673;  4261223;
 4279337;  4279967;  4296353;  4297523;  4326947;  4327823;
 4338167;  4384673;  4392383;  4398467;  4536947;  4537853;
 4542467;  4543313;  4549547;  4563467;  4578467;  4579283;
 4594397;  4597673;  4626113;  4627673;  4632647;  4696823;
 4816883;  4833617;  4837853;  4873643;  4891823;  4921523;
 4933967;  4966373;  4981373;  4986197;  4987523;  5181283;
 5187547;  5196337;  5337853;  5345953;  5367853;  5379397;
 5391367;  5391823;  5396353;  5397283;  5397673;  5424967;
 5427283;  5432797;  5439883;  5462467;  5493967;  5499397;
 5613967;  5661613;  5667547;  5673643;  5675347;  5697673;
 5724967;  5729173;  5753617;  5766373;  5792383;  5915683;
 5934673;  5961283;  5964373;  5979283;  6126317;  6132647;
 6139883;  6184967;  6231223;  6234673;  6237547;  6266947;
 6273643;  6275167;  6279397;  6336373;  6342467;  6346337;
 6367547;  6367853;  6367883;  6368443;  6373613;  6379283;
 6387853;  6391373;  6395443;  6396997;  6397283;  6398467;
 6399137;  6399643;  6421997;  6424547;  6463823;  6492467;
 6499397;  6516673;  6516883;  6536947;  6537547;  6543853;
 6576883;  6579283;  6597673;  6621997;  6626947;  6631223;
 6633967;  6666173;  6673613;  6676883;  6687523;  6692347;
 6721283;  6738317;  6813613;  6878167;  6878467;  6891823;
 6912953;  6915683;  6933967;  6934673;  6946997;  6961613;
 6962617;  6975743;  6981283;  6986197;  6987523;  7233617;
 7236947;  7237547;  7266947;  7291367;  7368443;  7392647;
 7399643;  7542797;  7543853;  7564373;  7567883;  7573673;
 7594397;  7621997;  7626947;  7629137;  7636997;  7659467;
 7662617;  7663823;  7692647;  7693967;  7696823;  7812347;
 7813613;  7816547;  7816883;  7818353;  7861613;  7867547;
 7869467;  7894547;  7896353;  7924967;  7932647;  7981283;
 7983617;  7986113;  7986197;  7995443;  7998443;  8121283;
 8133967;  8184523;  8192383;  8373823;  8391283;  8397283;
 8397547;  8427283;  8432797;  8454673;  8463313;  8481373;
 8493967;  8498467;  8613967;  8616547;  8666173;  8672953;
 8675743;  8676883;  8721997;  8724967;  8727673;  8729173;
 8739397;  8759467;  8787547;  8966653;  8979337;  9121523;
 9139397;  9139883;  9162683;  9184523;  9187547;  9192347;
 9243613;  9267523;  9279337;  9313613;  9318443;  9326113;
 9336373;  9345953;  9356197;  9362137;  9364373;  9366173;
 9391373;  9427883;  9433967;  9454547;  9516673;  9516883;
 9536353;  9537547;  9542683;  9563467;  9564937;  9566173;
 9576883;  9579967;  9594397;  9616547;  9633797;  9636947;
 9636997;  9642683;  9662617;  9663853;  9687523;  9693967;
 9729173;  9751613;  9759467;  9789137;  9812347;  9813613;
 9818353;  9833347;  9833617;  9834283;  9848647;  9861613;
 9866653;  9869467;  9875683;  9878467;  9879283;  9891823;
 9891997;  9915683;  9918353;  9933613;  9951283;  9956113;
 9961283;  9961613;  9962683;  9966883;  9973547;  9979283;
 9979337;  9981373;  9986113].

Definition ltprime_list8 := 
[:: 12184967;  12336353;  12366173;  12375743;  12463313;
 12649613;  12667883;  12723167;  12912953;  12973547;
 13272383;  13276883;  13294397;  13564937;  13578167;
 13692347;  13834283;  13986113;  15187547;  15367853;
 15391823;  15427283;  15439883;  15462467;  15613967;
 15675347;  15697673;  15729173;  15979283;  16237547;
 16266947;  16275167;  16336373;  16387853;  16396997;
 16398467;  16543853;  16576883;  18133967;  18675743;
 18676883;  19536353;  19594397;  19693967;  19818353;
 19861613;  19981373;  21384673;  21563467;  21629137;
 21632647;  21833347;  21987523;  23616673;  23636947;
 23751613;  23946997;  23961283;  23969467;  24384673;
 24536947;  24537853;  24542467;  24543313;  24597673;
 26492467;  26499397;  26673613;  26676883;  26738317;
 26912953;  26934673;  26975743;  27233617;  27266947;
 27291367;  27543853;  27573673;  27626947;  27662617;
 27692647;  29121523;  29427883;  29633797;  29636947;
 29751613;  29918353;  31549547;  31633967;  31686353;
 31891997;  31998443;  32184967;  32313613;  32373823;
 32421997;  32427883;  32649613;  32667883;  32723167;
 32729173;  32738317;  32912953;  32961613;  32969467;
 32973547;  33381223;  33396997;  33398467;  33673613;
 33724967;  33739397;  33787547;  33924337;  34326947;
 34338167;  34542467;  34563467;  34816883;  34891823;
 34987523;  35345953;  35397283;  35424967;  35499397;
 35675347;  35961283;  35979283;  36132647;  36237547;
 36266947;  36275167;  36368443;  36399137;  36424547;
 36516673;  36621997;  36631223;  36666173;  36673613;
 36676883;  36878167;  36878467;  36891823;  36946997;
 36981283;  37237547;  37291367;  37659467;  37812347;
 37869467;  37932647;  37986197;  38979337;  39139883;
 39192347;  39313613;  39336373;  39362137;  39563467;
 39566173;  39616547;  39663853;  39693967;  39879283;
 39918353;  39962683;  39979283;  39979337;  39986113;
 42186113;  42313613;  42366173;  42375743;  42427883;
 42433967;  42642797;  42738317;  42961613;  43279337;
 43294397;  43381223;  43837853;  43995443;  45396353;
 45439883;  45661613;  45934673;  45961283;  46275167;
 46387853;  46398467;  46579283;  46626947;  46986197;
 48184523;  48676883;  48729173;  48966653;  49243613;
 49516673;  49536353;  49537547;  49636997;  49866653;
 49879283;  49951283;  49962683;  49986113;  51332467;
 51336997;  51338167;  51356197;  51686197;  51813613;
 51875683;  51966337;  53364937;  53433967;  53724967;
 53732467;  53912647;  53918443;  53961283;  54215443;
 54398467;  54632647;  54981373;  56373613;  56379283;
 56492467;  56499397;  56666173;  56721283;  56912953;
 56934673;  56961613;  57266947;  57573673;  57621997;
 57692647;  57816883;  57981283;  59184523;  59192347;
 59318443;  59364373;  59366173;  59454547;  59642683;
 61368443;  61516883;  61629137;  61636997;  61812347;
 61813613;  61818353;  61833347;  61965647;  61966337;
 62195443;  62313613;  62336353;  62366173;  62759467;
 62796337;  63243613;  63327673;  63348353;  63364937;
 63381223;  63396353;  63396997;  63399173;  63616673;
 63692347;  63751613;  63786197;  63787547;  63918353;
 63932647;  63966883;  63969467;  63987523;  63995443;
 64234673;  64326947;  64338167;  64579283;  64632647;
 64696823;  64966373;  64986197;  64987523;  65181283;
 65187547;  65345953;  65499397;  65915683;  66139883;
 66234673;  66237547;  66279397;  66346337;  66367853;
 66373613;  66379283;  66391373;  66421997;  66516673;
 66631223;  66673613;  66692347;  66813613;  66962617;
 67236947;  67368443;  67573673;  67629137;  67659467;
 67812347;  67816883;  67869467;  67986197;  67995443;
 68427283;  68613967;  68666173;  68672953;  68675743;
 68724967;  68729173;  68787547;  69121523;  69279337;
 69326113;  69391373;  69516883;  69537547;  69563467;
 69566173;  69633797;  69687523;  69729173;  69833347;
 69915683;  69918353;  69956113;  69986113;  72126317;
 72184967;  72313613;  72345953;  72636353;  72642797;
 72649613;  72969467;  73233617;  73276883;  73398467;
 73549547;  73564937;  73597673;  73626947;  73834283;
 73837853;  73879283;  73924337;  73932647;  75181283;
 75187547;  75667547;  75673643;  75766373;  75964373;
 75979283;  76273643;  76336373;  76399643;  76516673;
 76537547;  76543853;  76576883;  76621997;  76891823;
 76986197;  78184523;  78397283;  78432797;  78481373;
 78672953;  78966653;  78979337;  79516673;  79833617;
 79875683;  79878467;  79951283;  79956113;  79962683;
 79986113;  81332467;  81537853;  81549547;  81629137;
 81833347;  81965647;  83396353;  83433967;  83724967;
 83787547;  83918353;  83969467;  84261223;  84384673;
 84542467;  84563467;  84873643;  84921523;  84966373;
 86132647;  86342467;  86373613;  86391373;  86463823;
 86499397;  86738317;  86912953;  86946997;  86975743;
 87626947;  87693967;  87896353;  87983617;  87995443;
 89121523;  89192347;  89318443;  89616547;  89973547;
 91516883;  91564373;  91891997;  91998443;  92186113;
 92195443;  92366173;  92379283;  92427883;  92463313;
 92465167;  92763823;  92796337;  92961613;  92973547;
 93192347;  93299137;  93364937;  93378317;  93564937;
 93578167;  93616673;  93626947;  93732467;  93834283;
 93879283;  93946997;  94297523;  94384673;  94392383;
 94536947;  94578467;  94594397;  94981373;  95391367;
 95391823;  95462467;  95675347;  95729173;  95766373;
 95792383;  95979283;  96273643;  96346337;  96387853;
 96396997;  96399137;  96399643;  96463823;  96597673;
 96692347;  96878167;  96915683;  96962617;  97236947;
 97291367;  97594397;  97816547;  97861613;  97983617;
 97998443;  98427283;  98672953;  98675743;  98676883;
 98739397;  98966653;  99187547;  99267523;  99336373;
 99356197;  99454547;  99537547;  99633797;  99636997;
 99759467;  99818353;  99951283;  99961613;  99962683;  99979337].


Definition ltprime_list9 := 
[::
124536947; 126934673; 127692647; 132649613; 132723167; 132738317; 133381223;
133924337; 135345953; 135424967; 136266947; 136368443; 136981283; 154981373;
156492467; 157573673; 162195443; 162366173; 163327673; 163381223; 163932647;
163995443; 166516673; 166813613; 166962617; 169516883; 169833347; 169956113;
181332467; 181833347; 181965647; 184873643; 184966373; 186342467; 189121523;
193626947; 195462467; 196273643; 196692347; 198672953; 198739397; 212336353;
212667883; 212973547; 213272383; 215367853; 215391823; 215697673; 218133967;
219536353; 219861613; 231633967; 234542467; 236424547; 236676883; 237237547;
237291367; 237986197; 239192347; 242313613; 242738317; 243381223; 245661613;
246275167; 249951283; 261813613; 263348353; 263616673; 263786197; 263969467;
264326947; 264579283; 264987523; 266139883; 266673613; 267816883; 267986197;
267995443; 269391373; 269633797; 269915683; 273233617; 276516673; 276543853;
276621997; 276986197; 278184523; 278397283; 279516673; 293946997; 294536947;
294981373; 296463823; 297983617; 299633797; 312375743; 312973547; 315187547;
315367853; 315391823; 315427283; 315462467; 315729173; 316266947; 316336373;
316543853; 319693967; 319981373; 323636947; 323961283; 324542467; 329633797;
331686353; 331891997; 332961613; 333396997; 333924337; 335979283; 336516673;
336666173; 337237547; 337659467; 339313613; 339566173; 339616547; 339693967;
339986113; 342738317; 342961613; 346986197; 351813613; 351875683; 351966337;
353433967; 354215443; 354632647; 356666173; 359184523; 359454547; 361629137;
361966337; 363243613; 363399173; 363692347; 364579283; 364696823; 364966373;
364986197; 365187547; 366379283; 366421997; 367573673; 367986197; 368666173;
372126317; 373597673; 373626947; 373837853; 373924337; 375979283; 376399643;
378184523; 378432797; 379962683; 383396353; 386373613; 386391373; 386946997;
389973547; 391564373; 392465167; 393192347; 393834283; 394594397; 395462467;
396273643; 396396997; 396597673; 398675743; 398966653; 399636997; 399759467;
399951283; 421384673; 423751613; 423946997; 424597673; 426738317; 427233617;
427573673; 427662617; 432729173; 433398467; 435397283; 435675347; 439663853;
451332467; 451336997; 451686197; 451813613; 451966337; 453732467; 454398467;
456492467; 456721283; 457266947; 457816883; 457981283; 459642683; 462796337;
466237547; 468675743; 468787547; 469279337; 469326113; 469687523; 469833347;
469986113; 481537853; 484384673; 484921523; 486912953; 489318443; 492186113;
492195443; 492961613; 493564937; 493578167; 495729173; 495979283; 496962617;
499537547; 499636997; 513986113; 515697673; 515729173; 516275167; 516387853;
518676883; 534542467; 536132647; 536676883; 539139883; 539192347; 542642797;
543279337; 546275167; 546579283; 549879283; 561813613; 563399173; 564234673;
564326947; 564696823; 564987523; 566367853; 567629137; 569633797; 572184967;
572313613; 573837853; 576336373; 576537547; 576986197; 578481373; 578672953;
578966653; 578979337; 591998443; 593732467; 594536947; 597594397; 612649613;
612667883; 612973547; 613276883; 613564937; 613578167; 613692347; 615462467;
615697673; 616237547; 616266947; 616396997; 616543853; 619594397; 621987523;
623616673; 623946997; 624536947; 624537853; 626492467; 626499397; 627266947;
627291367; 627543853; 627626947; 629636947; 629751613; 629918353; 631686353;
632373823; 632667883; 632912953; 632961613; 633396997; 634338167; 635424967;
635675347; 635961283; 636631223; 636676883; 636878467; 636946997; 637237547;
637659467; 637812347; 639192347; 639918353; 642186113; 645661613; 646387853;
649951283; 651332467; 651356197; 651686197; 653912647; 653918443; 653961283;
656492467; 656666173; 656721283; 656912953; 656934673; 657816883; 661966337;
663786197; 663995443; 664326947; 664986197; 666391373; 666421997; 666673613;
667812347; 668427283; 669326113; 669729173; 669915683; 672649613; 673834283;
676399643; 676986197; 679833617; 686342467; 686463823; 687693967; 689121523;
691516883; 692961613; 693192347; 693299137; 695729173; 695979283; 696399643;
697594397; 697861613; 697983617; 697998443; 698427283; 699336373; 699537547;
699979337; 724597673; 726738317; 729427883; 732313613; 732738317; 735961283;
736275167; 736621997; 736878167; 739962683; 751338167; 751813613; 756373613;
756499397; 756721283; 757692647; 757981283; 759192347; 759364373; 762195443;
763327673; 768672953; 768729173; 769326113; 769566173; 769833347; 769956113;
781332467; 781549547; 783724967; 784384673; 784563467; 786373613; 787626947;
787983617; 789192347; 789616547; 793578167; 793879283; 795462467; 799537547;
799636997; 813276883; 816387853; 816398467; 816543853; 831549547; 831891997;
833787547; 834816883; 836673613; 837237547; 837659467; 837932647; 839918353;
839979337; 842433967; 842642797; 845439883; 845961283; 848966653; 849243613;
861966337; 863751613; 863786197; 864234673; 867368443; 867629137; 867659467;
867812347; 869121523; 869633797; 869729173; 872345953; 872969467; 873398467;
875667547; 876516673; 876537547; 876986197; 893192347; 893946997; 894392383;
894594397; 897816547; 897998443; 899633797; 899759467; 912366173; 912375743;
913294397; 913564937; 915613967; 916237547; 916396997; 916398467; 916576883;
918133967; 919594397; 919693967; 919981373; 923946997; 926673613; 929636947;
933673613; 933739397; 933924337; 934542467; 934563467; 935397283; 935675347;
936275167; 936516673; 936666173; 936676883; 939336373; 939616547; 942313613;
946275167; 946986197; 948966653; 949636997; 949879283; 949962683; 951813613;
956379283; 956934673; 959192347; 959454547; 961516883; 961813613; 961818353;
961965647; 962366173; 963396997; 963932647; 963969467; 964579283; 966139883;
966692347; 967368443; 968666173; 972969467; 973233617; 973276883; 973398467;
973549547; 973564937; 973837853; 973924337; 975181283; 975667547; 978397283;
979951283; 979956113; 979986113; 983724967; 984563467; 984966373; 986132647;
987983617; 991998443; 993946997; 994297523; 995391367; 995391823; 995729173;
996399137; 998966653; 999267523; 999636997; 999818353; 999962683
].

Definition ltprime_list10 := 
[::
1219861613; 1231633967; 1266139883; 1273233617; 1296463823; 1324542467;
1329633797; 1336516673; 1339693967; 1354632647; 1363243613; 1365187547;
1383396353; 1393834283; 1398675743; 1399951283; 1518676883; 1539139883;
1543279337; 1546275167; 1564326947; 1564696823; 1566367853; 1593732467;
1632373823; 1656666173; 1656912953; 1668427283; 1687693967; 1695729173;
1816543853; 1834816883; 1848966653; 1867368443; 1867659467; 1876986197;
1926673613; 1935675347; 1951813613; 1962366173; 1968666173; 1995391367;
2136981283; 2181833347; 2184966373; 2331891997; 2342738317; 2346986197;
2366421997; 2373924337; 2427233617; 2427662617; 2466237547; 2469326113;
2493578167; 2496962617; 2613564937; 2636631223; 2636946997; 2637659467;
2637812347; 2661966337; 2666391373; 2669915683; 2672649613; 2673834283;
2679833617; 2693192347; 2732313613; 2736621997; 2757981283; 2759364373;
2763327673; 2769326113; 2781332467; 2912366173; 2919693967; 2961965647;
2973924337; 2975181283; 2975667547; 2979951283; 2979956113; 3127692647;
3135345953; 3154981373; 3162366173; 3169833347; 3169956113; 3181332467;
3195462467; 3212336353; 3213272383; 3243381223; 3263616673; 3267995443;
3269915683; 3312375743; 3315391823; 3319693967; 3331686353; 3333924337;
3336666173; 3339313613; 3339616547; 3339693967; 3342738317; 3351966337;
3359454547; 3363243613; 3363399173; 3364696823; 3366421997; 3367986197;
3389973547; 3395462467; 3398675743; 3435397283; 3451813613; 3456721283;
3457816883; 3457981283; 3469279337; 3469687523; 3469833347; 3492961613;
3493564937; 3499636997; 3536676883; 3546275167; 3567629137; 3594536947;
3613578167; 3615462467; 3619594397; 3632961613; 3635675347; 3635961283;
3637237547; 3642186113; 3646387853; 3651356197; 3663786197; 3686342467;
3699537547; 3736621997; 3757692647; 3759364373; 3768672953; 3769566173;
3837659467; 3837932647; 3839979337; 3849243613; 3869633797; 3876537547;
3894594397; 3897816547; 3899633797; 3899759467; 3915613967; 3923946997;
3929636947; 3933673613; 3934563467; 3949962683; 3962366173; 3963932647;
3966139883; 3966692347; 3967368443; 3973276883; 3994297523; 3996399137;
3999267523; 4212336353; 4234542467; 4242313613; 4242738317; 4263969467;
4264579283; 4266139883; 4267986197; 4273233617; 4297983617; 4333396997;
4336516673; 4368666173; 4386946997; 4389973547; 4392465167; 4396396997;
4516387853; 4546579283; 4564326947; 4627266947; 4632667883; 4656666173;
4656721283; 4695729173; 4699336373; 4813276883; 4833787547; 4837237547;
4837932647; 4867812347; 4936275167; 4939336373; 4956379283; 4968666173;
4984966373; 4986132647; 4999636997; 5133381223; 5162366173; 5315729173;
5337237547; 5372126317; 5376399643; 5378184523; 5393192347; 5394594397;
5427573673; 5432729173; 5451813613; 5469326113; 5484384673; 5612973547;
5613276883; 5613564937; 5613578167; 5615697673; 5616543853; 5636631223;
5636676883; 5663786197; 5666391373; 5693192347; 5697983617; 5736878167;
5756373613; 5759192347; 5762195443; 5769833347; 5769956113; 5786373613;
5918133967; 5936676883; 5939616547; 5942313613; 5963969467; 5973924337;
5975181283; 5978397283; 5993946997; 6124536947; 6127692647; 6132649613;
6132738317; 6136266947; 6184966373; 6186342467; 6212336353; 6215391823;
6237237547; 6263348353; 6264987523; 6294536947; 6294981373; 6315462467;
6316336373; 6324542467; 6333396997; 6336516673; 6363692347; 6367986197;
6372126317; 6373837853; 6386391373; 6391564373; 6399759467; 6426738317;
6433398467; 6435675347; 6451332467; 6451966337; 6457266947; 6484921523;
6495729173; 6496962617; 6513986113; 6515729173; 6546275167; 6561813613;
6567629137; 6572313613; 6597594397; 6613692347; 6616266947; 6616543853;
6623616673; 6627291367; 6631686353; 6632667883; 6633396997; 6636946997;
6645661613; 6649951283; 6656666173; 6673834283; 6676399643; 6699537547;
6699979337; 6763327673; 6799636997; 6842642797; 6849243613; 6863786197;
6864234673; 6869729173; 6876986197; 6893192347; 6912366173; 6913294397;
6915613967; 6918133967; 6919594397; 6933673613; 6933924337; 6934542467;
6936275167; 6936516673; 6936666173; 6946986197; 6949879283; 6973837853;
6973924337; 6993946997; 6994297523; 7212336353; 7213272383; 7215367853;
7219861613; 7237237547; 7249951283; 7336516673; 7396597673; 7398675743;
7399951283; 7542642797; 7546579283; 7561813613; 7564234673; 7564326947;
7564696823; 7572313613; 7578481373; 7578979337; 7591998443; 7594536947;
7623946997; 7627266947; 7627543853; 7627626947; 7632373823; 7632961613;
7635675347; 7653918443; 7686463823; 7689121523; 7692961613; 7693299137;
7695979283; 7699336373; 7816387853; 7839918353; 7863786197; 7864234673;
7933924337; 7935675347; 7939336373; 7984563467; 7986132647; 7995391367;
7999962683; 8127692647; 8186342467; 8196692347; 8198739397; 8315187547;
8315427283; 8315729173; 8342738317; 8361629137; 8367986197; 8391564373;
8393192347; 8427573673; 8453732467; 8462796337; 8484384673; 8492961613;
8499636997; 8612649613; 8613276883; 8616237547; 8616266947; 8636676883;
8637237547; 8639192347; 8666391373; 8732738317; 8739962683; 8756499397;
8757981283; 8759192347; 8759364373; 8768672953; 8768729173; 8769326113;
8769566173; 8769956113; 8783724967; 8786373613; 8789616547; 8913564937;
8934563467; 8939616547; 8942313613; 8949962683; 8979951283; 8991998443;
9127692647; 9135345953; 9136266947; 9156492467; 9157573673; 9166516673;
9193626947; 9198739397; 9215367853; 9231633967; 9245661613; 9267986197;
9276543853; 9293946997; 9315462467; 9316543853; 9333924337; 9337659467;
9339986113; 9346986197; 9351813613; 9353433967; 9354632647; 9363243613;
9367573673; 9372126317; 9383396353; 9391564373; 9395462467; 9398966653;
9399636997; 9424597673; 9427233617; 9439663853; 9456492467; 9459642683;
9468787547; 9481537853; 9492961613; 9496962617; 9515697673; 9539192347;
9546579283; 9573837853; 9576537547; 9613564937; 9627626947; 9629751613;
9631686353; 9634338167; 9656934673; 9666391373; 9666421997; 9693192347;
9693299137; 9695979283; 9726738317; 9751338167; 9751813613; 9756721283;
9757692647; 9769326113; 9769956113; 9793578167; 9793879283; 9799636997;
9816387853; 9831891997; 9839979337; 9863786197; 9864234673; 9867659467;
9875667547; 9876537547; 9912366173; 9919981373; 9926673613; 9946275167;
9946986197; 9948966653; 9956379283; 9978397283; 9984563467; 9984966373;
9987983617
].

Definition ltprime_list11 := 
[::
12181833347; 12331891997; 12366421997; 12373924337; 12666391373;
12763327673; 12781332467; 13269915683; 13333924337; 13398675743;
13536676883; 13651356197; 13699537547; 13876537547; 15162366173;
15432729173; 15451813613; 15469326113; 15636631223; 15756373613;
15759192347; 15769833347; 15786373613; 15939616547; 15942313613;
15978397283; 16333396997; 16567629137; 16842642797; 16849243613;
16876986197; 18196692347; 18315187547; 18361629137; 18427573673;
18616237547; 18616266947; 18639192347; 18732738317; 18768729173;
18913564937; 19245661613; 19395462467; 19573837853; 19956379283;
21219861613; 21273233617; 21339693967; 21656666173; 21867368443;
23319693967; 23363399173; 23366421997; 23457816883; 23469833347;
23499636997; 23769566173; 23967368443; 24389973547; 24627266947;
24656666173; 24984966373; 26316336373; 26451966337; 26457266947;
26496962617; 26616266947; 26645661613; 26649951283; 26936666173;
26946986197; 26973837853; 27215367853; 27561813613; 27591998443;
27594536947; 27632961613; 27653918443; 27692961613; 27699336373;
29156492467; 29193626947; 29315462467; 29337659467; 29346986197;
29367573673; 29439663853; 29492961613; 29666421997; 29946986197;
29978397283; 31273233617; 31816543853; 31834816883; 32373924337;
32736621997; 32759364373; 32919693967; 33312375743; 33339616547;
33398675743; 33457816883; 33642186113; 33837659467; 33837932647;
33839979337; 33869633797; 33899633797; 33923946997; 34267986197;
34389973547; 34392465167; 34656666173; 34936275167; 35427573673;
35613276883; 35613564937; 35666391373; 35756373613; 35759192347;
35786373613; 35918133967; 35936676883; 36212336353; 36399759467;
36451966337; 36484921523; 36546275167; 36656666173; 36912366173;
36934542467; 36973837853; 37237237547; 37336516673; 37689121523;
37816387853; 37839918353; 37864234673; 37984563467; 38367986197;
38427573673; 38453732467; 38612649613; 38613276883; 38949962683;
39136266947; 39166516673; 39193626947; 39198739397; 39293946997;
39481537853; 39539192347; 39546579283; 39576537547; 39627626947;
39629751613; 39695979283; 39867659467; 42331891997; 42427662617;
42961965647; 42973924337; 42979956113; 43567629137; 43963932647;
43966692347; 45162366173; 45451813613; 45613578167; 45663786197;
45975181283; 46263348353; 46264987523; 46567629137; 46597594397;
46869729173; 46876986197; 46893192347; 46936275167; 48198739397;
48315729173; 48361629137; 48391564373; 48616237547; 48616266947;
48639192347; 48739962683; 48759364373; 48768729173; 48769566173;
48934563467; 48939616547; 49546579283; 49839979337; 49956379283;
51365187547; 51546275167; 51656912953; 51926673613; 51968666173;
51995391367; 53169833347; 53181332467; 53319693967; 53339313613;
53367986197; 53493564937; 53613578167; 53973276883; 54264579283;
54273233617; 54813276883; 54837932647; 54867812347; 54999636997;
56435675347; 56457266947; 56645661613; 56649951283; 56799636997;
56915613967; 56946986197; 56973837853; 57564326947; 57564696823;
57627266947; 57984563467; 59346986197; 59367573673; 59613564937;
61339693967; 61656912953; 61687693967; 61867659467; 62427662617;
62637659467; 62979951283; 63195462467; 63389973547; 63435397283;
63451813613; 63635675347; 63699537547; 63876537547; 63894594397;
63966139883; 63966692347; 64242313613; 64273233617; 64386946997;
64392465167; 64546579283; 64564326947; 64695729173; 64968666173;
65337237547; 65378184523; 65484384673; 65613578167; 65759192347;
65769956113; 65978397283; 66127692647; 66132738317; 66294536947;
66294981373; 66426738317; 66435675347; 66451966337; 66546275167;
66649951283; 66656666173; 66864234673; 66994297523; 67623946997;
67627626947; 67695979283; 67863786197; 68186342467; 68636676883;
68768729173; 68769326113; 68786373613; 68939616547; 68991998443;
69245661613; 69267986197; 69316543853; 69395462467; 69424597673;
69456492467; 69459642683; 69627626947; 69666391373; 69751813613;
69757692647; 69816387853; 69863786197; 72427233617; 72493578167;
72672649613; 72912366173; 72961965647; 72975667547; 72979956113;
73267995443; 73546275167; 73635961283; 73651356197; 73837932647;
73839979337; 73849243613; 73876537547; 73897816547; 73999267523;
75133381223; 75315729173; 75613276883; 75636631223; 75666391373;
75973924337; 76363692347; 76546275167; 76572313613; 76633396997;
76936275167; 78127692647; 78769956113; 78783724967; 78949962683;
79383396353; 79398966653; 79515697673; 79546579283; 79573837853;
79695979283; 79839979337; 79984563467; 81329633797; 81656666173;
81834816883; 83169956113; 83315391823; 83319693967; 83366421997;
83457981283; 83492961613; 83642186113; 83934563467; 84212336353;
84266139883; 84297983617; 84516387853; 86132738317; 86316336373;
86367986197; 86391564373; 86451332467; 86636946997; 86933673613;
86993946997; 87398675743; 87399951283; 87564234673; 87578481373;
87591998443; 87623946997; 87816387853; 87864234673; 89468787547;
89666421997; 89769326113; 89769956113; 89946986197; 91219861613;
91273233617; 91339693967; 91518676883; 91546275167; 91566367853;
91687693967; 91848966653; 91867659467; 91876986197; 91962366173;
92181833347; 92342738317; 92373924337; 92466237547; 92732313613;
92769326113; 93162366173; 93243381223; 93263616673; 93331686353;
93342738317; 93364696823; 93398675743; 93493564937; 93546275167;
93973276883; 94837932647; 94936275167; 94956379283; 94968666173;
95133381223; 95393192347; 95613276883; 95613578167; 95616543853;
95693192347; 95939616547; 95978397283; 96215391823; 96316336373;
96513986113; 96561813613; 96597594397; 96613692347; 96636946997;
96676399643; 96863786197; 96864234673; 96918133967; 96936516673;
96973924337; 96993946997; 96994297523; 97564326947; 97699336373;
97863786197; 98612649613; 98756499397; 99127692647; 99276543853;
99333924337; 99354632647; 99367573673; 99383396353; 99439663853;
99492961613; 99631686353; 99656934673; 99693299137; 99757692647;
99793578167; 99919981373; 99978397283
].

Definition ltprime_list12 := 
[::
121339693967; 123967368443; 124627266947; 127653918443; 129156492467;
129315462467; 133837659467; 133899633797; 151968666173; 153339313613;
154837932647; 154867812347; 154999636997; 159613564937; 163894594397;
165378184523; 165613578167; 166656666173; 183319693967; 186132738317;
195613276883; 195693192347; 195978397283; 199354632647; 213536676883;
213876537547; 215769833347; 215786373613; 216567629137; 218196692347;
231816543853; 239481537853; 242961965647; 245663786197; 246893192347;
263966139883; 264242313613; 264564326947; 266127692647; 266649951283;
266994297523; 267627626947; 272493578167; 272979956113; 273876537547;
275133381223; 275315729173; 279515697673; 291219861613; 291566367853;
291962366173; 294968666173; 296636946997; 297564326947; 297863786197;
299631686353; 315432729173; 316333396997; 316842642797; 316876986197;
318361629137; 319245661613; 319573837853; 321867368443; 323469833347;
323769566173; 326316336373; 327561813613; 329337659467; 329492961613;
329978397283; 333312375743; 333839979337; 335756373613; 335759192347;
335786373613; 336451966337; 337984563467; 339481537853; 339695979283;
342331891997; 343963932647; 345451813613; 345975181283; 348198739397;
348361629137; 348391564373; 348616237547; 348939616547; 351995391367;
354867812347; 356645661613; 356973837853; 357564326947; 359346986197;
361867659467; 363894594397; 366127692647; 366294981373; 367623946997;
367863786197; 368636676883; 372912366173; 373849243613; 373876537547;
378769956113; 379546579283; 383642186113; 384266139883; 384297983617;
387816387853; 387864234673; 391876986197; 392342738317; 392466237547;
393546275167; 395616543853; 396936516673; 397699336373; 399333924337;
421273233617; 421656666173; 421867368443; 426451966337; 427653918443;
429346986197; 435759192347; 435936676883; 438427573673; 439867659467;
451365187547; 454264579283; 454999636997; 456435675347; 456645661613;
457984563467; 463876537547; 469627626947; 481329633797; 483492961613;
483934563467; 484266139883; 487864234673; 489666421997; 493398675743;
495616543853; 496936516673; 512331891997; 513398675743; 513876537547;
518427573673; 518616237547; 518616266947; 518768729173; 518913564937;
531834816883; 533457816883; 536484921523; 536912366173; 537839918353;
539166516673; 539198739397; 542961965647; 545162366173; 545663786197;
549956379283; 564386946997; 575315729173; 576363692347; 576572313613;
578949962683; 579383396353; 579839979337; 599757692647; 613269915683;
615162366173; 615636631223; 616333396997; 621339693967; 626645661613;
626936666173; 627215367853; 629346986197; 629492961613; 629666421997;
631834816883; 632759364373; 635918133967; 636399759467; 636934542467;
637689121523; 637816387853; 638949962683; 639576537547; 639627626947;
645663786197; 648934563467; 651656912953; 651995391367; 653319693967;
654999636997; 656973837853; 659346986197; 659613564937; 663435397283;
664392465167; 665759192347; 665978397283; 666656666173; 667695979283;
669751813613; 672493578167; 672961965647; 673546275167; 673651356197;
673876537547; 679695979283; 684297983617; 684516387853; 687564234673;
689468787547; 691219861613; 692342738317; 692373924337; 693162366173;
693263616673; 695133381223; 696864234673; 696994297523; 699276543853;
699492961613; 699919981373; 721273233617; 723769566173; 726451966337;
727591998443; 727653918443; 729337659467; 732759364373; 733869633797;
733923946997; 735666391373; 735756373613; 738613276883; 739293946997;
739539192347; 739629751613; 753319693967; 754837932647; 759346986197;
762427662617; 763389973547; 765484384673; 765759192347; 766294536947;
766656666173; 766864234673; 768769326113; 769267986197; 781834816883;
783457981283; 784212336353; 786316336373; 787623946997; 793398675743;
793546275167; 795939616547; 799354632647; 815451813613; 818196692347;
819573837853; 819956379283; 831273233617; 833457816883; 834392465167;
837237237547; 837839918353; 837864234673; 837984563467; 839198739397;
842979956113; 843567629137; 845613578167; 848616266947; 848768729173;
848769566173; 872493578167; 872979956113; 873635961283; 876546275167;
878783724967; 891876986197; 891962366173; 899127692647; 912366421997;
912373924337; 913398675743; 913651356197; 913699537547; 916842642797;
918361629137; 918427573673; 919956379283; 921219861613; 921656666173;
923769566173; 924389973547; 927215367853; 929946986197; 931273233617;
933839979337; 933869633797; 935613276883; 936484921523; 937816387853;
938367986197; 945162366173; 945451813613; 946893192347; 953319693967;
953613578167; 954837932647; 956645661613; 956946986197; 957984563467;
964968666173; 965978397283; 966426738317; 967623946997; 968636676883;
969245661613; 969395462467; 969816387853; 972493578167; 973897816547;
976546275167; 981834816883; 983315391823; 983366421997; 986316336373;
986391564373; 986451332467; 987816387853; 991687693967; 992181833347;
992466237547; 993243381223; 993398675743; 993546275167; 995393192347;
995616543853; 996676399643; 997564326947; 999631686353
].

Definition ltprime_list13 := 
[::
1213536676883; 1213876537547; 1218196692347; 1242961965647; 1291566367853;
1333839979337; 1335759192347; 1357564326947; 1518768729173; 1533457816883;
1639627626947; 1651656912953; 1665759192347; 1692373924337; 1837839918353;
1848768729173; 1872493578167; 1899127692647; 1924389973547; 1956645661613;
1983366421997; 1986391564373; 1995393192347; 2153339313613; 2163894594397;
2183319693967; 2195693192347; 2199354632647; 2316333396997; 2345975181283;
2456435675347; 2487864234673; 2496936516673; 2637816387853; 2663435397283;
2673876537547; 2739293946997; 2739539192347; 2759346986197; 2793546275167;
2799354632647; 2918427573673; 2936484921523; 2967623946997; 2996676399643;
3129156492467; 3129315462467; 3195613276883; 3231816543853; 3242961965647;
3264242313613; 3275315729173; 3316333396997; 3316876986197; 3326316336373;
3339481537853; 3339695979283; 3356973837853; 3357564326947; 3359346986197;
3367863786197; 3387816387853; 3395616543853; 3421656666173; 3427653918443;
3518913564937; 3531834816883; 3533457816883; 3536912366173; 3579383396353;
3615162366173; 3621339693967; 3636934542467; 3639576537547; 3689468787547;
3692342738317; 3693263616673; 3695133381223; 3696864234673; 3723769566173;
3733923946997; 3766656666173; 3766864234673; 3783457981283; 3842979956113;
3912373924337; 3913699537547; 3921219861613; 3931273233617; 3933869633797;
3956946986197; 3976546275167; 3983366421997; 3986391564373; 3986451332467;
3991687693967; 3995393192347; 4231816543853; 4245663786197; 4266127692647;
4279515697673; 4294968666173; 4297863786197; 4321867368443; 4327561813613;
4335786373613; 4518913564937; 4533457816883; 4654999636997; 4656973837853;
4818196692347; 4891876986197; 4933839979337; 4954837932647; 4992181833347;
5165378184523; 5345451813613; 5366127692647; 5421273233617; 5426451966337;
5456435675347; 5463876537547; 5483492961613; 5487864234673; 5613269915683;
5616333396997; 5664392465167; 5669751813613; 5672961965647; 5727653918443;
5966426738317; 6129156492467; 6154837932647; 6154867812347; 6195693192347;
6195978397283; 6215769833347; 6215786373613; 6216567629137; 6218196692347;
6327561813613; 6335786373613; 6339481537853; 6348391564373; 6354867812347;
6373849243613; 6387864234673; 6392342738317; 6454999636997; 6483934563467;
6495616543853; 6518427573673; 6518913564937; 6549956379283; 6579839979337;
6637689121523; 6645663786197; 6739293946997; 6787623946997; 6793398675743;
6795939616547; 6819956379283; 6833457816883; 6848769566173; 6916842642797;
6919956379283; 6921656666173; 6931273233617; 6938367986197; 6965978397283;
6969245661613; 6969395462467; 6986451332467; 6992181833347; 7213536676883;
7216567629137; 7239481537853; 7266994297523; 7267627626947; 7329492961613;
7333839979337; 7335786373613; 7392342738317; 7392466237547; 7513876537547;
7518616237547; 7545162366173; 7549956379283; 7575315729173; 7576572313613;
7629346986197; 7629492961613; 7639576537547; 7653319693967; 7656973837853;
7684516387853; 7696864234673; 7699276543853; 7815451813613; 7837984563467;
7845613578167; 7872979956113; 7924389973547; 7935613276883; 7953613578167;
7957984563467; 7968636676883; 7969245661613; 7969395462467; 7986391564373;
8154867812347; 8195978397283; 8319245661613; 8372912366173; 8421867368443;
8427653918443; 8454264579283; 8463876537547; 8645663786197; 8664392465167;
8673651356197; 8691219861613; 8739293946997; 8762427662617; 8765759192347;
8766294536947; 8786316336373; 8799354632647; 8912366421997; 8996676399643;
9121339693967; 9123967368443; 9291219861613; 9319245661613; 9319573837853;
9326316336373; 9333839979337; 9335756373613; 9348391564373; 9348616237547;
9356645661613; 9361867659467; 9373849243613; 9373876537547; 9384266139883;
9387864234673; 9456645661613; 9463876537547; 9518616266947; 9575315729173;
9576572313613; 9579839979337; 9626645661613; 9629346986197; 9667695979283;
9669751813613; 9684516387853; 9732759364373; 9733923946997; 9753319693967;
9765484384673; 9769267986197; 9781834816883; 9793398675743; 9793546275167;
9872979956113; 9899127692647; 9923769566173; 9933869633797; 9945451813613;
9954837932647; 9964968666173; 9967623946997; 9993243381223; 9995616543853;
9997564326947
].

Definition ltprime_list14 := 
[::
12673876537547; 12967623946997; 13231816543853; 13264242313613;
13986451332467; 15345451813613; 15366127692647; 15421273233617;
15483492961613; 15727653918443; 16215786373613; 16327561813613;
16518427573673; 16579839979337; 16833457816883; 16986451332467;
18195978397283; 18372912366173; 18799354632647; 19384266139883;
19954837932647; 21837839918353; 21848768729173; 21986391564373;
23129156492467; 23129315462467; 23766656666173; 23931273233617;
24279515697673; 24294968666173; 24321867368443; 24933839979337;
26483934563467; 26916842642797; 26931273233617; 27329492961613;
27696864234673; 27969245661613; 29121339693967; 29319245661613;
29348616237547; 29456645661613; 29765484384673; 29769267986197;
29781834816883; 31357564326947; 31899127692647; 32195693192347;
32799354632647; 33231816543853; 33264242313613; 33367863786197;
33427653918443; 33696864234673; 33956946986197; 34231816543853;
34245663786197; 34327561813613; 35613269915683; 35616333396997;
36129156492467; 36335786373613; 36454999636997; 36848769566173;
36938367986197; 37266994297523; 37267627626947; 37392466237547;
37513876537547; 37518616237547; 38463876537547; 38912366421997;
39121339693967; 39348616237547; 39387864234673; 39793546275167;
39933869633797; 39967623946997; 42496936516673; 42739539192347;
42759346986197; 42918427573673; 43639576537547; 46215769833347;
46216567629137; 46833457816883; 46938367986197; 48372912366173;
48463876537547; 48664392465167; 48739293946997; 48765759192347;
49335756373613; 49872979956113; 49995616543853; 51518768729173;
53129315462467; 56129156492467; 56787623946997; 57213536676883;
57267627626947; 57333839979337; 57845613578167; 57935613276883;
57969395462467; 59456645661613; 59669751813613; 61639627626947;
62183319693967; 62316333396997; 62799354632647; 63339695979283;
63359346986197; 63427653918443; 63692342738317; 63986391564373;
65165378184523; 65345451813613; 65366127692647; 65463876537547;
65487864234673; 65672961965647; 66129156492467; 66335786373613;
66354867812347; 66518913564937; 66793398675743; 67239481537853;
67392342738317; 67684516387853; 67872979956113; 67969245661613;
68645663786197; 68664392465167; 68673651356197; 68691219861613;
68739293946997; 69291219861613; 69326316336373; 69348616237547;
69667695979283; 69684516387853; 69733923946997; 69872979956113;
69997564326947; 72637816387853; 72793546275167; 73275315729173;
73357564326947; 73518913564937; 73533457816883; 73842979956113;
73933869633797; 75463876537547; 75727653918443; 76518913564937;
78154867812347; 78195978397283; 78372912366173; 78463876537547;
78739293946997; 78786316336373; 79333839979337; 79384266139883;
79576572313613; 81651656912953; 81872493578167; 83129156492467;
83339481537853; 84294968666173; 84321867368443; 84335786373613;
84992181833347; 86154867812347; 86195693192347; 86195978397283;
87837984563467; 89463876537547; 89669751813613; 89964968666173;
89967623946997; 91335759192347; 91639627626947; 91837839918353;
91983366421997; 92153339313613; 92163894594397; 92195693192347;
92316333396997; 92739293946997; 92793546275167; 92996676399643;
93357564326947; 93639576537547; 93956946986197; 94231816543853;
95483492961613; 95669751813613; 96154867812347; 96645663786197;
96986451332467; 96992181833347; 97545162366173; 97653319693967;
97656973837853; 97935613276883; 98766294536947; 98799354632647;
99335756373613; 99463876537547; 99518616266947; 99769267986197
].

Definition ltprime_list15 := 
[::
121848768729173; 129456645661613; 132195693192347; 136335786373613;
136938367986197; 151518768729173; 156129156492467; 162799354632647;
165487864234673; 165672961965647; 168664392465167; 189463876537547;
212673876537547; 216579839979337; 218799354632647; 231357564326947;
237267627626947; 239793546275167; 242759346986197; 243639576537547;
246215769833347; 249872979956113; 261639627626947; 275463876537547;
275727653918443; 297935613276883; 313231816543853; 315421273233617;
323129315462467; 327969245661613; 329121339693967; 332195693192347;
334245663786197; 349872979956113; 366354867812347; 378372912366173;
394231816543853; 396986451332467; 396992181833347; 399335756373613;
421837839918353; 429121339693967; 435616333396997; 439387864234673;
468645663786197; 469326316336373; 481651656912953; 489463876537547;
493956946986197; 516215786373613; 516579839979337; 533427653918443;
539967623946997; 546215769833347; 546216567629137; 546833457816883;
563427653918443; 573275315729173; 573357564326947; 578739293946997;
579333839979337; 596154867812347; 615345451813613; 616986451332467;
631899127692647; 633231816543853; 633264242313613; 635613269915683;
636335786373613; 637267627626947; 637392466237547; 637513876537547;
639933869633797; 646216567629137; 663359346986197; 665366127692647;
667684516387853; 669684516387853; 678739293946997; 681872493578167;
696154867812347; 696645663786197; 699335756373613; 699769267986197;
724294968666173; 724933839979337; 726483934563467; 726931273233617;
735613269915683; 739387864234673; 763986391564373; 768673651356197;
768691219861613; 784335786373613; 798799354632647; 812967623946997;
816327561813613; 818372912366173; 837266994297523; 891639627626947;
912673876537547; 916579839979337; 923766656666173; 933427653918443;
934231816543853; 937513876537547; 939348616237547; 946938367986197;
957213536676883; 957969395462467; 962316333396997; 963986391564373;
969872979956113; 978195978397283; 997653319693967; 998799354632647;
999769267986197
].

Definition ltprime_list16 := 
[::
1275463876537547; 1399335756373613; 1546215769833347; 1563427653918443;
1635613269915683; 2136938367986197; 2315421273233617; 2429121339693967;
2646216567629137; 2696154867812347; 3315421273233617; 3329121339693967;
3332195693192347; 3394231816543853; 3546216567629137; 3573357564326947;
3726931273233617; 3923766656666173; 3997653319693967; 3999769267986197;
4249872979956113; 4275463876537547; 4546833457816883; 4669684516387853;
4681872493578167; 4699335756373613; 4818372912366173; 4957213536676883;
4957969395462467; 4963986391564373; 4969872979956113; 5136938367986197;
5313231816543853; 5678739293946997; 5934231816543853; 5946938367986197;
6121848768729173; 6132195693192347; 6243639576537547; 6315421273233617;
6334245663786197; 6435616333396997; 6573357564326947; 6633264242313613;
6726483934563467; 6798799354632647; 6812967623946997; 6923766656666173;
6933427653918443; 7216579839979337; 7539967623946997; 7573357564326947;
7579333839979337; 7663359346986197; 7669684516387853; 8162799354632647;
8165672961965647; 8439387864234673; 8493956946986197; 8615345451813613;
8637267627626947; 8997653319693967; 9242759346986197; 9546833457816883;
9573357564326947; 9615345451813613; 9735613269915683; 9763986391564373;
9768673651356197; 9912673876537547; 9946938367986197; 9957969395462467
].

Definition ltprime_list17 := 
[::
12429121339693967; 12646216567629137; 13573357564326947; 18165672961965647;
18997653319693967; 21546215769833347; 24275463876537547; 24963986391564373;
27669684516387853; 34249872979956113; 36334245663786197; 38997653319693967;
39763986391564373; 39768673651356197; 42429121339693967; 51275463876537547;
53315421273233617; 56132195693192347; 56726483934563467; 63315421273233617;
63394231816543853; 63546216567629137; 65678739293946997; 66315421273233617;
66812967623946997; 68637267627626947; 72136938367986197; 75136938367986197;
76812967623946997; 78162799354632647; 78493956946986197; 78615345451813613;
84275463876537547; 84957213536676883; 86315421273233617; 86798799354632647;
92429121339693967; 94669684516387853; 96334245663786197; 97579333839979337;
98615345451813613; 99957969395462467
].

Definition ltprime_list18 :=
[::
165678739293946997; 198615345451813613; 276812967623946997;
312646216567629137; 351275463876537547; 396334245663786197;
397579333839979337; 484957213536676883; 596334245663786197;
624275463876537547; 624963986391564373; 639763986391564373;
663546216567629137; 675136938367986197; 678493956946986197;
686315421273233617; 686798799354632647; 878493956946986197;
918997653319693967; 921546215769833347; 963315421273233617;
984957213536676883; 986315421273233617; 992429121339693967
].

Definition ltprime_list19 := 
[::
1276812967623946997; 3396334245663786197; 3484957213536676883;
4686798799354632647; 5396334245663786197; 6165678739293946997;
6276812967623946997; 6312646216567629137; 6484957213536676883;
6918997653319693967; 7986315421273233617; 8918997653319693967;
8963315421273233617
].

Definition ltprime_list20 := 
[::
15396334245663786197; 18918997653319693967; 36484957213536676883;
66276812967623946997; 67986315421273233617; 86312646216567629137
].

Definition ltprime_list21 := 
[::
315396334245663786197; 367986315421273233617; 666276812967623946997;
686312646216567629137; 918918997653319693967
].

Definition ltprime_list22 :=
[::
5918918997653319693967; 6686312646216567629137; 7686312646216567629137;
9918918997653319693967
].

Definition ltprime_list23 := 
[::
57686312646216567629137; 95918918997653319693967; 96686312646216567629137
].

Definition ltprime_list24 := 
[::
357686312646216567629137
].

Definition ltprime_list25 : list Z :=
[::
].
