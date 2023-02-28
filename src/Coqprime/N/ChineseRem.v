Require Import Arith.
Require Import Wf_nat.
Require Import ZArith.
Require Import Peano_dec.
Require Import ZArith_dec.
Require Import NatAux ZCAux ZCmisc ZSum Pmod Ppow.

Open Scope nat_scope.

(* *  Compatibility Lemmas (to remove someday)

   These lemmas are deprecated since 8.16. 
   We re-introduce them, since they occur in non-trivial terms in the 
   original proof scripts.

 *)

Lemma mult_O_le : forall n m : nat, m = 0%nat \/ (n <= m * n)%nat.
Proof.
   destruct m. 
   - now left. 
   - right; replace n with (1 * n)%nat  at 1. 
     apply Nat.mul_le_mono_r; auto with arith. 
     now rewrite Nat.mul_1_l. 
Qed. 


Lemma le_plus_trans (n m p : nat) : (n <= m)%nat -> (n <= m + p)%nat.
Proof. 
 intro H; apply Nat.le_trans with m; [assumption | apply Nat.le_add_r].
Qed.

Lemma ltgt1: forall a b : nat, (a < b -> b > 0)%nat. 
Proof. lia. Qed.

Lemma minus1: forall a b c : Z, (a - c)%Z = (b - c)%Z -> a = b.
Proof. lia. Qed.

Lemma minusS : forall a b : nat, b - a = S b - S a.
Proof. lia. Qed.

Lemma div_trans (p q r: nat) : divide p q -> divide q r -> divide p r.
Proof. intros [x Hx] [y Hy]; exists (x * y); lia. Qed.

Lemma div_refl p : divide p p.
Proof. exists 1; now rewrite Nat.mul_1_r. Qed.

Fixpoint prod (n:nat) (x: nat -> nat) :=
  match n with
    O => 1%nat
  | S p => x p * prod p x
  end.

Lemma prodBig1 :
 forall (n : nat) (x : nat -> nat),
 (forall z : nat, z < n -> x z > 0) -> prod n x > 0.
Proof.
  induction n as [| n Hrecn].
  - intros x H; simpl in |- *; apply Nat.lt_succ_diag_r.
  - intros x H; simpl in |- *; apply Nat.mul_pos_pos.
    + apply H; apply Nat.lt_succ_diag_r.
    + apply Hrecn; intros; now apply H, Nat.lt_lt_succ_r.
Qed.

Lemma prodExtensional :
  forall (n : nat) (x1 x2 : nat -> nat),
    (forall z : nat, z < n -> x1 z = x2 z) -> prod n x1 = prod n x2.
Proof.
  induction n as [| n Hrecn].
  - intros; reflexivity. 
  - intros x1 x2 H; simpl in |- *; replace (x1 n) with (x2 n).
    + f_equal; auto.
    + rewrite (H n); auto. 
Qed.

Definition factorial (n : nat) : nat := prod n S.



(** *  Relative primality *)

(** A [nat] version of [rel-prime] *)

Definition CoPrime (a b : nat) := Zis_gcd (Z.of_nat a) (Z.of_nat b) 1%Z.

Lemma coPrimeSym: forall a b : nat, CoPrime a b -> CoPrime b a.
Proof. intros. now apply Zis_gcd_sym. Qed.

Lemma gcd_bezout_nat: forall (x y d : nat),
  (x > 0)%nat ->
  Zis_gcd (Z_of_nat x) (Z_of_nat y) (Z_of_nat d) ->
  Bezout (Z_of_nat x) (Z_of_nat y)  (Z_of_nat d) .
Proof.
  intros x y d H H0; destruct (Zis_gcd_bezout (Z.of_nat x)
                                 (Z.of_nat y) (Z.of_nat d) H0)
                              as [u v ?]; now exists u v.
Qed.

Lemma coPrimeMult : 
  forall a b c : nat, CoPrime a b -> divide a (b * c) -> divide a c.
Proof.
  intros ? ? ? H H0; unfold CoPrime in H.
  destruct a as [| a].
  - (* a = 0 *)
    induction H0 as (x, H0).
    cbn in H0; rewrite Nat.eq_mul_0 in H0. (* b = O \/ c = O *)
    destruct H0 as [H1 | H1].
    + rewrite H1 in H; simpl in H.
      inversion H. clear H H0 H1 H2.
      assert (2 | 0). { exists 0%Z. auto. }
      destruct (H3 _ H H). nia.
    + rewrite H1; now exists 0%nat. 
  - assert (H1: (S a > 0)%nat) by apply Nat.lt_0_succ.
    pose (gcd_bezout_nat (S a) b 1 H1 H) as W.
    inversion W; clear W; destruct H0 as [x1 H0].
    assert (1 * Z.of_nat c =
              Z_of_nat (S a) * (u * Z.of_nat c + Z.of_nat x1 * v))%Z.
    { rewrite (Z.mul_comm (Z.of_nat (S a))).
      rewrite  Z.mul_add_distr_r.
      rewrite (Z.mul_comm (u * Z.of_nat c)).
      rewrite (Z.mul_comm (Z.of_nat x1 * v)).
      repeat rewrite Z.mul_assoc.
      rewrite <- Znat.inj_mult.
      rewrite <- H0.
      rewrite Znat.inj_mult.
      rewrite (Z.mul_comm (Z.of_nat b)).
      rewrite <- (Z.mul_assoc (Z.of_nat c)).
      rewrite (Z.mul_comm (Z.of_nat c)).
      rewrite <- Z.mul_add_distr_r.
      nia. }
    rewrite Zmult_1_l in H3.
    assert (Z.divide (Z.of_nat (S a)) (Z.of_nat c)).
    { exists (u * Z.of_nat c + Z.of_nat x1 * v)%Z.
      now rewrite Z.mul_comm at 1. }
    clear H2 H3 u v.
    rewrite <- (Znat.Zabs2Nat.id (S a)).
    rewrite <- (Znat.Zabs2Nat.id c).
    repeat rewrite Zabs2Nat.id. destruct H4. exists (Z.to_nat x). nia.
Qed.

Lemma coPrimeMult2 : 
  forall a b c : nat,
    CoPrime a b -> divide a c -> divide b c -> divide (a * b) c.
Proof.
  intros a b c H H0 [x H1]; assert (H2: divide a x).
  { eapply coPrimeMult with (1:= H); now rewrite <- H1. }
  destruct H2 as [x0 H2]; exists x0; subst; ring.
Qed.


Lemma chRem2 : 
  forall b1 r1 b2 r2 q : Z,
    (0 <= r1)%Z ->
    (0 <= r2)%Z ->
    (r1 < q)%Z -> (r2 < q)%Z -> (b1 * q + r1)%Z = (b2 * q + r2)%Z ->
    r1 = r2.
Proof.
  intros * H H0 H1 H2 H3.
  assert (H4: ((b1 - b2) * q)%Z = (r2 - r1)%Z) by
    (rewrite  Z.mul_sub_distr_r; lia).
  induction (Zle_or_lt 0 (b1 - b2)) as [H5 | H5].
  induction (Zle_lt_or_eq _ _ H5) as [H6 | H6].
  assert (H7: (1 <= b1 - b2)%Z).
  { replace 1%Z with (Z.succ 0) by reflexivity. 
     now apply Zlt_le_succ.
  }
  assert (H8: (q <= r2 - r1)%Z).
  { replace q with (1 * q)%Z by apply Zmult_1_l.
    - rewrite <- H4.
       apply Zmult_le_compat_r.
      + assumption.
      + eapply Z.le_trans.
        * apply H.
        * now apply Zlt_le_weak.
  }
  set (A1 := Zplus_lt_le_compat r2 q (- r1) 0 H2) in *.
  assert (H9: (r2 - r1 < q)%Z).
  { replace q with (q + 0)%Z by ( now rewrite <- Zplus_0_r_reverse). 
    unfold Zminus in |- *; apply A1.
    eapply (fun a b : Z => Zplus_le_reg_l a b r1).
    rewrite Zplus_opp_r.
    now rewrite <- Zplus_0_r_reverse.
  }
  destruct (Zle_not_lt q (r2 - r1)).
  assumption.
  assumption.
  rewrite <- H6, Z.mul_comm in H4.
  rewrite <- Zmult_0_r_reverse in H4.
  rewrite <- (Zplus_opp_r r2) in H4.
  unfold Zminus in H4.
  apply Z.opp_inj.
  symmetry  in |- *; eapply Zplus_reg_l.
  apply H4.
  assert (H6: (1 <= b2 - b1)%Z).
  { replace 1%Z with (Z.succ 0) by reflexivity.
    apply Zlt_le_succ.
    apply (Zplus_lt_reg_l 0 (b2 - b1) b1).
    rewrite Zplus_minus.
    rewrite <- Zplus_0_r_reverse.
    apply (Zplus_lt_reg_l b1 b2 (- b2)).
    rewrite Zplus_opp_l.
    rewrite Zplus_comm.
    now unfold Zminus in H5.
  }
  assert (H7: ((b2 - b1) * q)%Z = (r1 - r2)%Z) by
    ( rewrite Z.mul_sub_distr_r ; lia ).
  assert (H8:(q <= r1 - r2)%Z).
  { replace q with (1 * q)%Z.
    rewrite <- H7.
    apply Zmult_le_compat_r.
    assumption.
    eapply Z.le_trans.
    apply H.
    apply Zlt_le_weak.
    assumption.
    apply Zmult_1_l.
  }
  set (A1 := Zplus_lt_le_compat r1 q (- r2) 0 H1) in *.
  assert (H9:(r1 - r2 < q)%Z).
  { replace q with (q + 0)%Z.
    unfold Zminus in |- *.
    apply A1.
    eapply (fun a b : Z => Zplus_le_reg_l a b r2).
    rewrite Zplus_opp_r.
    now rewrite <- Zplus_0_r_reverse.
    now rewrite <- Zplus_0_r_reverse.
  }
  destruct (Zle_not_lt q (r1 - r2)); assumption.
Qed.

(** Imported by PRrepresentable *)

Lemma uniqueRem :
 forall r1 r2 b : nat,
 b > 0 ->
 forall a : nat,
 (exists q : nat, a = q * b + r1 /\ b > r1) ->
 (exists q : nat, a = q * b + r2 /\ b > r2) -> r1 = r2.
Proof.
  intros ? ? ? H a [x [H0 H2]] [x0 [H1 H3]].
  assert (x = x0). { nia. } nia.
Qed.

(** Imported by PRRepresentable *)
Lemma div_eucl :
 forall b : nat,  b > 0 ->
 forall a : nat, {p : nat * nat | a = fst p * b + snd p /\ b > snd p}.
Proof.
  intros b H a; apply (gt_wf_rec a).
  intros n H0 .
  destruct (le_lt_dec b n) as [Hle | Hlt].
  - assert (n > n - b).
    { unfold gt in |- *; apply Nat.sub_lt; assumption. }
    destruct (H0 _ H1) as [[a1 b0] p].
    simpl in p;  exists (S a1, b0); simpl in |- *.
    destruct p as (H2, H3).
    split; [| assumption].
    + rewrite <- Nat.add_assoc, <- H2.
      now rewrite Nat.add_comm, Nat.sub_add. 
   -  exists (0, n); simpl in |- *; now split.
Qed.


Lemma chRem1 : 
 forall b : nat,  b > 0 -> forall a : Z,
     {p : Z * nat | snd p < b /\
                      Z.of_nat (snd p) = (fst p * Z.of_nat b + a)%Z}.
Proof.
  intros b H a.
  assert
    (H0: forall a' : Z,
        (a' >= 0)%Z ->
        {p : Z * nat | snd p < b /\
                         Z.of_nat (snd p) =
                           (fst p * Z.of_nat b + a')%Z}).
  { intros a' H0; set (A := Z.to_nat a') in *.
    induction (div_eucl b H A) as [x p].
    destruct x as (a0, b0).
    exists ((- Z.of_nat a0)%Z, b0).
    destruct p as (H1, H2).
    split.
    - apply H2.
    - rewrite <- (Z2Nat.id a'). 
      + simpl fst ; simpl snd. 
        rewrite Zopp_mult_distr_l_reverse.
        rewrite Z.add_comm.
        fold (Z.of_nat (Z.to_nat a') - Z.of_nat a0 * Z.of_nat b)%Z
          in |- *.
        apply Zplus_minus_eq.
        rewrite <- Znat.inj_mult.
        rewrite <- Znat.inj_plus.
        apply Znat.inj_eq.
        apply H1.
      + auto.
        now rewrite <- Z.ge_le_iff.
  }
  destruct (Z_ge_lt_dec a 0) as [g | l].
  + apply H0; assumption.
  + assert (a + Z.of_nat b * - a >= 0)%Z.
    induction b as [| b Hrecb].
    * elim (Nat.lt_irrefl _ H).
    * rewrite Znat.inj_S.
      rewrite Z.mul_comm.
      rewrite <- Zmult_succ_r_reverse.
      fold (- a * Z.of_nat b - a)%Z in |- *.
      rewrite Zplus_minus.
      replace 0%Z with (0 * Z.of_nat b)%Z.
      apply Zmult_ge_compat_r.
      rewrite (Zminus_diag_reverse a).
      rewrite <- (Zplus_0_l (- a)).
      unfold Zminus in |- *; apply Z.le_ge.
      apply Zplus_le_compat_r.
      now apply Zlt_le_weak.
      change  0%Z with (Z.of_nat 0).
      apply Znat.inj_ge.
      unfold ge in |- *.
      apply Nat.le_0_l.
      auto.
    * destruct  (H0 _ H1) as [(a0,b1) [H2 H3]].
      exists ((a0 - a)%Z, b1); split.
      -- simpl in |- *; apply H2.
      -- cbv beta iota zeta delta [fst snd] in H3 |- *.
         rewrite H3,  (Zplus_comm a), Zplus_assoc.
         apply Zplus_eq_compat.
         rewrite Zmult_minus_distr_r.
         unfold Zminus in |- *.
         apply Zplus_eq_compat.
         reflexivity.
         rewrite Z.mul_comm.
         apply Zopp_mult_distr_l_reverse.
         reflexivity.
Qed.

Lemma euclid_gcd1 :
  forall (d : nat) (x y q r : Z),
    Zis_gcd x y (Z.of_nat d) -> x = (q * y + r)%Z ->
    Zis_gcd r y (Z.of_nat d).
Proof.
  intros. rewrite H0 in H. clear H0 x.
  replace r with  (y * - q + (q * y + r))%Z by lia.
  apply Zis_gcd_sym. 
  apply Zis_gcd_for_euclid2; auto with zarith.
Qed.

Lemma euclid_gcd (d1 d2 : nat) (x y q r : Z) :
   x = (q * y + r)%Z -> Zis_gcd x y (Z.of_nat d1) ->
   Zis_gcd r y (Z.of_nat d2) -> d1 = d2.
Proof.
   intros H H0 H1 ; pose proof (euclid_gcd1 d1 x y q r H0 H) as H2.
   pose proof (Zis_gcd_unique r y _ _ H2 H1); lia.
Qed.

Lemma gcd_lincomb_nat_dec :
 forall x y d : nat,
 x > 0 ->
 Zis_gcd (Z.of_nat x) (Z.of_nat y) (Z.of_nat d) ->
 {a : Z * Z |
   Z.of_nat d = (Z.of_nat x * fst a + Z.of_nat y * snd a)%Z}.
Proof.
   intro x; apply (lt_wf_rec x); intros X IH. intros y d H H0.
   elim (div_eucl X H y).
   intro z; elim z.
   intros q r; clear z; simpl in |- *.   
   case r.
   (* case r = 0 *)
   - intros; induction p as (H1, H2).
     rewrite <- plus_n_O in H1.
     exists (1%Z, 0%Z).
     simpl fst; simpl snd. 
     rewrite <- Zmult_0_r_reverse; rewrite <- Zplus_0_r_reverse.
     rewrite Z.mul_comm. rewrite Zmult_1_l.
     apply Znat.inj_eq.
     apply (euclid_gcd d X (Z.of_nat y) (Z.of_nat X) (Z.of_nat q) 0).
     rewrite <- Zplus_0_r_reverse; rewrite <- Znat.inj_mult;
       apply Znat.inj_eq; assumption.
     apply Zis_gcd_sym; assumption.
     constructor.
     + exists 0%Z. auto.
     + exists 1%Z. lia.
     + auto.
   - (* case r > 0 *)
   intros r1 [H1 H2].
   elim (IH (S r1) H2 X d).
   + intro z; elim z.
     intros delta gamma; clear z.
     simpl fst; simpl snd.
   intros p. 
   exists ((gamma - Z.of_nat q * delta)%Z, delta).
   simpl fst; simpl snd.
   rewrite p, H1.
   unfold Zminus in |- *; rewrite Zmult_plus_distr_r.
   rewrite Znat.inj_plus; rewrite Zmult_plus_distr_l.
   rewrite Znat.inj_mult; rewrite <- Zopp_mult_distr_l_reverse.
   rewrite (Z.mul_assoc (Z.of_nat X)).
   rewrite (Z.mul_comm (Z.of_nat X) (- Z.of_nat q)).
   rewrite Zopp_mult_distr_l_reverse.
   rewrite Zopp_mult_distr_l_reverse.
   rewrite <- (Z.add_assoc (Z.of_nat X * gamma)).
   rewrite <- Znat.inj_mult.
   rewrite (Z.add_assoc (- (Z.of_nat (q * X) * delta))). 
   rewrite Zplus_opp_l. simpl in |- *. apply Z.add_comm.
   + auto with arith. 
   + apply (euclid_gcd1 d (Z.of_nat y) (Z.of_nat X) (Z.of_nat q) (Z.of_nat (S r1))).
     * apply Zis_gcd_sym; assumption.
     * rewrite <- Znat.inj_mult; rewrite <- Znat.inj_plus;
          apply Znat.inj_eq; assumption.
Qed.

Lemma chineseRemainderTheoremHelp :
  forall x1 x2 : nat,
    CoPrime x1 x2 ->
    forall (a b : nat) (pa : a < x1) (pb : b < x2),
      a <= b ->
      {y : nat |
        y < x1 * x2 /\
          a = snd (proj1_sig (div_eucl x1 (ltgt1 _ _ pa) y)) /\
          b = snd (proj1_sig (div_eucl x2 (ltgt1 _ _ pb) y))}.
Proof.
  intros ? ? H a b pa pb H0. unfold CoPrime in H.
  replace 1%Z with (Z.of_nat 1) in H by auto.
  destruct (gcd_lincomb_nat_dec _ _ _ (ltgt1 _ _ pa) H)
    as [(a0,b0) p]. 
  set (A := Z.of_nat a) in *.
  set (B := Z.of_nat b) in *.
  set (X1 := Z.of_nat x1) in *.
  set (X2 := Z.of_nat x2) in *.
  set (y := (a0 * (B - A))%Z) in *.
  set (z := (b0 * (A - B))%Z) in *.
  set (d := (A + X1 * y)%Z) in *.
  assert (d = (B + X2 * z)%Z).
  unfold d in |- *; simpl in p.
  apply minus1 with (X2 * z)%Z.
  rewrite (Z.add_comm B).
  rewrite Zminus_plus.
  unfold z in |- *.
  replace (A - B)%Z with (- (B - A))%Z.
  unfold Zminus in |- *.
  rewrite (Z.mul_comm b0).
  rewrite Zopp_mult_distr_l_reverse.
  rewrite (Z.mul_comm X2).
  rewrite Zopp_mult_distr_l_reverse.
  rewrite Z.opp_involutive.
  unfold y in |- *.
  rewrite <- (Z.mul_assoc (B + - A)).
  rewrite (Z.mul_comm (B + - A)).
  rewrite (Z.mul_assoc X1).
  rewrite (Z.mul_comm b0).
  rewrite <- Z.add_assoc.
  rewrite <- Zmult_plus_distr_l.
  rewrite <- p.
  rewrite Z.mul_1_l.
  fold (B - A)%Z in |- *.
  apply Zplus_minus.
  unfold Zminus in |- *.
  rewrite Zopp_plus_distr.
  rewrite Z.add_comm.
  rewrite Z.opp_involutive.
  reflexivity.
  assert (H2: x1 * x2 > 0).
  { change 0 with (0 * x2).
    unfold gt in |- *; rewrite Nat.mul_comm.
    rewrite (Nat.mul_comm x1).
    induction x2 as [| x2 Hrecx2].
    elim (Nat.nlt_0_r _ pb).
    rewrite <- (Nat.mul_lt_mono_pos_l (S _)). 
    fold (x1 > 0) in |- *.
    eapply ltgt1.
    apply pa.
    auto.
    auto with arith. 
  }
  destruct (chRem1 _ H2 d) as [(a1, b1) [H3 H4]].
  exists b1; split.
  apply H3.
  cbv beta iota zeta delta [snd fst] in H4, p. 
  split.
  induction (div_eucl x1 (ltgt1 a x1 pa) b1).
  induction x as (a2, b2).
  simpl in |- *.
  induction p0 as (H5, H6).
  cbv beta iota zeta delta [snd fst] in H5.
  rewrite H5 in H4.
  unfold d in H4.
  unfold A, X1 in H4.
  assert (Z.of_nat a = Z.of_nat b2).
  { eapply chRem2; try lia.
    + apply Znat.inj_lt.
      apply pa.
    + apply Znat.inj_lt.
      apply H6.
    + rewrite Znat.inj_plus in H4.
      repeat rewrite Znat.inj_mult in H4.
      symmetry  in |- *.
      rewrite (Z.add_comm (Z.of_nat a)) in H4.
      rewrite Z.add_assoc in H4.
      rewrite Z.mul_assoc in H4.
      rewrite (Z.mul_comm a1) in H4.
      rewrite <- (Z.mul_assoc (Z.of_nat x1)) in H4.
      rewrite <- Zmult_plus_distr_r in H4.
      rewrite (Z.mul_comm (Z.of_nat x1)) in H4.
      apply H4. }
  lia.
  induction (div_eucl x2 (ltgt1 b x2 pb) b1).
  simpl in |- *.
  induction x as (a2, b2).
  cbv beta iota zeta delta [snd fst] in p0.
  induction p0 as (H5, H6).
  rewrite H5 in H4.
  rewrite H1 in H4.
  unfold B, X2 in H4.
  simpl. assert (Z.of_nat b = Z.of_nat b2).
  { eapply chRem2; try lia.
    + apply Znat.inj_lt.
      apply pb.
    + apply Znat.inj_lt.
      apply H6.
    + rewrite Znat.inj_plus in H4.
      repeat rewrite Znat.inj_mult in H4.
      symmetry  in |- *.
      rewrite (Z.add_comm (Z.of_nat b)) in H4.
      rewrite Z.mul_assoc in H4.
      rewrite Z.add_assoc in H4.
      rewrite (Z.mul_comm a1) in H4.
      rewrite (Z.mul_comm (Z.of_nat x2)) in H4.
      rewrite <- Zmult_plus_distr_l in H4.
      apply H4. }
  lia.
Qed.

Lemma chineseRemainderTheorem :
 forall x1 x2 : nat,
 CoPrime x1 x2 ->
 forall (a b : nat) (pa : a < x1) (pb : b < x2),
 {y : nat |
 y < x1 * x2 /\
 a = snd (proj1_sig (div_eucl x1 (ltgt1 _ _ pa) y)) /\
 b = snd (proj1_sig (div_eucl x2 (ltgt1 _ _ pb) y))}.
Proof.
  intros ? ? H a b pa pb.
  destruct (le_lt_dec a b).
  - apply chineseRemainderTheoremHelp; assumption.
  - assert (H0: b <= a) by (now apply Nat.lt_le_incl).
    assert (H1: CoPrime x2 x1) by (now apply coPrimeSym).
    induction (chineseRemainderTheoremHelp _ _ H1 b a pb pa H0)
                as [x [H2 [H3 H4]]].
    exists x.
    split.
    + now rewrite Nat.mul_comm.
    + split; assumption.
Qed.



Lemma coPrime1 : forall a : nat, CoPrime 1 a.
Proof.
  split.
  - simpl. exists 1%Z. auto.
  - exists (Z.of_nat a); lia.
  - intros e [H H0] [H1 H2].
    simpl in H0. symmetry in H0.
    assert (H >= 0 \/ H <= 0)%Z by lia. destruct H3.
    + pose proof (Zmult_one _ _ H3 H0). subst. exists 1%Z. lia.
    + assert (- H >= 0)%Z by lia.
      replace (H * e)%Z with ((- H) * (- e))%Z in H0 by lia.
      pose proof (Zmult_one _ _ H4 H0). rewrite H5 in H0.
      exists (-1)%Z. lia.
Qed.

Lemma coPrimeMult3 (a b c: nat):
  a > 0 -> b > 0 -> c > 0 ->
  CoPrime a c -> CoPrime b c -> CoPrime (a * b) c.
Proof.
  intros H H0 H1 H2 H3;
    assert (H4: Bezout (Z.of_nat a) (Z.of_nat c) (Z.of_nat 1)).
  { apply gcd_bezout_nat.
    assumption.
    apply H2.
  }
  assert (H5: Bezout (Z.of_nat b) (Z.of_nat c) (Z.of_nat 1)).
  { apply gcd_bezout_nat.
    assumption.
    apply H3.
  }
  inversion H4 as [x x0 H6]; clear H4.
  inversion H5 as [x1 x2 H7]; clear H5.
  split.
  - exists (Z.of_nat (a * b)). lia.
  - exists (Z.of_nat c). lia.
  - intros e [H8 H9].
    set (A := Z.of_nat a) in *.
    set (B := Z.of_nat b) in *.
    set (C := Z.of_nat c) in *.
    assert (H10:
             (1%Z =
                (A * B * (x * x1) +
                   C * (x0 * B * x1 + x2 * A * x + x0 * x2 * C))%Z)).
    {
      change  1%Z with (Z.of_nat 1 * Z.of_nat 1)%Z.
      rewrite <- H6 at 1.
      rewrite <- H7. 
      ring; reflexivity. 
    }
    intros. destruct H4. rewrite H10.
    apply Z.divide_add_r.
    + exists (H8 * x * x1)%Z. assert (A * B = Z.of_nat (a * b))%Z by lia.
      rewrite H5. rewrite H9. lia.
    + apply Z.divide_mul_l. exists x3. auto.
Qed.





Lemma coPrimeProd :
 forall (n : nat) (x : nat -> nat),
 (forall z1 z2 : nat,
  z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)) ->
 (forall z : nat, z < S n -> x z > 0) -> CoPrime (prod n x) (x n).
Proof.
  induction n as [| n Hrecn].
  - intros; simpl in |- *; apply coPrime1.
  - intros x H H0.
    assert
      (H1: forall z1 z2 : nat,
          z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
    { intros;apply H.
      1,2:  now apply Nat.lt_lt_succ_r.
      - assumption.
    }
    simpl in |- *; apply coPrimeMult3.
  + apply H0.
    apply Nat.lt_lt_succ_r.
    apply Nat.lt_succ_diag_r.
  + apply prodBig1.
    intros; apply H0.
    do 2 apply Nat.lt_lt_succ_r.
    assumption.
  + apply H0.
    apply Nat.lt_succ_diag_r.
  + apply H.
    apply Nat.lt_lt_succ_r.
    apply Nat.lt_succ_diag_r.
    apply Nat.lt_succ_diag_r.
    auto.
  + set
      (A1 :=
         fun a : nat =>
           match eq_nat_dec a n with
           | left _ => x (S n)
           | right _ => x a
           end) in *.
    assert (H2: CoPrime (prod n A1) (A1 n)).
    { apply Hrecn.
      intros.
      unfold A1 in |- *.
      induction (eq_nat_dec z1 n).
      + induction (eq_nat_dec z2 n).
        * elim H4.
          rewrite a0.
          assumption.
        * apply H.
          apply Nat.lt_succ_diag_r.
          apply Nat.lt_lt_succ_r.
          assumption.
          unfold not in |- *; intros.
          rewrite H5 in H3.
          elim (Nat.lt_irrefl _ H3).
      + induction (eq_nat_dec z2 n).
        * apply H.
          apply Nat.lt_lt_succ_r.
          assumption.
          apply Nat.lt_succ_diag_r.
          unfold not in |- *; intros.
          rewrite H5 in H2.
          elim (Nat.lt_irrefl _ H2).
        * apply H.
          apply Nat.lt_lt_succ_r.
          assumption.
          apply Nat.lt_lt_succ_r.
          assumption.
          assumption.
      + intros.
        unfold A1 in |- *.
        induction (eq_nat_dec z n).
        * apply H0.
          apply Nat.lt_succ_diag_r.
        * apply H0.
          apply Nat.lt_lt_succ_r.
          assumption.
    }
    auto.
    replace (x (S n)) with (A1 n).
    replace (prod n x) with (prod n A1).
    assumption.
    apply prodExtensional.
    intros.
    unfold A1 in |- *.
    induction (eq_nat_dec z n).
   * rewrite a in H3.
     elim (Nat.lt_irrefl _ H3).
   * reflexivity.
   * unfold A1 in |- *.
     induction (eq_nat_dec n n).
     -- reflexivity.
     -- elim b; reflexivity.
Qed.

Lemma divProd :
  forall (n : nat) (x : nat -> nat) (i : nat),
    i < n -> divide (x i) (prod n x).
Proof.
  induction n as [| n Hrecn].
  - intros x i H; destruct (Nat.nlt_0_r _ H).
  - intros x i H.
    assert (lein: i <= n) by lia;
      rewrite Nat.lt_eq_cases in lein; destruct lein. 
    + simpl in |- *.
      rewrite Nat.mul_comm.
      destruct (Hrecn x i H0).
      rewrite H1. exists (x0 * x n). lia.
    + subst. simpl. exists (prod n x). auto.
Qed.

Lemma chRem :
 forall (n : nat) (x : nat -> nat),
   (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 ->
                        CoPrime (x z1) (x z2)) ->
 forall (y : nat -> nat) (py : forall z : nat, z < n -> y z < x z),
 {a : nat |
 a < prod n x /\
 (forall (z : nat) (pz : z < n),
  y z = snd (proj1_sig (div_eucl (x z) (ltgt1 _ _ (py z pz)) a)))}. 
Proof.
  intro.
  induction n as [| n Hrecn].
  - intros; exists 0.
    split.
    + simpl in |- *.
      apply Nat.lt_0_succ.
    + intros.
      elim (Nat.nlt_0_r _ pz).
  - intros.
    assert
      (H0: forall z1 z2 : nat,
          z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
    { intros; apply H.
      apply Nat.lt_lt_succ_r.
      assumption.
      apply Nat.lt_lt_succ_r.
      assumption.
      assumption.
    }
    assert (H1: forall z : nat, z < n -> y z < x z).
    { intros.
      apply py.
      apply Nat.lt_lt_succ_r.
      assumption.
    }
    induction (Hrecn x H0 y H1).
    clear Hrecn; induction p as (H2, H3).
    assert (H4: CoPrime (prod n x) (x n)).
    { apply coPrimeProd.
      - apply H.
      - intros.
        eapply ltgt1.
        apply py.
        assumption.
    } assert (H5: y n < x n).
    { apply py.
      apply Nat.lt_succ_diag_r.
    }
    induction (chineseRemainderTheorem
                   (prod n x) (x n) H4 x0 (y n) H2 H5).
    exists x1; induction p as (H6, (H7, H8)).
    split.
    simpl in |- *.
    rewrite Nat.mul_comm.
    assumption.
    intros.
    assert (lezn : z <= n) by lia.
    rewrite Nat.lt_eq_cases in lezn. destruct lezn.
   
    + assert
        (H10: y z =
                snd (proj1_sig (div_eucl (x z) (ltgt1 (y z) (x z)
                                                (H1 z H9)) x0)))
    by apply H3.
      induction (div_eucl (x z) (ltgt1 (y z) (x z) (H1 z H9)) x0).
      simpl in H10.
      induction (div_eucl (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
      simpl in |- *; rewrite H10.
      induction (div_eucl (prod n x) (ltgt1 x0 (prod n x) H2) x1).
      simpl in H7.
      rewrite H7 in p.
      induction p1 as (H11, H12).
      induction p as (H13, H14).
      induction p0 as (H15, H16).
      rewrite H13 in H11.
      apply uniqueRem with (x z) x1.
      apply (ltgt1 (y z) (x z) (py z pz)).
      assert (divide (x z) (prod n x)).
      { apply divProd.
        assumption.
      }
      induction H17 as (x5, H17).
      rewrite H17 in H11.
      rewrite (Nat.mul_comm (x z)) in H11.
      rewrite Nat.mul_assoc in H11.
      rewrite Nat.add_assoc in H11.
      rewrite <- Nat.mul_add_distr_r in H11.
      exists (fst x4 * x5 + fst x2).
      split.
      apply H11.
      assumption.
      exists (fst x3); auto.
    + induction (div_eucl (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
      induction (div_eucl (x n) (ltgt1 (y n) (x n) H5) x1).
      simpl in H8.
      simpl in |- *.
      rewrite H9.
      rewrite H8.
      eapply uniqueRem.
      apply (ltgt1 (y n) (x n) H5).
      exists (fst x3).
      apply p0.
      exists (fst x2).
      rewrite H9 in p.
      assumption.
Qed.


Definition Prime (n : nat) : Prop :=
  n > 1 /\ (forall q : nat, divide q n -> q = 1 \/ q = n).

Lemma divdec : forall n d : nat, divide d n \/ ~ divide d n.
Proof.
  intros. assert (d = 0 \/ 0 < d) by lia. destruct H.
  + destruct n.
    - left. exists 0. auto.
    - right. intro. destruct H0. lia.
  + revert d H. apply (lt_wf_ind n). clear n. intros.
    assert (n = 0 \/ 0 < n) by lia. destruct H1.
    - left. exists 0. lia.
    - assert (d <= n \/ n < d) by lia. destruct H2.
      * assert (n - d < n) by lia. destruct (H _ H3 _ H0).
        ++ destruct H4. left. exists (S x). lia.
        ++ right. intro. apply H4. destruct H5. exists (x - 1). nia.
      * right. intro. destruct H3. destruct x; lia.
Qed.

Lemma prime_Prime (n: nat) : prime (Z.of_nat n) -> Prime n.
Proof.
  intro. inversion H. clear H. unfold Prime. split.
  + lia.
  + intros. destruct H. assert (Z.of_nat n = Z.of_nat q * Z.of_nat x)%Z by lia.
    assert (n = 0 \/ 0 < n) by lia. destruct H3.
    - lia.
    - assert (1 < q < n \/ q = 1 \/ n <= q) by nia.
      destruct H4 as [H4 | [H4 | H4]].
      * assert (1 <= Z.of_nat q < Z.of_nat n)%Z by lia.
        pose proof (H1 _ H5). subst. exfalso.
        assert (1 < x) by nia. unfold rel_prime in H6.
        inversion H6. assert (Z.of_nat q | Z.of_nat q).
        { exists 1%Z. auto. lia. }
        assert (Z.of_nat q | Z.of_nat (q * x))%Z.
        { exists (Z.of_nat x). lia. }
        pose proof (H9 _ H10 H11). destruct H12. destruct x0; nia.
      * left. auto.
      * right. destruct x; nia.
Qed.

Lemma Prime_prime (n: nat) : Prime n -> prime (Z.of_nat n).
Proof.
  intros. unfold Prime in H. destruct H. constructor.
  + lia.
  + intros. destruct H1. unfold rel_prime.
    set (Z.gcd n0 (Z.of_nat n)) as W.
    assert (W <= n0)%Z.
    { pose proof (Z.gcd_divide_l n0 (Z.of_nat n)).
      apply Z.divide_pos_le in H3. auto. lia. }
    pose proof (Z.gcd_divide_r n0 (Z.of_nat n)).
    assert (divide (Z.to_nat W) n).
    { destruct H4. exists (Z.to_nat x). unfold W.
      pose proof (Z.gcd_nonneg n0 (Z.of_nat n)).
      nia. }
    apply H0 in H5. destruct H5.
    - assert (W = 1)%Z by lia.
      rewrite <- H6. apply Znumtheory.Zgcd_is_gcd.
    - lia.
Qed.

Lemma Prime_dec (n: nat) : Prime n \/ ~ Prime n.
Proof.
  destruct (prime_dec (Z.of_nat n)).
  + left. apply prime_Prime. auto.
  + right. intro. apply n0. apply Prime_prime. auto.
Qed.

Lemma primeDiv :
  forall a : nat, 1 < a ->
                  exists p : nat, Prime p /\
                                    divide p a.
Proof.
  intro a. apply (lt_wf_ind a). clear a. intros.
  destruct (Prime_dec n).
  + exists n. split; auto. exists 1. lia.
  + assert (~ prime (Z.of_nat n)).
    { intro. apply H1. apply prime_Prime. auto. }
    apply not_prime_divide in H2. destruct H2. destruct H2.
    assert (Z.to_nat x < n) by lia.
    assert (1 < Z.to_nat x) by lia.
    destruct (H _ H4 H5). destruct H6.
    exists x0. split; auto. destruct H3, H7.
    exists (Z.to_nat x1 * x2).
    nia. lia.
Qed.

Lemma coPrimePrime :
 forall a b : nat,
   (forall p : nat, Prime p ->
                    ~ divide p a \/ ~ divide p b) ->
   CoPrime a b.
Proof.
  intros. unfold CoPrime. constructor.
  + exists (Z.of_nat a). lia.
  + exists (Z.of_nat b). lia.
  + intros. apply Zdivide_Zabs_inv_l in H0. apply Zdivide_Zabs_inv_l in H1.
    assert (Z.abs x = 0 \/ Z.abs x = 1 \/ 1 < Z.abs x)%Z by lia.
    destruct H2 as [H2 | [H2 | H2]].
    - destruct H0. rewrite H2 in H0. destruct H1. rewrite H2 in H1.
      assert (a = 0) by lia. assert (b = 0) by lia. subst.
      assert (Prime 2).
      { apply prime_Prime. simpl. apply prime_2. }
      pose proof (H _ H3). destruct H4.
      * elim H4. exists 0. auto.
      * elim H4. exists 0. auto.
    - assert (x < 0 \/ 0 <= x)%Z by lia. destruct H3.
      * exists (-1)%Z. lia.
      * exists 1%Z. lia.
    - assert (1 < Z.to_nat (Z.abs x)) by lia.
      apply primeDiv in H3.
      destruct H3 as [p [H3 H4]]. pose proof (H _ H3).
      exfalso. destruct H4. destruct H5.
      * apply H5. destruct H0. exists (x0 * Z.to_nat x1). nia.
      * apply H5. destruct H1. exists (x0 * Z.to_nat x1). nia.
Qed.

Lemma div_plus_r :
 forall a b d : nat, divide d a -> divide d (a + b) -> divide d b.
Proof.
  intros. destruct H, H0. exists (x0 - x). nia.
Qed.

Lemma div_mult_compat_l :
  forall a b c : nat, divide a b -> divide a (b * c).
Proof.
  intros. destruct H. exists (c * x). lia.
Qed.

Lemma primedivmult :
  forall p n m : nat,
  Prime p -> divide p (n * m) -> divide p n \/ divide p m.
Proof.
  intros. apply Prime_prime in H. assert (Z.divide (Z.of_nat p) (Z.of_nat n * Z.of_nat m)).
  { destruct H0. exists (Z.of_nat x). nia. }
  apply prime_mult in H1; auto. destruct H1.
  + left. destruct H1. exists (Z.to_nat x). nia.
  + right. destruct H1. exists (Z.to_nat x). nia.
Qed.



Lemma coPrimeSeqHelp :
 forall c i j n : nat,
 divide (factorial n) c ->
 i < j -> i <= n -> j <= n -> CoPrime (S (c * S i)) (S (c * S j)).
Proof.
  intros ? ? ? ? H H0 H1 H2.
  apply coPrimePrime.
  intros p H3.
  destruct (divdec (S (c * S i)) p) as [H4 | H4].
   assert (H5: ~ divide p c).
   { intro H5. 
     assert (H6: divide p 1).
     { eapply div_plus_r.
       apply div_mult_compat_l.
       apply H5.
       rewrite Nat.add_comm.
       simpl in |- *.
       apply H4.
     }
     induction H3 as (H3, H7).
     red in H3; rewrite Nat.lt_nge in H3; apply H3.
     destruct H6 as [x Hx];destruct x; lia.
   }
   destruct (divdec (S (c * S j)) p).
   assert (H7: divide p (c * (j - i))).
   { rewrite minusS.
     rewrite Nat.mul_comm.
     rewrite Nat.mul_sub_distr_r.
     rewrite (Nat.mul_comm (S j)).
     rewrite (Nat.mul_comm (S i)).
     rewrite minusS.
     destruct H4, H6. rewrite H4, H6. exists (x0 - x). nia.
   }
   destruct (primedivmult _ _ _ H3 H7).
  - elim H5.
    assumption.
  - assert (H9: j - i <= n).
    { eapply Nat.le_trans.
      apply Nat.le_sub_l.
      assumption.
    }
    elim H5. 
    apply div_trans with (factorial n).
    apply div_trans with (j - i).
    assumption.
    unfold factorial in |- *.
    assert (H10: 1 <= j - i).
    { assert (H10: j = i + (j - i)).

      rewrite Nat.add_comm.
      rewrite  Nat.sub_add. 
      reflexivity.
      apply Nat.lt_le_incl; assumption.
      rewrite H10 in H0; lia.
    }
    replace (j - i) with (S (pred (j - i))).
    apply divProd.
    rewrite <- Nat.sub_1_r. 
    apply Nat.succ_lt_mono. 
    apply Nat.lt_succ_r.
    replace (S (j - i - 1)) with (1 + (j - i - 1)).
    rewrite Nat.add_comm, Nat.sub_add. 
    assumption.
    assumption.
    auto.
    induction (j - i).
    elim (Nat.nle_succ_diag_l _ H10).
    rewrite <- pred_Sn.
    reflexivity.
    assumption.
- auto.
- auto.
Qed.

(** Imported by PRRepresentable *)
Definition coPrimeBeta (z c : nat) : nat := S (c * S z).

Lemma coPrimeSeq :
  forall c i j n : nat,
    divide (factorial n) c ->
    i <> j -> i <= n -> j <= n ->
    CoPrime (coPrimeBeta i c) (coPrimeBeta j c).
Proof.
  unfold coPrimeBeta in |- *.
  intros ? ? ? ? H H0 H1 H2.
  rewrite Nat.lt_gt_cases in H0; destruct H0 as [H3 | H3].
  - eapply coPrimeSeqHelp.
    apply H.
    assumption.
    assumption.
    assumption.
  - apply coPrimeSym.
    eapply coPrimeSeqHelp.
    + apply H.
    + assumption.
    + assumption.
    + assumption.
Qed.

(** Imported by PRRepresentable *)
Lemma gtBeta : forall z c : nat, coPrimeBeta z c > 0.
Proof.
  unfold coPrimeBeta in |- *; intros; apply Nat.lt_0_succ.
Qed.

Fixpoint maxBeta (n: nat) (x: nat -> nat) :=
  match n with
  | 0 => 0
  | S n => Nat.max (x n) (maxBeta n x)
  end.

Lemma maxBetaLe :
  forall (n : nat) (x : nat -> nat) (i : nat),
    i < n -> x i <= maxBeta n x.
Proof.
  simple induction n.
  - intros x i H; elim (Nat.nlt_0_r _ H).
  - intros; simpl in |- *.
    assert (lein: i <= n0) by lia; rewrite Nat.lt_eq_cases in lein;
      destruct lein.
    +  eapply Nat.le_trans; [now apply H | apply Nat.le_max_r].
    + rewrite H1; apply Nat.le_max_l.
Qed.

Theorem divProd2 :
 forall (n : nat) (x : nat -> nat) (i : nat),
 i <= n -> divide (prod i x) (prod n x).
Proof.
  simple induction n.
  - intros x i ?; assert (H0: (0 = i)).
    { symmetry; now apply Nat.le_0_r. }
    rewrite H0.
    exists 1. lia.
  - intros n0 H x i H0.
    rewrite Nat.lt_eq_cases in H0; destruct H0.
    + simpl in |- *.
      rewrite Nat.mul_comm. assert (H2: i <= n0) by lia.
      destruct (H x i H2).
      rewrite H1.
      exists (x0 * x n0). lia.
    + rewrite H0; exists 1; lia.
Qed.

(** Imported by PRRepresentable *)
Theorem betaTheorem1 :
 forall (n : nat) (y : nat -> nat),
 {a : nat * nat |
 forall z : nat,
 z < n ->
 y z =
   snd (proj1_sig (div_eucl (coPrimeBeta z (snd a))
                     (gtBeta z (snd a)) (fst a)))}.
Proof.
  intros n y.
  set (c := factorial (max n (maxBeta n y))) in *.
  set (x := fun z : nat => coPrimeBeta z c) in *.
  assert
    (H: forall z1 z2 : nat,
        z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
  { intros; unfold x in |- *; eapply coPrimeSeq.
    - eapply div_trans.
      + unfold factorial in |- *; apply divProd2.
        apply Nat.le_max_l.
      + unfold c, factorial in |- *.
        exists 1; now rewrite Nat.mul_1_r. 
    - assumption.
    - now apply Nat.lt_le_incl.
    - apply Nat.lt_le_incl; assumption.
  }
  assert (H0: forall z : nat, z < n -> y z < x z).
  { intros; unfold x, coPrimeBeta in |- *.
    apply Nat.lt_succ_r. 
    induction (mult_O_le c (S z)). 
    - discriminate H1.
    - apply Nat.le_trans with c.
      + unfold c in |- *.
        apply Nat.le_trans with (max n (maxBeta n y)).
        apply Nat.le_trans with (maxBeta n y).
        apply maxBetaLe.
        assumption.
        apply Nat.le_max_r.
        generalize (max n (maxBeta n y)).
        intros.
        induction n0 as [| n0 Hrecn0].
        simpl in |- *.
        apply Nat.le_succ_diag_r. 
        induction n0 as [| n0 Hrecn1].
        simpl in |- *.
        apply le_n.
        assert (H2: factorial n0 > 0).
        { unfold factorial in |- *.
          apply prodBig1.
          intros.
          apply Nat.lt_0_succ.
        }
        simpl in |- *.
        apply Nat.le_trans with
          (1 + (1 + n0 * (factorial n0 + n0 * factorial n0))).
        * simpl in |- *.
          repeat apply le_n_S.
          induction (mult_O_le n0 (factorial n0 + n0 * factorial n0)).
          -- unfold gt in H2.
             assert (H4: factorial n0 = factorial n0 + 0)
               by (rewrite Nat.add_comm; auto).
             rewrite H4 in H2.
             set (A1 := factorial n0 + 0) in *.
             rewrite <- H3 in H2.
             unfold A1 in H2.
             clear H4 A1.
             assert (H4: n0 * factorial n0 < 0).
             { eapply Nat.add_lt_mono_l. 
               apply H2.
             }
             elim (Nat.nlt_0_r _ H4).
          -- rewrite Nat.mul_comm; assumption.
        * apply Nat.add_le_mono.
          apply le_plus_trans. (* to do *)
          apply Nat.lt_succ_r.
          rewrite <- Nat.succ_lt_mono.
          auto.           
          apply Nat.add_le_mono.
          apply le_plus_trans.
          apply Nat.lt_succ_r.
          rewrite <-  Nat.succ_lt_mono.
          assumption.
          apply le_n.
      + now rewrite Nat.mul_comm.
  }
  destruct (chRem _ _ H _ H0) as [x0 [H2 H3]].
  exists (x0, c).
  intros z H1; rewrite (H3 z H1).
  induction (div_eucl (x z) (ltgt1 (y z) (x z) (H0 z H1)) x0).
  simpl fst; simpl snd.
  destruct (div_eucl (coPrimeBeta z c) (gtBeta z c) x0) as [x2 p0].
  simpl in |- *.
  eapply uniqueRem.
  apply gtBeta.
  unfold x in p.
  exists (fst x1); apply p.
  exists (fst x2); apply p0.
Qed.

