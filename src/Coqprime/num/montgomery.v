Require Import List ZArith Znumtheory Int31 Cyclic31.

(* We are going to implement modular arithmetic with
   montgomery reduction
*)

Definition number := list int31.

Definition nhead (n : number) :=
  match n with cons i _ => i | _ => 0%int31 end.

Definition ntail (n : number) : number :=
  match n with cons _ t => t | _ => @nil _ end.

Open Scope int31_scope.

Fixpoint positive_aux_to_num (p : positive) (i j : int31) : number :=
  match p with
  | xH    => (i + j) :: nil
  | xO p1 =>
    let i1 := 2 * i in
    match i1 ?= 0 with
    | Gt => positive_aux_to_num  p1 i1 j
    | _  =>  j :: positive_aux_to_num  p1 1 0
    end
  | xI p1 =>
    let i1 := 2 * i in
    let j1 := i + j in
    match i1 ?= 0 with
    | Gt => positive_aux_to_num  p1 i1 j1
    | _  =>  j1 :: positive_aux_to_num  p1 1 0
    end
  end.

Definition positive_to_num (p : positive) : number :=
  positive_aux_to_num p 1 0.

Definition Z_to_num z :=
  match z with
  | Zpos p => positive_to_num p
  | _      => nil
  end.

Eval vm_compute in
  positive_to_num 31415926535897932384626433.

Eval vm_compute in
  positive_to_num 2147483648.

Local Definition wB := (2^ Z_of_nat size)%Z.
Definition mphi (n : number) :=
  fold_right (fun i r => phi i + wB * r )%Z 0%Z n.

Notation "[ a ]" := (mphi a).

Eval vm_compute in
  [positive_to_num 31415926535897932384626433].

Lemma phi_nil : [nil] = 0%Z.
Proof. auto. Qed.

Lemma phi_cons a l : ([a::l] = phi a + wB * [l])%Z.
Proof. auto. Qed.

Lemma phi_head_tail n : [n] = [nhead n :: ntail n].
Proof. unfold nhead, ntail; case n; auto. Qed.

Ltac nrom :=
 repeat rewrite phi_nil;
 repeat rewrite phi_cons;
 try change (phi 0) with 0%Z;
 try change (phi 1) with 1%Z;
 try change (phi 2) with 2%Z;
 try change (phi Tn) with (wB - 1)%Z;
 try change (2^ Z_of_nat size)%Z with wB.

Lemma Zpower_nat_0 x : Zpower_nat x 0 = 1%Z.
Proof. auto. Qed.

Lemma Zpower_nat_S x n : Zpower_nat x (S n) =  (x * Zpower_nat x n)%Z.
Proof. auto. Qed.

Lemma Zpower_nat_pos u n : (0 < u -> 0  < Zpower_nat u n)%Z.
Proof.
intros Hu.
induction n. reflexivity.
rewrite Zpower_nat_S.
apply Zmult_lt_0_compat; assumption.
Qed.

Lemma Zpower_base_pos n : (0  < Zpower_nat wB n)%Z.
Proof. apply Zpower_nat_pos; auto with zarith; red; auto. Qed.

Lemma Zpower_nat_le_compat u n m :
  (0 < u)%Z -> (n <= m)%nat -> (Zpower_nat u n  <= Zpower_nat u m)%Z.
Proof.
intros Hu; generalize m; clear m; induction n as [ | n Hrec]; auto with zarith.
intros [ | m]; repeat rewrite Zpower_nat_S; try rewrite Zpower_nat_0; auto with zarith.
intros _; change 1%Z with (1 * 1)%Z; apply Zmult_le_compat; auto with zarith.
generalize (Zpower_nat_pos _ m Hu); auto with zarith.
intros [ | m]; repeat rewrite Zpower_nat_S; try rewrite Zpower_nat_0; auto with zarith.
Qed.

Lemma Zpower_nat_lt_compat u n m :
  (1 < u)%Z -> (n < m)%nat -> (Zpower_nat u n  < Zpower_nat u m)%Z.
Proof.
intros Hu; generalize m; clear m; induction n as [ | n Hrec]; auto with zarith.
intros [ | m]; repeat rewrite Zpower_nat_S; try rewrite Zpower_nat_0; auto with zarith.
intros _; apply Z.lt_le_trans with (u * 1)%Z; auto with zarith.
assert (Hv: (0 < u)%Z); auto with zarith.
generalize (Zpower_nat_pos _ m Hv); auto with zarith.
intros [ | m]; repeat rewrite Zpower_nat_S; try rewrite Zpower_nat_0; auto with zarith.
intros HH.
apply Zmult_lt_compat_l; auto with zarith.
Qed.

Lemma Zpower_nat_le_reg u n m :
  (1 < u)%Z -> (Zpower_nat u n  <= Zpower_nat u m)%Z -> (n <= m)%nat .
Proof.
intros Hu; generalize m; clear m; induction n as [ | n Hrec]; auto with zarith.
intros [ | m]; repeat rewrite Zpower_nat_S; try rewrite Zpower_nat_0.
intros Hv; contradict Hv; apply Zlt_not_le.
apply Z.lt_le_trans with (u * 1)%Z; auto with zarith.
assert (HH: (0 < u)%Z); auto with zarith.
assert (HH1:= Zpower_nat_pos u n HH); auto with zarith.
intros Hv; assert (n <= m)%nat; auto with arith.
apply Hrec; apply Zmult_le_reg_r with u; auto with zarith;
  repeat rewrite <- (Zmult_comm u); auto.
Qed.

Lemma Zpower_nat_lt_reg u n m :
  (1 < u)%Z -> (Zpower_nat u n  < Zpower_nat u m)%Z -> (n < m)%nat .
Proof.
intros Hu; generalize m; clear m; induction n as [ | n Hrec]; auto with zarith.
intros [ | m]; repeat rewrite Zpower_nat_S; try rewrite Zpower_nat_0; auto with zarith.
intros [ | m]; repeat rewrite Zpower_nat_S; try rewrite Zpower_nat_0; auto with zarith.
intros Hv; contradict Hv; apply Zle_not_lt.
apply Z.le_trans with (u * 1)%Z; auto with zarith.
assert (HH: (0 < u)%Z); auto with zarith.
assert (HH1:= Zpower_nat_pos u n HH); auto with zarith.
intros Hv; assert (n < m)%nat; auto with arith.
apply Hrec; apply Zmult_lt_reg_r with u; auto with zarith;
  repeat rewrite <- (Zmult_comm u); auto.
Qed.

Lemma positive_phi p : [positive_to_num p] = Zpos p.
Proof.
assert (Hi0: (forall i n, phi i = Zpower_nat 2 n ->
              match 2 * i ?= 0 with
              | Eq => n = 30%nat
              | Lt => False
              | Gt => phi (2 * i) = Zpower_nat 2 (S n)
              end)).
intros i n Hi.
  assert (n < 31)%nat.
  case (phi_bounded i); nrom; rewrite Hi; intros Hi1 Hi2.
  apply Zpower_nat_lt_reg with 2%Z; auto with zarith.
assert (HH1: (0 < 2)%Z); auto with zarith.
assert (HH2 := Zpower_nat_pos _ (S n) HH1).
rewrite spec_compare; case Z.compare_spec.
rewrite spec_mul; nrom.
rewrite Hi, <- Zpower_nat_S; auto with zarith.
case (le_lt_or_eq n 30); auto with zarith; intros HH3.
rewrite Zmod_small; auto with zarith.
split; auto with zarith.
change wB with (Zpower_nat 2 31); apply Zpower_nat_lt_compat; auto with zarith.
intros HH; contradict HH.
case (phi_bounded (2 * i)); nrom; auto with zarith.
rewrite spec_mul; nrom; rewrite Hi, <- Zpower_nat_S; auto with zarith.
case (le_lt_or_eq n 30); auto with zarith; intros HH3.
rewrite Zmod_small; nrom; auto with zarith.
split; auto with zarith.
change wB with (Zpower_nat 2 31); apply Zpower_nat_lt_compat; auto with zarith.
rewrite HH3, Z_mod_same; auto with zarith.
apply Z.lt_gt; auto with zarith.
assert (Hij: (forall i j n, phi i = Zpower_nat 2 n -> phi j < phi i ->
             phi (i + j) = phi i + phi j)%Z).
intros i j n Hi Hj.
  rewrite spec_add, Zmod_small; auto; nrom.
  case (phi_bounded i); case (phi_bounded j); nrom; intros H1j H2j H1i H2i;
   split; auto with zarith.
  assert (n < 31)%nat.
  apply Zpower_nat_lt_reg with 2%Z; auto with zarith.
  rewrite <- Hi; auto with zarith.
  apply Z.lt_le_trans with (Zpower_nat 2 (S n)).
  rewrite Zpower_nat_S, <-Hi; auto with zarith.
  change wB with (Zpower_nat 2 31).
  apply Zpower_nat_le_compat; auto with zarith.
assert (H: forall p1 i j n, phi i = Zpower_nat 2 n -> (phi j < phi i ->
   mphi (positive_aux_to_num p1 i j) = Zpos p1 * phi i + phi j)%Z).
induction p1 as [p1 Hrec| p1 Hrec| ]; simpl positive_aux_to_num; intros i j n Hi Hj.
generalize (Hi0 i n Hi); rewrite spec_compare; case Z.compare_spec; nrom.
intros Hphi Hn; rewrite (Hij i j n), Hi, Hn; auto with zarith.
rewrite (Hrec 1 0 0%nat); nrom; auto with zarith.
rewrite Zpos_xI; change wB with (2 * Zpower_nat 2 30)%Z; ring.
generalize (phi_bounded (2 * i)); auto with zarith.
intros HH H2i; rewrite (Hrec _ _ (S n)); auto with zarith.
rewrite Zpos_xI, H2i, (Hij i j n), Hi, Zpower_nat_S by auto with zarith.
ring.
rewrite (Hij i j n), H2i, Zpower_nat_S, <- Hi; auto with zarith.
generalize (Hi0 i n Hi); rewrite spec_compare; case Z.compare_spec; nrom.
intros HH Hn; rewrite Hi, Hn; auto with zarith.
rewrite (Hrec 1 0 0%nat); nrom; auto with zarith.
rewrite Zpos_xO; change wB with (2 * Zpower_nat 2 30)%Z; ring.
generalize (phi_bounded (2 * i)); auto with zarith.
intros HH H2i; rewrite (Hrec _ _ (S n)); auto with zarith.
rewrite Zpos_xO, H2i, Hi, Zpower_nat_S by auto with zarith.
ring.
case (phi_bounded i); intros Hi1 H2.
rewrite H2i, Zpower_nat_S, <- Hi; auto with zarith.
rewrite phi_cons, (Hij i j n); nrom; auto with zarith.
unfold positive_to_num.
rewrite (H _ _ _ 0%nat); auto with zarith.
nrom; ring.
nrom; auto with zarith.
Qed.

Lemma phi_pos n : (0 <= [n])%Z.
Proof.
induction n as [ | a n Hrec]; nrom; auto with zarith.
case (phi_bounded a); intros Ha1 Ha2; auto with zarith.
apply Z.add_nonneg_nonneg; auto with zarith.
apply Z.mul_nonneg_nonneg; auto with zarith.
apply Z.pow_nonneg; auto with zarith.
Qed.

Lemma num_phi z :  (0 <= z)%Z -> [Z_to_num z] = z.
Proof.
destruct z as [|p|p]; intros Hp. auto with zarith.
apply positive_phi.
contradict Hp; auto with zarith.
Qed.

Lemma add_cp a b :
  match (a + b) ?= a with
  | Lt => (phi (a + b) = phi a + phi b - wB)%Z
  | _  => (phi (a + b) = phi a + phi b)%Z
  end.
Proof.
case (phi_bounded a); nrom; intros Ha1 Ha2.
case (phi_bounded b); nrom; intros Hb1 Hb2.
case (phi_bounded (a + b)); nrom; intros Hab1 Hab2.
assert (H2ab: (phi a + phi b < 2 * wB)%Z); auto with zarith.
case (Zle_or_lt wB (phi a + phi b)); intros H1ab.
assert (He: (phi(a + b) = phi a + phi b - wB)%Z).
rewrite <- (fun x y => Zmod_small (x - y) wB); auto with zarith.
rewrite Zminus_mod, Z_mod_same_full, Zminus_0_r, Zmod_mod, <- spec_add; auto.
rewrite spec_compare; case Z.compare_spec; nrom; intros Hc; auto with zarith.
assert (He: (phi(a + b) = phi a + phi b)%Z).
rewrite spec_add, Zmod_small; auto with zarith.
rewrite spec_compare; case Z.compare_spec; nrom; intros Hc; auto with zarith.
Qed.

Lemma add1_cp a :
  match (1 + a) ?= 0 with
  | Eq => (phi a = wB - 1)%Z
  | _ => (phi (1 + a) = 1 + phi a)%Z
  end.
Proof.
case (phi_bounded a);
case (phi_bounded (1 + a));
  generalize (add_cp 1 a); rewrite spec_compare; case Z.compare_spec;
  rewrite spec_compare; case Z.compare_spec; nrom; auto with zarith.
Qed.

Lemma add2_cp a b :
  match (1 + (a + b)) ?= a with
  | Gt  => (phi (1 + (a + b)) = phi a + phi b + 1)%Z
  | _ => (phi (1 + (a + b)) = phi a + phi b + 1 - wB)%Z
  end.
Proof.
case (phi_bounded a); nrom; intros Ha1 Ha2.
case (phi_bounded b); nrom; intros Hb1 Hb2.
case (phi_bounded (a + b)); nrom; intros Hab1 Hab2.
case (phi_bounded (1 + (a + b))); nrom; intros H1ab1 H1ab2.
generalize (add_cp 1 (a + b)) (add_cp a b);
 do 2 (rewrite spec_compare; case Z.compare_spec); nrom; intros H1 H2;
  lazy zeta; rewrite spec_compare; case Z.compare_spec; nrom; auto with zarith.
Qed.

Fixpoint incr_num (n: number): number :=
  match n with
  | nil => 1 :: nil
  | a::n1 => let c :=  1 + a in
             match c ?= 0 with
             | Eq => 0 :: incr_num n1
             | _  => c :: n1
             end
  end.

Notation "a .+1" := (incr_num a) (at level 0).

Lemma incr_correct n : ([n.+1] = [n] + 1)%Z.
Proof.
induction n as [ | a n Hrec]; nrom; auto.
unfold incr_num; fold incr_num.
generalize (add1_cp a); rewrite spec_compare; case Z.compare_spec; nrom;
  intros HH H; rewrite H; try rewrite Hrec; try ring.
Qed.

Fixpoint add_num (n1 n2 : number) :=
  match n1 with
  | nil => n2
  | a :: n3 => match n2 with
             | nil => n1
             | b :: n4 => let c := a + b in
                          match c ?= a with
                          | Lt => c :: add1_num n3 n4
                          | _  => c :: add_num n3 n4
                          end
             end
  end
with add1_num (n1 n2 : number) :=
  match n1 with
  | nil => incr_num n2
  | a :: n3 => match n2 with
               | nil => incr_num n1
               | b :: n4 => let c := (1 + (a + b)) in
                            match c ?= a with
                            | Gt  => c :: add_num n3 n4
                            | _   => c :: add1_num n3 n4
                            end
               end
  end.

Notation "a + b" := (add_num a b).
Notation "a +1 b" := (add1_num a b) (at level 40).

Lemma add_add1_correct m n :
  [m + n] = ([m] + [n])%Z /\ [m +1 n] = ([m] + [n] + 1)%Z.
Proof.
generalize n; clear n.
induction m as [ | a m Hrec]; nrom; auto.
intros n; simpl; rewrite incr_correct; auto.
intros n; destruct n as [ | b n].
  unfold add_num; fold add_num;
  unfold add1_num; fold add1_num;
  rewrite incr_correct; auto with zarith.
split.
change ((a :: m) + (b :: n)) with
                      (let c :=  (a + b)%int31 in
                        match c ?= a with
                        | Lt => c::add1_num m n
                        | _  => c::add_num m n
                        end).
lazy zeta; generalize (add_cp a b); rewrite spec_compare; case Z.compare_spec;
  nrom; intros HH H; case (Hrec n); intros H1 H2;
  try rewrite H; try rewrite H1; try rewrite H2; ring.
change ((a :: m) +1 (b :: n)) with
                      (let c :=  (1 + (a + b))%int31 in
                        match c ?= a with
                        | Gt => c::add_num m n
                        | _  => c::add1_num m n
                        end).
lazy zeta;  generalize (add2_cp a b); rewrite spec_compare; case Z.compare_spec;
 nrom; intros HH H1; case (Hrec n); intros Hr1 Hr2;
 rewrite H1; (rewrite Hr1 || rewrite Hr2); ring.
Qed.

Lemma add_correct m n : [m + n] = ([m] + [n])%Z.
Proof. case (add_add1_correct m n); auto. Qed.

Lemma add1_correct m n : [m +1 n] = ([m] + [n] + 1)%Z.
Proof. case (add_add1_correct m n); auto. Qed.

Fixpoint zerop_num (n: number) :=
  match n with
  | nil => true
  | a::n1 => match a ?= 0 with
             | Eq => zerop_num n1
             | _  => false
             end
  end.

Lemma zerop_correct n :
  if zerop_num n then [n] = 0%Z else [n] <> 0%Z.
Proof.
induction n as [ | a n Hrec].
simpl; auto.
case (phi_bounded a); nrom; intros Ha1 Ha2.
unfold zerop_num; fold zerop_num.
rewrite spec_compare; case Z.compare_spec; nrom. 2: auto with zarith.
generalize Hrec; case zerop_num.
intros H1 H2; rewrite H1, H2; ring.
intros H1 H2; rewrite H2.
rewrite Zplus_0_l; intros HH; case (Zmult_integral _ _ HH);
  auto with zarith.
generalize (phi_pos n); intros H1 H2 H3.
enough (0 < phi a + wB * [n])%Z by auto with zarith.
apply Z.lt_le_trans with (phi a). auto with zarith.
assert (0 <= wB * [n])%Z; auto with zarith.
Qed.

Fixpoint cpr_num (n1 n2: number) res :=
  match n1 with
  | nil => if zerop_num n2 then res else Lt
  | a :: n3 => match n2 with
             | nil => if zerop_num n1 then res else Gt
             | b :: n4 => let res1 :=
                          match a ?= b with
                          | Eq => res
                          | v  => v
                          end in cpr_num n3 n4 res1
             end
  end.

Lemma base_lexi_order a b n1 n2 wB :
  (0 <= a < wB -> 0 <= b < wB ->
   match a + wB * n1 ?= b + wB * n2 with
   | Eq => a = b /\ n1 = n2
   | Lt => n1 < n2 \/ (n1 = n2 /\ a < b)
   | Gt => n2 < n1 \/ (n1 = n2 /\ b < a)
   end)%Z.
Proof.
intros (Ha1, Ha2) (Hb1, Hb2).
case Z.compare_spec; intros HH.
case (Zle_or_lt n1 n2); intros H1.
case (Zle_lt_or_eq _ _ H1); clear H1; intros H1; auto.
assert (HH1: (wB + wB * (n2 - n1 -1) = (a - b))%Z).
replace a with ((a + wB * n1) - wB * n1)%Z by ring.
rewrite HH; ring.
assert (Hu: (0 <= wB * (n2 - n1 - 1))%Z); auto with zarith.
split; auto.
replace a with ((a + wB * n1) - wB * n1)%Z by ring.
rewrite HH, H1; ring.
assert (wB + wB * (n1 - n2 -1) = (b - a))%Z.
replace b with ((b + wB * n2) - wB * n2)%Z by ring.
rewrite <-HH; ring.
assert (Hu: (0 <= wB * (n1 - n2 - 1))%Z); auto with zarith.
case (Zle_or_lt n2 n1); intros H1; auto.
case (Zle_lt_or_eq _ _ H1); clear H1; intros H1; auto.
assert (0 <= wB * (n1 - n2 - 1))%Z by auto with zarith.
enough (wB + wB * (n1 - n2 -1) < (b - a))%Z by auto with zarith.
repeat rewrite Zmult_minus_distr_l; rewrite Zmult_1_r; auto with zarith.
rewrite H1 in HH; auto with zarith.
case (Zle_or_lt n1 n2); intros H1; auto.
case (Zle_lt_or_eq _ _ H1); clear H1; intros H1; auto.
assert (0 <= wB * (n2 - n1 - 1))%Z by auto with zarith.
enough (wB + wB * (n2 - n1 -1) < (a - b))%Z by auto with zarith.
repeat rewrite Zmult_minus_distr_l; rewrite Zmult_1_r; auto with zarith.
rewrite H1 in HH; auto with zarith.
Qed.

Lemma cpr_correct n1 n2 res :
  match ([n1] ?= [n2])%Z with
  | Lt => cpr_num n1 n2 res = Lt
  | Gt => cpr_num n1 n2 res = Gt
  | Eq => cpr_num n1 n2 res = res
  end.
Proof.
generalize n2 res; clear n2 res.
induction n1 as [ | a n1 Hrec].
intros n2 res; simpl cpr_num; nrom.
generalize (phi_pos n2); case Z.compare_spec; auto with zarith;
  generalize (zerop_correct n2); case zerop_num; auto with zarith;
  intros H1 H2 H3; contradict H1; auto with zarith.
intros [ | b n2].
intros res; unfold cpr_num.
generalize (phi_pos (a::n1)); case Z.compare_spec; auto with zarith;
  generalize (zerop_correct (a::n1)); case zerop_num; auto with zarith;
  nrom; intros H1 H2 H3; contradict H1; auto with zarith.
intros res; unfold cpr_num; fold cpr_num.
set (v := (match a ?= b with Eq => res | _ => a ?= b end)).
generalize (base_lexi_order _ _ [n1] [n2] _
                    (phi_bounded a) (phi_bounded b)); nrom;
  case Z.compare.
intros (HH, HH0).
unfold v; rewrite spec_compare; case Z.compare_spec; nrom; intros HH2;
  try (contradict HH2; auto with zarith; fail).
generalize (Hrec n2 res); case Z.compare_spec; auto;
 intros HH3; contradict HH3; auto with zarith.
intros [HH2 | (HH2, HH3)].
generalize (Hrec n2 v); rewrite HH2; unfold v;
  rewrite spec_compare; case Z.compare_spec; auto.
generalize (Hrec n2 v); rewrite HH2; unfold v.
rewrite Z.compare_refl.
rewrite spec_compare; case Z.compare_spec; auto with zarith
 ; intros HH; contradict HH; auto with zarith.
intros [HH2 | (HH2, HH3)].
generalize (Hrec n2 v); case Z.compare_spec; auto with zarith.
intros HH; contradict HH2; auto with zarith.
intros HH; contradict HH2; auto with zarith.
unfold v; rewrite spec_compare; case Z.compare_spec; auto.
generalize (Hrec n2 v); rewrite HH2, Z.compare_refl.
unfold v; rewrite spec_compare; case Z.compare_spec; auto.
intros HH4; contradict HH3; auto with zarith.
intros HH4; contradict HH3; auto with zarith.
Qed.

Definition cp_num n1 n2 := cpr_num n1 n2 Eq.

Inductive CpSpec (i j : number) : comparison -> Prop :=
    CpSpecEq : [i] = [j] -> CpSpec i j Eq
  | CpSpecLt : ([i] < [j])%Z -> CpSpec i j Lt
  | CpSpecGt : ([j] < [i])%Z -> CpSpec i j Gt.

Lemma cp_spec i j : CpSpec i j (cp_num i j).
Proof.
generalize (cpr_correct i j Eq).
unfold cp_num; case Z.compare_spec; intros H1 H2; rewrite H2;
  constructor; auto.
Qed.

Fixpoint eq_num (n1 n2: number) :=
  match n1 with
  | nil     => zerop_num n2
  | a :: n3 => match n2 with
             | nil     => zerop_num n1
             | b :: n4 => match a ?= b with
                          | Eq => eq_num n3 n4
                          | _  => false
                        end
             end
  end.

Lemma eq_correct n1 n2 :
  if eq_num n1 n2 then [n1] = [n2]%Z else [n1] <> [n2]%Z.
Proof.
generalize n2; clear n2.
induction n1 as [ | a n1 Hrec].
intros n2; generalize (zerop_correct n2); simpl; case zerop_num; auto.
case (phi_bounded a); nrom; intros Ha1 Ha2.
intros [ |b n2]; unfold eq_num; fold eq_num; nrom.
generalize (zerop_correct (a::n1)); simpl; case zerop_num; auto.
rewrite spec_compare; case Z.compare_spec; nrom; intros H1;
  try (
    intros HH;
     generalize (base_lexi_order _ _ [n1] [n2] _
                      (phi_bounded a) (phi_bounded b)); nrom;
    rewrite HH, Z.compare_refl; intros (H3,H4); contradict H1; auto with zarith).
generalize (Hrec n2); case eq_num; intros H2.
apply Zcompare_Eq_eq;
  generalize (base_lexi_order _ _ [n1] [n2] _
                    (phi_bounded a) (phi_bounded b)); nrom;
  case Z.compare; auto.
intros [H3 | (H3, H4)]; contradict H3; auto with zarith.
intros [H3 | (H3, H4)]; contradict H3; auto with zarith.
intros HH;
  generalize (base_lexi_order _ _ [n1] [n2] _
                    (phi_bounded a) (phi_bounded b)); nrom;
  rewrite HH, Z.compare_refl; intros (H3,H4); case H2; auto.
Qed.

Fixpoint decr_num (n: number): number :=
  match n with
  | nil     => 1 :: nil
  | a :: n1 => match a ?= 0 with
             | Eq => Tn :: decr_num n1
             | _  => (a - 1) :: n1
             end
  end.

Notation "a .-1" := (decr_num a) (at level 0).

Lemma decr_correct n : (0 < [n])%Z -> ([n.-1] = [n] - 1)%Z.
Proof.
induction n as [ | a n Hrec]; nrom. auto with zarith.
unfold decr_num; fold decr_num.
case (phi_bounded a); nrom; intros Ha1 Ha2.
rewrite spec_compare; case Z.compare_spec;
  nrom; try rewrite spec_Bm1; nrom. 2: auto with zarith.
intros H1 H2; rewrite H1 in H2 |- *; rewrite Hrec;
 auto with zarith; try ring.
apply Zmult_lt_0_reg_r with wB; auto with zarith.
rewrite Zmult_comm; auto with zarith.
intros H1 H2.
rewrite spec_sub; nrom.
rewrite Zmod_small; auto with zarith.
Qed.

Fixpoint sub_num (n1 n2 : number) :=
  match n1 with
  | nil     => nil
  | a :: n3 => match n2 with
             | nil     => n1
             | b :: n4 => let c := a - b in
                          match c ?= a with
                          | Gt => c :: sub1_num n3 n4
                          | _  => c :: sub_num n3 n4
                          end
             end
  end
with sub1_num (n1 n2 : number) :=
  match n1 with
  | nil     => nil
  | a :: n3 => match n2 with
               | nil     => decr_num n1
               | b :: n4 => let c := (a - (1 + b)) in
                            match c ?= a with
                            | Lt  => c :: sub_num n3 n4
                            | _   => c :: sub1_num n3 n4
                            end
               end
  end.

Notation "a - b" := (sub_num a b).
Notation "a -1 b" := (sub1_num a b) (at level 40).

Lemma sub_cp a b :
  match (a - b) ?= a with
  | Gt => (phi (a - b) = phi a - phi b + wB)%Z
  | _  => (phi (a - b) = phi a - phi b)%Z
  end.
Proof.
case (phi_bounded a); nrom; intros Ha1 Ha2.
case (phi_bounded b); nrom; intros Hb1 Hb2.
case (phi_bounded (a - b)); nrom; intros Hab1 Hab2.
assert (H1ab: (phi a - phi b < wB)%Z); auto with zarith.
case (Zle_or_lt 0 (phi a - phi b)); intros Hab.
assert (He: (phi(a - b) = phi a - phi b)%Z).
rewrite spec_sub, Zmod_small; auto with zarith.
rewrite spec_compare; case Z.compare_spec; intros Hc;
  auto with zarith.
assert (He: (phi(a - b) = phi a - phi b + wB)%Z).
rewrite <- (fun x y => Zmod_small (x + y) wB); auto with zarith.
rewrite Zplus_mod, Z_mod_same_full, Zplus_0_r, Zmod_mod, <- spec_sub; auto.
rewrite spec_compare; case Z.compare_spec; intros Hc;
  auto with zarith.
Qed.

Lemma sub1_cp a b :
  match (a - (1 + b)) ?= a with
  | Lt => (phi (a - (1 + b)) = phi a - (1 + phi b))%Z
  | _  => (phi (a - (1 + b)) = phi a - (1 + phi b) + wB)%Z
  end.
Proof.
case (phi_bounded a); nrom; intros Ha1 Ha2.
case (phi_bounded b); nrom; intros Hb1 Hb2.
case (phi_bounded (1 + b)); nrom; intros H1b1 H1b2.
case (phi_bounded (a - (1 + b))); nrom; intros Hab1 Hab2.
case (Zle_lt_or_eq (1 + phi b) wB); auto with zarith; intros Hb3;
  try(
  rewrite spec_compare; case Z.compare_spec; intros Hc;
  auto with zarith;
  generalize Hc; rewrite spec_sub, spec_add; nrom;
  rewrite Hb3, Z_mod_same_full, Zminus_0_r, Zmod_small; auto with zarith).
assert (H1b: phi (1 + b) = (phi b + 1)%Z).
  rewrite spec_add, Zmod_small; nrom; auto with zarith.
assert (H1ab: (phi a - phi (1 + b) < wB)%Z); auto with zarith.
case (Zle_or_lt 0 (phi a - phi (1 + b))); intros Hab.
assert (He: (phi(a - (1 + b)) = phi a - phi b - 1)%Z).
rewrite spec_sub, Zmod_small; nrom; auto with zarith.
rewrite spec_compare; case Z.compare_spec; intros Hc;
  auto with zarith.
assert (He: (phi(a - (1 + b)) = phi a - phi b - 1 + wB)%Z).
rewrite <- (fun x y => Zmod_small (x + y) wB); auto with zarith.
rewrite Zplus_mod, Z_mod_same_full, Zplus_0_r, Zmod_mod; auto with zarith.
rewrite spec_sub, H1b; nrom; apply f_equal2 with (f := Zmod); auto with zarith.
rewrite spec_compare; case Z.compare_spec; intros Hc;
  auto with zarith.
Qed.

Lemma sub_sub1_correct m n :
   (([n] <= [m])%Z -> [m - n] = ([m] - [n])%Z)
/\ ([n] <  [m] -> [m -1 n] = [m] - (1 + [n]))%Z.
Proof.
generalize n; clear n.
induction m as [ | a m Hrec]; nrom; auto.
intros n; induction n as [ | b n Hrec];
  unfold sub_num, sub1_num; fold sub_num;
  fold sub1_num; nrom; auto with zarith.
generalize (phi_pos (b::n)); nrom; auto with zarith.
intros n; destruct n as [ | b n];
  unfold sub_num, sub1_num; fold sub_num;
  fold sub1_num; nrom; auto with zarith.
split; intros H1; auto with zarith.
rewrite decr_correct; auto with zarith.
split; intros H1.
case (Hrec n); intros H2 H3.
assert (H4: ([n] <= [m])%Z).
  generalize (base_lexi_order _ _ [n] [m] _ (phi_bounded b) (phi_bounded a));
  nrom;
  case (Zle_lt_or_eq _ _ H1); intros H4.
    red in H4; rewrite H4; auto with zarith.
  rewrite H4, Z.compare_refl; auto with zarith.
generalize (sub_cp a b); rewrite spec_compare; case Z.compare_spec; nrom; intros HH0 HH1;
  rewrite HH1; try rewrite H2; auto; try ring.
rewrite H3; try ring.
case (Zle_lt_or_eq _ _ H4); intros H5; auto.
rewrite H5 in H1 |- *.
generalize (base_lexi_order _ _ [m] [m] _ (phi_bounded b) (phi_bounded a));
nrom.
assert (H6: (phi a < phi b)%Z).
case (Zle_or_lt (phi b) (phi a)); intros H6; auto.
generalize HH1; rewrite spec_sub; nrom.
  case (phi_bounded a); nrom; intros Ha1 Ha2;
  case (phi_bounded b); nrom; intros Hb1 Hb2;
    rewrite Zmod_small; auto with zarith.
case (Zle_lt_or_eq _ _ H1); intros H7.
red in H7; rewrite H7; auto with zarith.
rewrite H7, Z.compare_refl; auto with zarith.
generalize (base_lexi_order _ _ [n] [m] _ (phi_bounded b) (phi_bounded a)); nrom.
red in H1; rewrite H1.
intros [H2 | (H2, H3)].
case (Hrec n); intros H3 H4.
generalize (sub1_cp a b); rewrite spec_compare; case Z.compare_spec; nrom; intros HH0 HH1;
  rewrite HH1; try rewrite H3; try rewrite H4;
  auto with zarith; try ring.
assert (Ha: (phi (a - (1 + b)) < phi a)%Z).
  case (phi_bounded a); nrom; intros H1a H2a.
  case (phi_bounded b); nrom; intros H1b _.
  rewrite spec_sub, Zmod_small; nrom; auto with zarith;
  rewrite spec_add, Zmod_small; nrom; auto with zarith.
rewrite spec_compare; case Z.compare_spec; auto with zarith.
intros _; case (Hrec n); intros H4 _; nrom.
rewrite H4; auto with zarith.
case (phi_bounded a); nrom; intros H1a H2a;
  case (phi_bounded b); nrom; intros H1b _;
  rewrite spec_sub, Zmod_small; nrom; auto with zarith;
  rewrite spec_add, Zmod_small; nrom; auto with zarith;
  try ring.
Qed.

Lemma sub_correct m n :
  ([n] <= [m])%Z -> [m - n] = ([m] - [n])%Z.
Proof. intros H; case (sub_sub1_correct m n); auto with zarith. Qed.

Lemma sub1_correct m n :
  ([n] < [m])%Z -> [m -1 n] = ([m] - [n] - 1)%Z.
Proof. intros H; case (sub_sub1_correct m n); auto with zarith. Qed.

Definition add_mod p m n :=
  let res := m + n in
  match cp_num res p with
  | Lt => res
  | _  => res - p
  end.

Lemma add_mod_correct p m n :
  (0 <= [m] < [p] -> 0 <= [n] < [p] ->
       [add_mod p m n] = ([m] + [n]) mod [p])%Z.
Proof.
intros H1 H2; unfold add_mod.
case cp_spec; rewrite add_correct; intros H3;
  try rewrite sub_correct; try rewrite add_correct; auto with zarith.
rewrite H3, Z_mod_same_full; auto with zarith.
rewrite Zmod_small; auto with zarith.
rewrite <-(fun x y => (Zmod_small (x - y) [p])); auto with zarith.
rewrite Zminus_mod, Z_mod_same_full, Zminus_0_r, Zmod_mod; auto.
Qed.

Lemma add_mod_bound p m n :
  (0 <= [m] < [p] -> 0 <= [n] < [p] ->
       0 <= [add_mod p m n] < [p])%Z.
Proof.
intros H1 H2; rewrite add_mod_correct; auto.
apply Z_mod_lt; auto with zarith.
Qed.

Definition sub_mod p m n :=
  match cp_num m n with
  | Lt => (p + m) - n
  | _  => m - n
  end.

Lemma sub_mod_correct p m n :
  (0 <= [m] < [p] -> 0 <= [n] < [p] ->
       [sub_mod p m n] = ([m] - [n]) mod [p])%Z.
Proof.
intros H1 H2; unfold sub_mod.
case cp_spec; intros H3.
rewrite H3, Zminus_diag, Zmod_0_l, sub_correct, H3; auto with zarith.
rewrite sub_correct; rewrite add_correct; auto with zarith.
rewrite <-(fun x y => (Zmod_small (x - y) [p])); auto with zarith.
rewrite Zminus_mod, Zplus_mod, Z_mod_same_full, Zplus_0_l,
        Zmod_mod, <- Zminus_mod; auto.
rewrite Zmod_small, sub_correct; auto with zarith.
Qed.

Lemma sub_mod_bound p m n :
  (0 <= [m] < [p] -> 0 <= [n] < [p] ->
       0 <= [sub_mod p m n] < [p])%Z.
Proof.
intros H1 H2; rewrite sub_mod_correct; auto.
apply Z_mod_lt; auto with zarith.
Qed.

Definition amd (A: Type) (a b c: int31) (f: int31 -> int31 -> A): A :=
match a *c b with
| W0 => f c 0
| WW resh resl =>
    let u := (resl + c)%int31 in
    match u ?= resl with
    | Lt => f u (incr resh)
    | _ => f u resh
    end
end.

Fixpoint amd_num (a b: int31) (n: number): number :=
match n with
| nil => b :: nil
| c::n1 => amd _ a c b
    (fun xl xh =>
       xl :: amd_num a xh n1)
end.

Lemma amd_correct a b n :
  [amd_num a b n] = (phi a * [n] + phi b)%Z.
Proof.
generalize a b; clear a b;
  induction n as [ | c n1 Hrec]; intros a b;
  unfold amd_num; fold amd_num; nrom; nrom.
ring.
unfold amd; generalize (spec_mul_c a c); nrom;
  case (_ *c _); simpl zn2z_to_Z.
intros H1; nrom; rewrite Hrec; nrom.
repeat rewrite Zmult_plus_distr_r; rewrite <- H1.
ring.
intros xh xl Hx; generalize (add_cp xl b); case (_ ?= _);
  intros H1; nrom; rewrite H1, Hrec;
  repeat rewrite Zmult_plus_distr_r; rewrite <- Hx; try ring.
replace (phi (incr xh)) with (phi xh + 1)%Z; try ring.
case (phi_bounded a); nrom; intros H1a H2a.
case (phi_bounded c); nrom; intros H1c H2c.
case (phi_bounded xl); nrom; intros H1xl H2xl.
rewrite phi_incr, Zmod_small; nrom; auto with zarith.
case (phi_bounded xh); nrom; intros H1xh H2xh; split; auto with zarith.
assert (HH: (phi a * phi c <= (wB - 1) * (wB - 1))%Z).
apply Zmult_le_compat; auto with zarith.
replace ((wB - 1) * (wB - 1))%Z with
    (1 + wB * (wB - 2) )%Z in HH;try ring.
rewrite <-Hx, Zmult_comm, Zplus_comm in HH.
assert (HH1: (0 <= 1 < wB)%Z);
  case (phi_bounded 1); nrom; auto with zarith.
generalize (base_lexi_order (phi xl) 1 (phi xh) (wB - 2) wB
             (phi_bounded xl) HH1).
case (Zle_lt_or_eq _ _ HH); intros HH2.
red in HH2; rewrite HH2; auto with zarith.
rewrite HH2, Z.compare_refl; auto with zarith.
Qed.

Definition scal_num (a : int31) (n : number) : number :=
  amd_num a 0 n.

Lemma scal_correct a n :
  [scal_num a n] = (phi a * [n])%Z.
Proof. unfold scal_num; rewrite amd_correct; nrom; ring. Qed.

Fixpoint prod_num (m n : number) : number :=
  match n with
  | nil     => nil
  | a :: n1 => match scal_num a m with
               | nil     => 0 :: prod_num m n1
               | b :: n2 => b :: add_num n2 (prod_num m n1)
               end
  end.

Lemma prod_correct m n : [prod_num m n] = ([m] * [n])%Z.
Proof.
induction n as [ | a n Hrec]; unfold prod_num;
  fold prod_num.
nrom; ring.
generalize (scal_correct a m); case scal_num; nrom.
rewrite Hrec; intros HH.
rewrite Zmult_plus_distr_r, (Zmult_comm [m]), (Zmult_comm [m]),
        <-HH; ring.
intros i l; nrom; intros HH.
rewrite add_correct, Hrec, Zmult_plus_distr_r, Zplus_assoc, HH;
  ring.
Qed.

Fixpoint exp_num (m : number) (n : nat) : number :=
  match n with
  | O    => 1 :: nil
  | S n1 => prod_num m (exp_num m n1)
  end.

Lemma exp_correct m n: [exp_num m n] = Zpower_nat [m] n.
Proof.
induction n as [ | n Hrec]; unfold exp_num; fold exp_num.
nrom; nrom; unfold Zpower_nat; simpl; auto.
change (S n) with (1 + n)%nat; rewrite Zpower_nat_is_exp.
rewrite prod_correct, Hrec; change (Zpower_nat [m] 1) with ([m] * 1)%Z.
ring.
Qed.

Definition shift_num (t : number) : number :=
  match t with nil => nil | a :: t1 => t1 end.

Lemma shift_correct t : [shift_num t] = ([t] / wB)%Z.
Proof.
destruct t as [ | a t]; unfold shift_num; nrom.
rewrite Zdiv_0_l; auto.
case (phi_bounded a); nrom; intros H1a H2a.
rewrite Zmult_comm, Z_div_plus_full; auto with zarith.
rewrite Zdiv_small; auto with zarith.
Qed.

Section Reduce.

Variable M : number.
Variable m' : int31.
Hypothesis Hmm' : (phi (nhead M * m') = wB - 1)%Z.

Lemma M_pos : (0 < [M])%Z.
Proof.
rewrite phi_head_tail.
nrom; case (phi_bounded (nhead M)); nrom; intros H1a H2a.
case (Zle_lt_or_eq _ _ H1a); intros H3a.
assert (Hms := phi_pos (ntail M)).
apply Z.lt_le_trans with (phi (nhead M) + wB * 0)%Z; auto with zarith.
generalize Hmm'; rewrite spec_mul; nrom.
rewrite <-H3a, Zmult_0_l, Zmod_0_l; auto with zarith.
simpl; auto with zarith.
Qed.

Fixpoint reduce_aux_num (n : nat) (t : number)  :=
  match n with
  |    O => t
  | S n1 =>
     match t with
     | nil    => t
     | a :: _ =>
         reduce_aux_num n1
            (shift_num (add_num t (scal_num (a * m') M)))
     end
  end.

Lemma reduce_aux_step a t :
  ((phi a + wB * [t] + phi (a * m') * [M]) / wB * wB =
   phi a + wB * [t] + phi (a * m') * [M])%Z.
Proof.
case (phi_bounded a); nrom; intros H1a H2a.
rewrite (phi_head_tail M); nrom.
set (m := nhead M); set (ms := ntail M).
replace (phi a + wB * [t] + phi (a * m') * (phi m + wB * [ms]))%Z
  with ((phi a + phi (a * m') * phi m) + ([t] +  phi (a * m') * [ms]) * wB)%Z;
  try ring.
rewrite Z_div_plus_full; auto with zarith.
set (v := (phi a + phi (a * m') * phi m)%Z).
assert (HH: (v / wB * wB = v)%Z).
rewrite (Z_div_mod_eq_full v wB); auto with zarith.
rewrite (Zmult_comm wB), Z_div_plus_full_l; auto with zarith.
assert (HH: (v mod wB = 0)%Z); auto with zarith.
unfold v; rewrite spec_mul; nrom.
rewrite Zplus_mod, Zmult_mod, Zmod_mod, <- Zmult_mod, <- Zmult_assoc,
        Zmult_mod.
unfold m.
generalize Hmm'; rewrite spec_mul; nrom; intros HH1; rewrite (Zmult_comm (phi m')), HH1.
rewrite (Zmult_mod (phi a mod wB)), Zmod_mod, <- Zmult_mod, <- Zplus_mod.
replace (phi a + phi a * (wB - 1))%Z with (phi a * wB)%Z; try ring.
rewrite Z_mod_mult; auto.
rewrite Zmult_plus_distr_l, HH, Zdiv_0_l, Zmult_0_l, <-HH,
        Zmult_comm, <- Z_div_mod_eq_full; auto with zarith.
rewrite Zmult_plus_distr_l, HH; unfold v.
nrom; ring.
Qed.

Lemma reduce_aux_correct n t :
  ([reduce_aux_num n t] * (Zpower_nat wB n) mod [M] = [t]  mod [M])%Z.
Proof.
generalize t; clear t.
induction n as [ | n Hrec]; intros t.
assert (HH := phi_pos t).
simpl reduce_aux_num; repeat rewrite Zpower_nat_0;
  repeat rewrite Zmult_1_r; auto.
repeat rewrite Zpower_nat_S.
simpl reduce_aux_num; case t.
nrom; rewrite Zmod_small, Zmult_0_l; auto with zarith.
rewrite Zmult_0_l; auto with zarith.
generalize M_pos; auto with zarith.
intros a t1.
rewrite (Zmult_comm wB), Zmult_assoc, Zmult_mod, Hrec,
        <- Zmult_mod, shift_correct, add_correct, scal_correct.
nrom.
rewrite reduce_aux_step, Zplus_mod, Z_mod_mult, Zplus_0_r, Zmod_mod; auto.
Qed.

Lemma reduce_aux_le n t :
  ([t] < [M] * (Zpower_nat wB n) -> [reduce_aux_num n t] < 2 * [M])%Z .
Proof.
intros Ht.
assert (HH: (exists U, [reduce_aux_num n t] * Zpower_nat wB n = [t] + U * [M]
                    /\ 0 <= U < Zpower_nat wB n)%Z).
generalize t; clear t Ht; induction n as [ | n Hrec]; intros t.
assert (HM := phi_pos M).
simpl reduce_aux_num; repeat rewrite Zpower_nat_0;
  repeat rewrite Zmult_1_r; auto with zarith.
exists 0%Z; auto with zarith.
repeat rewrite Zpower_nat_S.
assert (HH2 := Zpower_base_pos n).
simpl reduce_aux_num; case t; nrom.
exists 0%Z; split. auto with zarith.
split. auto with zarith. apply Zmult_lt_0_compat. 2: assumption.
red; auto.
intros a t1; nrom.
case (Hrec (shift_num (add_num (a :: t1) (scal_num (a * m') M)))).
intros U (H1U, H2U); exists (phi(a * m') + wB * U)%Z; split.
rewrite (Zmult_comm wB), Zmult_assoc, H1U,
         shift_correct, add_correct, scal_correct; nrom.
rewrite Zmult_plus_distr_l, reduce_aux_step; ring.
case (phi_bounded (a * m')); nrom; intros H1am H2am.
split. auto with zarith.
apply Z.lt_le_trans with (wB + wB * U)%Z. auto with zarith.
replace (wB * Zpower_nat wB n)%Z with
        (wB + wB * (Zpower_nat wB n - 1))%Z by ring; auto with zarith.
apply Zmult_gt_0_lt_reg_r with (1 := Z.lt_gt _ _ (Zpower_base_pos n)).
case HH; intros U (H1U, H2U).
rewrite H1U.
assert (U * [M] < [M] * Zpower_nat wB n)%Z.
rewrite Zmult_comm; apply Zmult_gt_0_lt_compat_l.
apply Z.lt_gt; apply M_pos.
auto with zarith.
replace (2 * [M] * Zpower_nat wB n)%Z with
       ([M] * Zpower_nat wB n + [M] * Zpower_nat wB n)%Z; auto with zarith;
  ring.
Qed.

Definition reduce_num (n : nat) (t : number) : number :=
  let res := reduce_aux_num n t in
  match cp_num res M with
  | Lt => res
  | _ => sub_num res M
  end.

Lemma reduce_correct n t :
  ([reduce_num n t] * (Zpower_nat wB n) mod [M] = [t]  mod [M])%Z.
Proof.
assert (H:= M_pos).
assert (HH:= reduce_aux_correct n t).
unfold reduce_num; case cp_spec; intros HH1; auto with zarith;
  rewrite sub_correct, Zmult_minus_distr_r; auto with zarith.
rewrite (Zmult_comm [M]); unfold Zminus.
rewrite Zopp_mult_distr_l, Z_mod_plus; auto with zarith.
rewrite (Zmult_comm [M]); unfold Zminus.
rewrite Zopp_mult_distr_l, Z_mod_plus; auto with zarith.
Qed.

Lemma reduce_bound n t :
  ([t] < [M] * (Zpower_nat wB n) ->
  0 <= [reduce_num n t] < [M])%Z.
Proof.
intros Ht; split.
apply phi_pos.
assert (HH := reduce_aux_le _ _ Ht).
unfold reduce_num; case cp_spec; intros HH1; auto with zarith;
  rewrite sub_correct; auto with zarith.
Qed.

Definition T n := reduce_num n (1%int31::nil).

Lemma Tn_correct n :
  ([T n] * (Zpower_nat wB n) mod [M] = 1 mod[M])%Z.
Proof.
unfold T; rewrite reduce_correct; nrom; nrom.
rewrite Zmult_0_r, Zplus_0_r; auto with zarith.
Qed.

Lemma eq_Tn_correct a b n :
  ((a * Zpower_nat wB n) mod [M] = (b * Zpower_nat wB n) mod [M] ->
    a mod [M] = b mod [M])%Z.
Proof.
intros H.
assert (HH: ((a - b) mod [M] = 0)%Z).
rewrite <- (Zmult_1_r (a - b)), Zmult_mod, <- (Tn_correct n),
        <- Zmult_mod, (Zmult_comm [T n]), Zmult_assoc,
        Zmult_minus_distr_r, Zmult_mod, Zminus_mod, H,
        <- Zminus_mod, <- Zmult_mod, Zminus_diag, Zmult_0_l,
        Zmod_0_l; auto.
replace a with (b + (a - b))%Z; try ring.
rewrite Zplus_mod, HH, Zplus_0_r, Zmod_mod; auto.
Qed.

Fixpoint reduce_amd_aux_num (n : nat) (t1 t2 res : number) {struct n} :=
  match n with
  | O    => add_num res (prod_num t1 t2)
  | S n1 =>
    match t1 with
    |     nil => reduce_aux_num n res
    | a :: t3 =>
      let res1 := add_num res (scal_num a t2) in
      match res1 with
      | nil    => reduce_amd_aux_num n1 t3 t2 nil
      | b :: _ =>
        reduce_amd_aux_num n1 t3 t2
            (shift_num (add_num res1 (scal_num (b * m') M)))
      end
    end
  end.

Lemma reduce_amd_aux_correct n t1 t2 res :
 (([reduce_amd_aux_num n t1 t2 res] * Zpower_nat wB n) mod [M] =
  ([t1] * [t2] + [res]) mod [M])%Z.
Proof.
generalize t1 t2 res; clear t1 t2 res.
induction n as [ |n1 Hrec]; intros t1 t2 res;
   unfold reduce_amd_aux_num; fold reduce_amd_aux_num.
rewrite Zpower_nat_0, Zmult_1_r, add_correct, prod_correct, Zplus_comm; auto.
destruct t1 as [ | a t3]; nrom.
rewrite Zmult_0_l, Zplus_0_l, reduce_aux_correct; auto.
set (v :=  add_num res (scal_num a t2)).
assert (Hv: [v] = ([res] + phi a * [t2])%Z).
unfold v; rewrite add_correct, scal_correct; auto.
generalize Hv; destruct v as [ | b v1]; nrom; clear Hv; intros Hv.
rewrite Zpower_nat_S, (Zmult_comm wB), Zmult_assoc, Zmult_mod, Hrec.
nrom; rewrite Zplus_0_r, <- Zmult_mod.
apply f_equal2 with (f := Zmod); auto.
rewrite <- Zminus_0_r, Hv; ring.
rewrite Zpower_nat_S, (Zmult_comm wB), Zmult_assoc, Zmult_mod, Hrec.
rewrite <- Zmult_mod, shift_correct, add_correct, scal_correct; nrom.
rewrite Zmult_plus_distr_l, reduce_aux_step.
rewrite Zplus_assoc, Z_mod_plus_full.
apply f_equal2 with (f := Zmod); auto.
rewrite Hv; ring.
Qed.

Lemma reduce_amd_aux_le n t1 t2 res :
  ([t1] < Zpower_nat wB n -> [t2] < [M] ->
  [res] <  2 * [M]  - 1 -> [reduce_amd_aux_num n t1 t2 res] < 2 * [M])%Z.
Proof.
generalize t1 t2 res; clear t1 t2 res.
induction n as [ |n1 Hrec]; intros t1 t2 res;
   unfold reduce_amd_aux_num; fold reduce_amd_aux_num.
rewrite Zpower_nat_0; intros H1t1 Ht2 Hres.
assert (H2t1 := phi_pos t1).
rewrite add_correct, prod_correct.
replace [t1] with 0%Z; auto with zarith.
destruct t1 as [ | a t3].
intros _ Ht2 Hres.
apply reduce_aux_le.
apply Z.lt_le_trans with (1 := Hres).
apply Z.le_trans with (2 * [M])%Z; auto with zarith.
rewrite Zmult_comm.
apply Zmult_le_compat_l.
apply Z.le_trans with wB; try (red; discriminate).
rewrite <- (Zmult_1_r wB) at 1; rewrite Zpower_nat_S.
apply Zmult_le_compat_l.
generalize (Zpower_base_pos n1); auto with zarith.
red; discriminate.
apply Zlt_le_weak; apply M_pos.
nrom; intros Ht3 Ht2 Hres.
set (v :=  add_num res (scal_num a t2)).
assert (Hv: [v] = ([res] + phi a * [t2])%Z).
unfold v; rewrite add_correct, scal_correct; auto.
generalize Hv; destruct v as [ | b v1]; nrom; clear Hv; intros Hv.
apply Hrec; auto with zarith.
apply Zmult_lt_reg_r with wB; auto with zarith; try (red; auto; fail).
repeat rewrite <- (Zmult_comm wB); apply Z.le_lt_trans with (2 := Ht3).
case (phi_bounded a); auto with zarith.
nrom; generalize M_pos; auto with zarith.
apply Hrec; auto with zarith.
apply Zmult_lt_reg_r with wB; auto with zarith; try (red; auto; fail).
repeat rewrite <- (Zmult_comm wB); apply Z.le_lt_trans with (2 := Ht3).
case (phi_bounded a); auto with zarith.
rewrite shift_correct, add_correct, scal_correct; nrom.
rewrite Hv.
apply Zdiv_lt_upper_bound; try (red; auto; fail); auto with zarith.
repeat apply Zplus_le_0_compat; repeat apply Zmult_le_0_compat;
  try apply phi_pos; try (red; discriminate).
case (phi_bounded a); nrom; intros H1a H2a.
case (phi_bounded (b * m')); nrom; intros H1bm H2bm.
apply Z.le_lt_trans with
  (((2 * [M] - 2) + (wB - 1) * ([M] - 1) + (wB - 1) * [M])%Z).
repeat apply Zplus_le_compat; auto with zarith.
apply Zmult_le_compat; auto with zarith.
apply phi_pos.
apply Zmult_le_compat; auto with zarith.
apply Zlt_le_weak; apply M_pos.
ring_simplify; auto with zarith.
Qed.

Definition reduce_mult_num (n: nat) (t1 t2 : number) :=
  let res := reduce_amd_aux_num n t1 t2 nil in
  match cp_num res M with
  | Lt => res
  | _ => sub_num res M
  end.

Lemma reduce_mult_correct n t1 t2 :
 ([reduce_mult_num n t1 t2] * (Zpower_nat wB n) mod [M] =
  ([t1] * [t2])  mod [M])%Z.
Proof.
assert (H:= M_pos).
generalize (reduce_amd_aux_correct n t1 t2 nil).
nrom; rewrite Zplus_0_r; intros HH.
unfold reduce_mult_num; case cp_spec; intros HH1; auto with zarith;
  rewrite sub_correct, Zmult_minus_distr_r; auto with zarith.
rewrite (Zmult_comm [M]); unfold Zminus.
rewrite Zopp_mult_distr_l, Z_mod_plus; auto with zarith.
rewrite (Zmult_comm [M]); unfold Zminus.
rewrite Zopp_mult_distr_l, Z_mod_plus; auto with zarith.
Qed.

Lemma reduce_mult_bound n t1 t2 :
  ([t1] < Zpower_nat wB n -> [t2] < [M] ->
  0 <= [reduce_mult_num n t1 t2] < [M])%Z.
Proof.
intros Ht1 Ht2; split.
apply phi_pos.
assert (Hres: ([nil] < 2 * [M] - 1)%Z).
  nrom; generalize M_pos; auto with zarith.
assert (HH := reduce_amd_aux_le _ _ _ _ Ht1 Ht2 Hres).
unfold reduce_mult_num; case cp_spec; intros HH1; auto with zarith;
  rewrite sub_correct; auto with zarith.
Qed.

Definition r_square n :=
 Z_to_num ((Zpower_nat wB  n * Zpower_nat wB n) mod [M]).

Lemma r_square_lt n : (0 <= [r_square n] < [M])%Z.
Proof.
unfold r_square.
rewrite num_phi; auto with zarith.
apply Z_mod_lt; auto with zarith.
apply Z.lt_gt; apply M_pos.
case (Z_mod_lt (Zpower_nat wB n * Zpower_nat wB n) [M]);
  auto with zarith.
apply Z.lt_gt; apply M_pos.
Qed.

Definition encode n z : number :=
  reduce_mult_num n (Z_to_num (z mod [M])) (r_square n).

Definition decode n m :=  [reduce_num n m].

Variable n : nat.

Hypothesis M_small : ([M] < Zpower_nat wB n)%Z.

Let HF0 := M_pos.
Let HF1:  (0 <= (Zpower_nat wB n * Zpower_nat wB n) mod [M])%Z.
Proof.
case (Z.mod_pos_bound (Zpower_nat wB n * Zpower_nat wB n) [M]); auto with zarith.
Qed.

Lemma reduce_bound_small t :
  (0 <= [t] < [M] -> 0 <= [reduce_num n t] < [M])%Z.
Proof.
intros Ht; apply reduce_bound.
case Ht; intros _ Ht1; apply Z.lt_le_trans with (1 := Ht1).
rewrite <-(Zmult_1_r [M]) at 1.
apply Zmult_le_compat_l; auto with zarith.
Qed.

Hint Resolve reduce_bound_small add_mod_bound sub_mod_bound : core.

Lemma reduce_mult_bound_small t1 t2 :
  (0 <= [t1] < [M] -> 0 <= [t2] < [M] ->
   0 <= [reduce_mult_num n t1 t2] < [M])%Z.
Proof.
intros Ht1 Ht2; apply reduce_mult_bound; auto with zarith.
Qed.

Hint Resolve reduce_mult_bound_small : core.

Lemma encode_correct z :
  (0 <= z < [M] -> [encode n z] = (z * Zpower_nat wB n) mod [M])%Z.
Proof.
intros Hz.
unfold encode; rewrite Zmod_small; auto with zarith.
rewrite <-(Zmod_small _ [M]); auto with zarith.
apply (eq_Tn_correct _ _ n).
rewrite reduce_mult_correct.
unfold r_square.
rewrite !num_phi; auto with zarith.
rewrite Zmult_mod, Zmod_mod, <-Zmult_mod, Zmult_assoc; auto with zarith.
apply reduce_mult_bound_small; auto with zarith.
rewrite num_phi; auto with zarith.
unfold r_square.
rewrite num_phi; auto with zarith.
apply Z_mod_lt; auto with zarith.
Qed.

Lemma encode_bound z :
  (0 <= z < [M] -> 0 <= [encode n z] < [M])%Z.
Proof.
intros Hz.
rewrite encode_correct; auto with zarith.
apply Z_mod_lt; auto with zarith.
Qed.

Hint Resolve encode_bound : core.

Lemma decode_encode p :
  (0 <= p < [M])%Z -> decode n (encode n p) = p.
Proof.
intros Hp.
unfold decode, encode.
assert (F1 : (0 <= [Z_to_num (p mod [M])] < [M])%Z).
  rewrite num_phi; auto with zarith.
  rewrite Zmod_small; auto with zarith.
  case (Z.mod_pos_bound p [M]); auto with zarith.
assert (F2: ([Z_to_num (p mod [M])] < Zpower_nat wB n)%Z).
  apply (Z.lt_trans _ [M]); auto with zarith.
assert (F3: ([r_square n] < [M])%Z).
  case (r_square_lt n); auto.
generalize (reduce_mult_bound _ _ _ F2 F3); intros F4.
rewrite <-(Zmod_small p [M]); auto with zarith.
rewrite <-(Zmod_small _ [M]).
apply (eq_Tn_correct _ _ n).
rewrite reduce_correct.
apply (eq_Tn_correct _ _ n).
rewrite reduce_mult_correct.
unfold r_square.
rewrite !num_phi; auto with zarith.
rewrite Zmod_mod, <-Zmult_mod, Zmult_assoc; auto.
case (Z.mod_pos_bound (Zpower_nat wB n * Zpower_nat wB n) [M]);
  auto with zarith.
case (Z.mod_pos_bound (p mod [M]) [M]); auto with zarith.
case (Z.mod_pos_bound p [M]); auto with zarith.
intros; apply reduce_bound_small.
rewrite Zmod_mod; auto with zarith.
Qed.

Lemma decode_encode_add p1 p2 :
  (0 <= p1 < [M])%Z -> (0 <= p2 < [M])%Z ->
  decode n (add_mod M (encode n p1) (encode n p2)) = ((p1 + p2) mod [M])%Z.
Proof.
intros Hp1 Hp2.
rewrite <-(Zmod_small _ [M]).
apply (eq_Tn_correct _ _ n).
unfold decode; rewrite reduce_correct.
rewrite add_mod_correct; auto with zarith.
rewrite !encode_correct; auto with zarith.
rewrite <-Zplus_mod, Zmod_mod, Zmult_plus_distr_l; auto with zarith.
unfold decode; auto with zarith.
Qed.

Lemma decode_encode_sub p1 p2 :
  (0 <= p1 < [M])%Z -> (0 <= p2 < [M])%Z ->
  decode n (sub_mod M (encode n p1) (encode n p2)) = ((p1 - p2) mod [M])%Z.
Proof.
intros Hp1 Hp2.
rewrite <-(Zmod_small _ [M]).
apply (eq_Tn_correct _ _ n).
unfold decode; rewrite reduce_correct.
rewrite sub_mod_correct; auto with zarith.
rewrite !encode_correct; auto with zarith.
rewrite <-Zminus_mod, Zmod_mod, Zmult_minus_distr_r; auto with zarith.
unfold decode; auto with zarith.
Qed.

Lemma decode_encode_mult p1 p2 :
  (0 <= p1 < [M])%Z -> (0 <= p2 < [M])%Z ->
  decode n (reduce_mult_num n (encode n p1) (encode n p2))
     = ((p1 * p2) mod [M])%Z.
Proof.
intros Hp1 Hp2.
rewrite <-(Zmod_small _ [M]).
apply (eq_Tn_correct _ _ n).
unfold decode; rewrite reduce_correct.
apply (eq_Tn_correct _ _ n).
rewrite reduce_mult_correct.
rewrite !encode_correct by auto with zarith.
rewrite <-Zmult_mod. apply f_equal2 with (f := Zmod).
ring.
reflexivity.
unfold decode; auto with zarith.
Qed.

End Reduce.
