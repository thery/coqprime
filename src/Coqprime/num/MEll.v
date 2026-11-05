
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)


From Stdlib Require Import ZArith Lia Znumtheory Zpow_facts Uint63.
From Stdlib Require Import Zmod.
From Coqprime Require Import ZEll montgomery.

(* NEll with Montgomery arithmetic: the elements of Z/NZ are the numbers
   of montgomery.v (lists of 63-bit words) in Montgomery form. *)


Set Implicit Arguments.

Open Scope Z_scope.


Record ex: Set := mkEx {
  vN : positive;
  vS : positive;
  vR:  List.list (positive * positive);
  vA:  Z;
  vB:  Z;
  vx:  Z;
  vy:  Z
}.

Local Coercion Zpos : positive >-> Z.

Record ex_spec (exx: ex): Prop := mkExS {
  n2_div: ~(2 | exx.(vN));
  n_pos: 2 < exx.(vN);
 lprime:
  forall p : positive * positive, List.In p (vR exx) -> prime (fst p);
   lbig:
    4 * vN exx < (Zmullp (vR exx) - 1) ^ 2;
   inC:
    vy exx ^ 2 mod vN exx = (vx exx ^ 3 + vA exx * vx exx + vB exx) mod vN exx
}.

Section InvM.

Local Open Scope uint63_scope.

(* invM m v: the x such that v * x = m modulo 2^63, for an odd v,
   computed bit by bit from the low bit. *)
Fixpoint invM_aux (n : nat) (m v : int) : int :=
  match n with
  | O => 0
  | S n =>
    if is_even m then (invM_aux n (m >> 1) v) << 1
    else 1 lor ((invM_aux n ((m - v) >> 1) v) << 1)
  end.

Definition invM := invM_aux 63.

Local Open Scope Z_scope.

Lemma wB_pow : wB = 2 ^ 63.
Proof. reflexivity. Qed.

(* 2^n divides wB when n <= 63 *)
Lemma pow_divide_wB (n : nat) : (n <= 63)%nat -> (2 ^ Z.of_nat n | wB).
Proof.
intros Hn; rewrite wB_pow.
assert (H : 63 = Z.of_nat n + (63 - Z.of_nat n)) by lia.
rewrite H, Z.pow_add_r by lia.
apply Z.divide_factor_l.
Qed.

(* reducing modulo wB first changes nothing modulo 2^n *)
Lemma mod_wB_pow a (n : nat) : (n <= 63)%nat ->
  (a mod wB) mod 2 ^ Z.of_nat n = a mod 2 ^ Z.of_nat n.
Proof. intros Hn; apply Z.mod_mod_divide, pow_divide_wB, Hn. Qed.

Lemma mul_mod_wB_r a b (n : nat) : (n <= 63)%nat ->
  (a * (b mod wB)) mod 2 ^ Z.of_nat n = (a * b) mod 2 ^ Z.of_nat n.
Proof.
intros Hn; rewrite <- (mod_wB_pow (a * (b mod wB))), <- (mod_wB_pow (a * b))
  by exact Hn.
rewrite Z.mul_mod_idemp_r; [reflexivity | rewrite wB_pow; lia].
Qed.

Lemma add_mod_wB_l a b (n : nat) : (n <= 63)%nat ->
  ((a mod wB) + b) mod 2 ^ Z.of_nat n = (a + b) mod 2 ^ Z.of_nat n.
Proof.
intros Hn; rewrite <- (mod_wB_pow (a mod wB + b)), <- (mod_wB_pow (a + b))
  by exact Hn.
rewrite Z.add_mod_idemp_l; [reflexivity | rewrite wB_pow; lia].
Qed.

(* or-ing 1 into an even number adds 1 *)
Lemma lor_1_even k : Z.lor 1 (2 * k) = 2 * k + 1.
Proof.
assert (Hland : Z.land 1 (2 * k) = 0).
{ rewrite Z.land_comm.
  assert (H1 : 1 = Z.ones 1) by reflexivity.
  rewrite H1, Z.land_ones by lia.
  rewrite Z.pow_1_r, Z.mul_comm, Z.mod_mul; lia. }
rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact Hland.
lia.
Qed.

Lemma invM_aux_spec (n : nat) m v : (n <= 63)%nat -> is_even v = false ->
  φ (v * invM_aux n m v)%uint63 mod 2 ^ Z.of_nat n = φ m mod 2 ^ Z.of_nat n.
Proof.
intros Hn Hv.
assert (Hvo : φ v mod 2 = 1).
{ generalize (is_even_spec v); rewrite Hv; auto. }
revert m; induction n as [| n IH]; intros m.
- rewrite !Z.mod_1_r; reflexivity.
- assert (Hn' : (n <= 63)%nat) by lia.
  assert (Hp : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
  assert (HS : 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n).
  { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring. }
  simpl invM_aux; rewrite mul_spec, mod_wB_pow by exact Hn.
  case_eq (is_even m); intros Hm.
  + (* m even: x = 2 x' with v x' = m / 2 *)
    assert (Hme : φ m mod 2 = 0).
    { generalize (is_even_spec m); rewrite Hm; auto. }
    set (x' := invM_aux n (m >> 1) v).
    assert (IHm := IH Hn' (m >> 1)); fold x' in IHm.
    rewrite mul_spec, mod_wB_pow, lsr_spec, to_Z_1 in IHm by exact Hn'.
    rewrite lsl_spec, to_Z_1, Z.pow_1_r, mul_mod_wB_r by exact Hn.
    rewrite Z.pow_1_r in IHm.
    assert (Hm2 : φ m = 2 * (φ m / 2)).
    { apply Z.div_exact; lia. }
    rewrite Hm2.
    rewrite HS.
    replace (φ v * (φ x' * 2)) with (2 * (φ v * φ x')) by ring.
    rewrite !Z.mul_mod_distr_l by lia.
    rewrite IHm; reflexivity.
  + (* m odd: x = 1 + 2 x' with v x' = (m - v) / 2 *)
    assert (Hmo : φ m mod 2 = 1).
    { generalize (is_even_spec m); rewrite Hm; auto. }
    set (x' := invM_aux n ((m - v) >> 1) v).
    assert (IHm := IH Hn' ((m - v) >> 1)); fold x' in IHm.
    rewrite mul_spec, mod_wB_pow, lsr_spec, sub_spec, to_Z_1 in IHm
      by exact Hn'.
    rewrite Z.pow_1_r in IHm.
    set (D := (φ m - φ v) mod wB) in IHm.
    assert (HD2 : D mod 2 = 0).
    { unfold D; rewrite Z.mod_mod_divide.
      - rewrite Zminus_mod, Hmo, Hvo; reflexivity.
      - rewrite wB_pow; exists (2 ^ 62); reflexivity. }
    assert (HD : D = 2 * (D / 2)).
    { apply Z.div_exact; lia. }
    rewrite lor_spec', to_Z_1, lsl_spec, to_Z_1, Z.pow_1_r.
    assert (Hx2 : (φ x' * 2) mod wB = 2 * ((φ x' * 2) mod wB / 2)).
    { apply Z.div_exact; [lia |].
      rewrite Z.mod_mod_divide.
      - apply Z.mod_mul; lia.
      - rewrite wB_pow; exists (2 ^ 62); reflexivity. }
    rewrite Hx2, lor_1_even, <- Hx2.
    assert (HpS : 2 ^ Z.of_nat (S n) <> 0) by lia.
    (* v * x' * 2 = D modulo 2^(n+1) *)
    assert (H2 : (φ v * (φ x' * 2)) mod 2 ^ Z.of_nat (S n)
                 = D mod 2 ^ Z.of_nat (S n)).
    { rewrite HS.
      replace (φ v * (φ x' * 2)) with (2 * (φ v * φ x')) by ring.
      rewrite HD.
      rewrite !Z.mul_mod_distr_l by lia.
      rewrite IHm; reflexivity. }
    rewrite Z.mul_add_distr_l, Z.mul_1_r.
    rewrite Z.add_mod by exact HpS.
    rewrite mul_mod_wB_r, H2 by exact Hn.
    rewrite <- Z.add_mod by exact HpS.
    (* (m - v) mod wB + v = m modulo 2^(n+1) *)
    unfold D; rewrite add_mod_wB_l by exact Hn.
    f_equal; ring.
Qed.

Lemma invM_spec m v : is_even v = false -> (v * invM m v)%uint63 = m.
Proof.
intros Hv; apply to_Z_inj.
generalize (@invM_aux_spec 63 m v (le_n 63) Hv).
change (2 ^ Z.of_nat 63) with wB.
rewrite !Z.mod_small by apply to_Z_bounded.
auto.
Qed.

End InvM.

(* a number of length k is smaller than wB^k *)
Lemma num_lt_length (l : number) : [l] < Zpower_nat wB (length l).
Proof.
induction l as [| a l IH].
- rewrite to_Z_nil; simpl; lia.
- rewrite to_Z_cons; simpl length; rewrite Zpower_nat_S.
  assert (Ha := to_Z_bounded a).
  assert (Hl := to_Z_pos l).
  assert (H : wB * ([l] + 1) <= wB * Zpower_nat wB (length l)).
  { apply Z.mul_le_mono_nonneg_l; lia. }
  lia.
Qed.

(* for an odd N, the Montgomery constant - (nhead M)^-1 mod 2^63 *)
Lemma mont_const (p : positive) : ~ (2 | Zpos p) ->
  let M := positive_to_num p in
  φ (nhead M * invM (0 - 1)%uint63 (nhead M))%uint63 = wB - 1.
Proof.
intros Hp M.
assert (Hodd : is_even (nhead M) = false).
{ generalize (is_even_spec (nhead M)); case_eq (is_even (nhead M));
    intros He Hs; [exfalso | reflexivity].
  apply Hp, Z.mod_divide; [lia |].
  unfold M; rewrite <- positive_to_Z, to_Z_head_tail, to_Z_cons.
  assert (HwB : wB = 2 ^ 62 * 2) by reflexivity.
  match goal with |- (?a + wB * ?b) mod 2 = 0 =>
    replace (a + wB * b) with (a + (2 ^ 62 * b) * 2) by (rewrite HwB; ring) end.
  rewrite Z_mod_plus_full; exact Hs. }
rewrite invM_spec by exact Hodd.
rewrite sub_spec, to_Z_0, to_Z_1; reflexivity.
Qed.

Section NEll.

Variable exx: ex.
Variable exxs: ex_spec exx.

(* The modulus N as a montgomery number MN, its Montgomery constant mM,
   its length nM in words and R^2 mod N: computed once by ell_test. *)
Variable MN : number.
Variable mM : int.
Variable nM : nat.
Variable rM : number.
Hypothesis MN_Z : [MN] = exx.(vN).
Hypothesis Hmm' : φ (nhead MN * mM)%uint63 = wB - 1.
Hypothesis M_small : [MN] < Zpower_nat wB nM.
Hypothesis HrM : rM = r_square MN nM.

(* An element of Z/NZ is stored in Montgomery form: z2Z reads it back. *)
Definition z2Z t := decode MN mM nM t.
Definition Z2z z := reduce_mult_num MN mM nM (Z_to_num (z mod exx.(vN))) rM.

Lemma Z2z_encode z : Z2z z = encode MN mM nM (z mod exx.(vN)).
Proof. unfold Z2z, encode; rewrite HrM, MN_Z, Zmod_mod; reflexivity. Qed.

Lemma vN_pos: 0 < exx.(vN).
Proof. red; simpl; auto. Qed.

Hint Resolve vN_pos : core.

Definition wft t := [t] mod [MN] = [t].

Lemma wft_iff t : wft t <-> 0 <= [t] < [MN].
Proof.
assert (H := to_Z_pos t); assert (HM : 0 < [MN]) by (rewrite MN_Z; auto).
unfold wft; split; intros Ht.
- rewrite <- Ht; apply Z.mod_pos_bound; lia.
- apply Zmod_small; lia.
Qed.

Definition RM := Zpower_nat wB nM.

Lemma RM_pos : 0 < RM.
Proof. apply Zpower_base_pos. Qed.

Lemma z2Z_bound t : wft t -> 0 <= z2Z t < exx.(vN).
Proof.
intros Ht; rewrite <- MN_Z.
apply (reduce_bound_small MN mM Hmm' nM M_small); apply wft_iff; exact Ht.
Qed.

Lemma z2Z_R t : (z2Z t * RM) mod exx.(vN) = [t] mod exx.(vN).
Proof. rewrite <- MN_Z; apply (reduce_correct MN mM Hmm'). Qed.

(* z2Z t is the only z in [0, N) with z * R = [t] modulo N *)
Lemma z2Z_char t z : wft t -> 0 <= z < exx.(vN) ->
  (z * RM) mod exx.(vN) = [t] mod exx.(vN) -> z2Z t = z.
Proof.
intros Ht Hz Hzt.
assert (Hb := z2Z_bound Ht).
assert (H : (z2Z t * RM) mod [MN] = (z * RM) mod [MN]).
{ rewrite MN_Z, Hzt; apply z2Z_R. }
generalize (eq_Tn_correct MN mM Hmm' (z2Z t) z nM H).
rewrite MN_Z, !Zmod_small by lia; auto.
Qed.

Definition nplus x y := add_mod MN x y.
Definition nsub x y := sub_mod MN x y.
Definition nmul x y := reduce_mult_num MN mM nM x y.
Definition neq x y := eq_num x y.


Definition S := exx.(vS).
Definition R := exx.(vR).
(* the constants used by the point operations: computed once by ell_test *)
Variable c0 c2 c3 A : number.
Hypothesis Hc0 : c0 = Z2z 0.
Hypothesis Hc2 : c2 = Z2z 2.
Hypothesis Hc3 : c3 = Z2z 3.
Hypothesis HA : A = Z2z exx.(vA).
Definition B := Z2z exx.(vB).
Definition xx := Z2z exx.(vx).
Definition yy := Z2z exx.(vy).
Definition c1 := Z2z 1.

Inductive nelt: Type :=
  nzero | ntriple: number -> number -> number  -> nelt.

Definition pp := ntriple xx yy c1.


Notation "x ++ y " := (nplus x y).
Notation "x -- y" := (nsub x y) (at level 50, left associativity).
Notation "x ** y" := (nmul x y) (at level 40, left associativity).
Notation "x ?= y" := (neq x y).

Definition ndouble: number -> nelt -> (nelt * number):= fun (sc: number) (p1: nelt) =>
 match p1 with
  nzero => (p1, sc)
 | (ntriple x1 y1 z1) =>
    if (y1 ?= c0) then (nzero, z1 ** sc) else
     (* we do 2p *)
    let m' := c3 ** x1 ** x1 ++ A ** z1 ** z1 in
    let l' := c2 ** y1 ** z1 in
    let m'2 := m' ** m' in
    let l'2 := l' ** l' in
    let l'3 := l'2 ** l' in
    let x3 := m'2 ** z1 -- c2 ** x1 ** l'2 in
    (ntriple
          (l' ** x3)
          (l'2 ** (m' ** x1 -- y1 ** l') -- m' ** x3)
          (z1 ** l'3), sc)
  end.


Definition nadd := fun (sc: number) (p1 p2: nelt) =>
 match p1, p2 with
  nzero, _ => (p2, sc)
 | _ , nzero => (p1, sc)
 | (ntriple x1 y1 z1), (ntriple x2 y2 z2) =>
  let d1 := x2 ** z1 in
  let d2 := x1 ** z2 in
  let l := d1 -- d2 in
  let dl := d1 ++ d2 in
  let m := y2 ** z1 -- y1 ** z2 in
  if (l ?= c0) then
   (* we have p1 = p2 o p1 = -p2 *)
   if (m ?= c0) then
    if (y1 ?= c0) then (nzero, z1 ** z2 ** sc) else
     (* we do 2p *)
    let m' := c3 ** x1 ** x1 ++ A ** z1 ** z1 in
    let l' := c2 ** y1 ** z1 in
    let m'2 := m' ** m' in
    let l'2 := l' ** l' in
    let l'3 := l'2 ** l' in
    let x3 := m'2 ** z1 -- c2 ** x1 ** l'2 in
    (ntriple
          (l' ** x3)
          (l'2 ** (m' ** x1 -- y1 ** l') -- m' ** x3)
          (z1 ** l'3), z2 ** sc)
    else (* p - p *)  (nzero, m ** z1 ** z2 ** sc)
  else
     let l2 := l ** l in
     let l3 := l2 ** l in
     let m2 := m ** m in
     let x3 := z1 ** z2 ** m2 -- l2 ** dl in
      (ntriple (l ** x3)
             (z2 ** l2 ** (m ** x1 -- y1 ** l) -- m ** x3)
             (z1 ** z2 ** l3), sc)
  end.


Definition nopp p :=
  match p with nzero => p | (ntriple x1 y1 z1) => (ntriple x1 (c0 -- y1) z1) end.

Fixpoint scalb (sc: number) (b:bool) (a: nelt) (p: positive) {struct p}:
 nelt * number :=
 match p with
   xH => if b then ndouble sc a else (a,sc)
 | xO p1 => let (a1, sc1) := scalb sc false a p1 in
              if b then
                let (a2, sc2) := ndouble sc1 a1 in
                nadd sc2 a a2
              else ndouble sc1 a1
 | xI p1 => let (a1, sc1) := scalb sc true a p1 in
              if b then  ndouble sc1 a1
              else
              let (a2, sc2) := ndouble sc1 a1 in
              nadd sc2 (nopp a) a2
 end.

Definition scal sc a p := scalb sc false a p.


Definition scal_list sc a l :=
  List.fold_left
  (fun (asc: nelt * number) p1 => let (a,sc) := asc in scal sc a p1) l (a,sc).

Fixpoint scalL (sc:number) (a: nelt) (l: List.list positive) {struct l}: (nelt * number) :=
   match l with
     List.nil => (a,sc)
   | List.cons n l1 =>
        let (a1, sc1) := scal sc a n in
        let (a2, sc2) := scal_list sc1 a l1 in
          match a2 with
             nzero => (nzero, c0)
          |  ntriple _ _ z => scalL (sc2 ** z) a1 l1
          end
   end.


Definition zpow sc p n :=
  let (p,sc') := scal sc p n in
  (p, Z.gcd (z2Z sc') exx.(vN)).

Definition e2E n :=
  match n with
    nzero => ZEll.nzero
  | ntriple x1 y1 z1 => ZEll.ntriple (z2Z x1) (z2Z y1) (z2Z z1)
  end.



Lemma nplusw: forall x y, wft x -> wft y ->  wft (x ++ y).
Proof. intros x y Hx Hy; apply wft_iff, add_mod_bound; apply wft_iff; auto. Qed.

Lemma nsubw: forall x y, wft x -> wft y ->  wft (x -- y).
Proof. intros x y Hx Hy; apply wft_iff, sub_mod_bound; apply wft_iff; auto. Qed.

Lemma nmulw: forall x y, wft x -> wft y ->  wft (x ** y).
Proof.
intros x y Hx Hy; apply wft_iff, (reduce_mult_bound_small MN mM Hmm' nM M_small);
  apply wft_iff; auto.
Qed.

Hint Resolve nmulw nplusw nsubw : core.

Lemma nplusz: forall x y, wft x -> wft y ->
      z2Z (x ++ y) = ZEll.nplus (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy; unfold ZEll.nplus.
apply z2Z_char; auto.
- apply Z.mod_pos_bound; auto.
- unfold nplus; rewrite add_mod_correct, MN_Z by (apply wft_iff; auto).
  rewrite Zmod_mod, Zmult_mod_idemp_l, Z.mul_add_distr_r.
  rewrite Z.add_mod, !z2Z_R, <- Z.add_mod by lia; reflexivity.
Qed.

Lemma nsubz: forall x y, wft x -> wft y ->
      z2Z (x -- y) = ZEll.nsub (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy; unfold ZEll.nsub.
apply z2Z_char; auto.
- apply Z.mod_pos_bound; auto.
- unfold nsub; rewrite sub_mod_correct, MN_Z by (apply wft_iff; auto).
  rewrite Zmod_mod, Zmult_mod_idemp_l, Z.mul_sub_distr_r.
  rewrite Zminus_mod, !z2Z_R, <- Zminus_mod; reflexivity.
Qed.

Lemma nmulz: forall x y, wft x -> wft y ->
      z2Z (x ** y) = ZEll.nmul (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy; unfold ZEll.nmul.
apply z2Z_char; auto.
- apply Z.mod_pos_bound; auto.
- rewrite Zmult_mod_idemp_l.
  (* cancel one factor RM: both sides times RM are [x] * [y] *)
  assert (H : ([x ** y] * RM) mod [MN] = (z2Z x * z2Z y * RM * RM) mod [MN]).
  { unfold nmul, RM; rewrite (reduce_mult_correct MN mM Hmm'); fold RM.
    replace (z2Z x * z2Z y * RM * RM) with ((z2Z x * RM) * (z2Z y * RM)) by ring.
    rewrite MN_Z, (Z.mul_mod (z2Z x * RM)), !z2Z_R, <- Z.mul_mod by lia;
    reflexivity. }
  generalize (eq_Tn_correct MN mM Hmm' _ _ nM H); rewrite MN_Z; auto.
Qed.

Definition wfe p := match p with
  ntriple x y z => wft x /\ wft y /\ wft z
| _ => True
end.


Lemma z2Zx: forall x, z2Z (Z2z x) = x mod exx.(vN).
Proof.
intros x; unfold z2Z; rewrite Z2z_encode.
rewrite (decode_encode MN mM Hmm' nM M_small); auto.
rewrite MN_Z; apply Z.mod_pos_bound; auto.
Qed.

Lemma z2Zx1: forall x, wft (Z2z x).
Proof.
intros x; rewrite Z2z_encode; apply wft_iff.
apply (encode_bound MN mM Hmm' nM M_small).
rewrite MN_Z; apply Z.mod_pos_bound; auto.
Qed.

Lemma c0w: wft c0.
Proof. rewrite Hc0; apply z2Zx1. Qed.

Lemma c2w: wft c2.
Proof. rewrite Hc2; apply z2Zx1. Qed.

Lemma c3w: wft c3.
Proof. rewrite Hc3; apply z2Zx1. Qed.

Lemma Aw: wft A.
Proof. rewrite HA; apply z2Zx1. Qed.

Hint Resolve c0w c2w c3w Aw : core.

Ltac nw :=
  repeat (apply c0w || apply c2w || apply c3w || apply Aw || apply z2Zx1 ||
          apply nplusw || apply nsubw || apply nmulw); auto.


Lemma nadd_wf: forall x y sc,
  wfe x -> wfe y -> wft sc ->
  wfe (fst (nadd sc x y)) /\  wft (snd (nadd sc x y)).
Proof.
intros x; case x; clear x; auto.
intros x1 y1 z1 y; case y; clear y; auto.
  intros x2 y2 z2 sc (wfx1,(wfy1, wfz1)) (wfx2,(wfy2, wfz2)) wfsc;
    simpl; auto.
   case neq.
    2: repeat split; simpl; nw.
   case neq.
    2: repeat split; simpl; nw.
   case neq.
   repeat split; simpl; nw; auto.
   repeat split; simpl; nw; auto.
Qed.


 Lemma ztest: forall x y, wft x -> wft y ->
     (x ?= y) = Z.eqb (z2Z x) (z2Z y).
 Proof.
 intros x y Hx Hy; unfold neq.
 generalize (eq_correct x y); case eq_num; intros Hxy.
 - assert (H : z2Z y = z2Z x).
   { apply z2Z_char; auto.
     - apply z2Z_bound; auto.
     - rewrite z2Z_R, Hxy; reflexivity. }
   rewrite H, Z.eqb_refl; reflexivity.
 - case Z.eqb_spec; auto; intros H; exfalso; apply Hxy.
   assert (H1 : [x] mod exx.(vN) = [y] mod exx.(vN)).
   { rewrite <- !z2Z_R, H; reflexivity. }
   revert H1; apply wft_iff in Hx; apply wft_iff in Hy; rewrite MN_Z in Hx, Hy.
   rewrite !Zmod_small; auto.
 Qed.

 Lemma zc0: z2Z c0 = 0.
 Proof. rewrite Hc0, z2Zx; apply Zmod_0_l. Qed.

Ltac iftac t :=
  match t with
   context[if ?x ?= ?y then _ else _] =>
      case_eq (x ?= y)
  end.

Ltac ftac := match goal with
  |- context[?x = ?y] => (iftac x);
    let H := fresh "tmp" in
     (try (rewrite ztest by nw); try rewrite zc0; intros H;
      repeat ((rewrite nmulz in H || rewrite nplusz in H || rewrite nsubz in H); auto);
      try (rewrite H; clear H))
    end.

Lemma c2ww: forall x, ZEll.nmul (vN exx) 2 x = ZEll.nmul (vN exx) (z2Z c2) x.
Proof.
intros x; unfold ZEll.nmul.
rewrite Hc2, z2Zx; rewrite Zmult_mod_idemp_l; auto.
Qed.
Lemma c3ww: forall x, ZEll.nmul (vN exx) 3 x = ZEll.nmul (vN exx) (z2Z c3) x.
Proof.
intros x; unfold ZEll.nmul.
rewrite Hc3, z2Zx; rewrite Zmult_mod_idemp_l; auto.
Qed.

Lemma Aww: forall x, ZEll.nmul (vN exx) exx.(vA) x = ZEll.nmul (vN exx) (z2Z A) x.
Proof.
intros x; unfold ZEll.nmul.
rewrite HA, z2Zx; rewrite Zmult_mod_idemp_l; auto.
Qed.

Lemma nadd_correct: forall x y sc,
  wfe x -> wfe y -> wft sc ->
  e2E (fst (nadd sc x y)) = fst (ZEll.nadd exx.(vN) exx.(vA) (z2Z sc) (e2E x) (e2E y) )/\
  z2Z (snd (nadd sc x y)) = snd (ZEll.nadd exx.(vN) exx.(vA) (z2Z sc) (e2E x) (e2E y)).
Proof.
intros x; case x; clear x; auto.
intros x1 y1 z1 y; case y; clear y; auto.
  intros x2 y2 z2 sc (wfx1,(wfy1, wfz1)) (wfx2,(wfy2, wfz2)) wfsc; simpl.
  ftac.
  ftac.
  ftac.
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz); auto).
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz||
           rewrite c2ww || rewrite c3ww || rewrite Aww); try nw; auto).
  rewrite nmulz; auto.
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz); auto).
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz ||
           rewrite c2ww || rewrite c3ww || rewrite Aww); try nw; auto).
  Qed.

 Lemma ndouble_wf: forall x sc,
  wfe x -> wft sc ->
  wfe (fst (ndouble sc x)) /\  wft (snd (ndouble sc x)).
Proof.
intros x; case x; clear x; auto.
intros x1 y1 z1 sc (wfx1,(wfy1, wfz1)) wfsc;
    simpl; auto.
  repeat (case neq; repeat split; simpl; nw; auto).
Qed.


Lemma ndouble_correct: forall x sc,
  wfe x -> wft sc ->
  e2E (fst (ndouble sc x)) = fst (ZEll.ndouble exx.(vN) exx.(vA) (z2Z sc) (e2E x))/\
  z2Z (snd (ndouble sc x)) = snd (ZEll.ndouble exx.(vN) exx.(vA) (z2Z sc) (e2E x)).
Proof.
intros x; case x; clear x; auto.
  intros x1 y1 z1 sc (wfx1,(wfy1, wfz1))  wfsc; simpl.
  ftac.
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz); auto).
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz ||
           rewrite c2ww || rewrite c3ww || rewrite Aww); try nw; auto).
  Qed.

Lemma nopp_wf: forall x, wfe x -> wfe (nopp x).
Proof.
intros x; case x; simpl nopp; auto.
intros x1 y1 z1 [H1 [H2 H3]]; repeat split; auto.
Qed.

Lemma scalb_wf: forall n b x sc,
  wfe x -> wft sc ->
  wfe (fst (scalb sc b x n)) /\  wft (snd (scalb sc b x n)).
Proof.
intros n; elim n; unfold scalb; fold scalb; auto.
  intros n1 Hrec b x sc H H1.
    case (Hrec true x sc H H1).
    case scalb; simpl fst; simpl snd.
    intros a1 sc1 H2 H3.
    case (ndouble_wf _ H2 H3); auto;
    case ndouble; simpl fst; simpl snd; intros x2 sc2 H4 H5.
    case b; auto.
    case (nadd_wf _ _ (nopp_wf _ H) H4 H5); auto;
    case ndouble; simpl fst; simpl snd; intros x2 sc2 H4 H5.
  intros n1 Hrec b x sc H H1.
    case (Hrec false x sc H H1).
    case scalb; simpl fst; simpl snd.
    intros a1 sc1 H2 H3.
    case (ndouble_wf _ H2 H3); auto;
    case ndouble; simpl fst; simpl snd; intros x2 sc2 H4 H5.
    case b; auto.
    case (nadd_wf _ _ H H4 H5); auto;
    case ndouble; simpl fst; simpl snd; intros x2 sc2 H4 H5.
intros b x sc H H1; case b; auto.
case (ndouble_wf _ H H1); auto.
Qed.


Lemma scal_wf: forall n x sc,
  wfe x -> wft sc ->
  wfe (fst (scal sc x n)) /\  wft (snd (scal sc x n)).
Proof.
intros n; exact (scalb_wf n false).
Qed.

Lemma nopp_correct: forall x,
  wfe x -> e2E x = ZEll.nopp exx.(vN) (e2E (nopp x)).
Proof.
intros x; case x; simpl; auto.
intros x1 y1 z1 [H1 [H2 H3]]; apply f_equal3 with (f := ZEll.ntriple); auto.
rewrite nsubz; auto.
rewrite zc0.
unfold ZEll.nsub, ninv; simpl.
apply sym_equal.
rewrite <- (Z_mod_plus) with (b := -(-z2Z y1 /exx.(vN))); auto with zarith.
rewrite <- Zopp_mult_distr_l.
rewrite <- Zopp_plus_distr.
rewrite Zmult_comm; rewrite Zplus_comm.
rewrite <- Z_div_mod_eq_full.
rewrite Z.opp_involutive.
apply Zmod_small, z2Z_bound; auto.
Qed.

Lemma scalb_correct: forall n b x sc,
  wfe x -> wft sc ->
  e2E (fst (scalb sc b x n)) = fst (ZEll.scalb exx.(vN) exx.(vA) (z2Z sc) b (e2E x) n)/\
  z2Z (snd (scalb sc b x n)) = snd (ZEll.scalb exx.(vN) exx.(vA) (z2Z sc) b (e2E x) n).
Proof.
intros n; elim n; clear n; auto.
intros p Hrec b x sc H1 H2.
  case b; unfold scalb; fold scalb.
    generalize (scalb_wf p true x H1 H2);
    generalize (Hrec true _ _ H1 H2); case scalb; simpl.
    case ZEll.scalb; intros r1 rc1; simpl.
    intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
    apply ndouble_correct; auto.
    generalize (scalb_wf p true x H1 H2);
    generalize (Hrec true _ _ H1 H2); case scalb; simpl.
    case ZEll.scalb; intros r1 rc1; simpl.
    intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
    generalize (ndouble_wf _ H5 H6);
      generalize (ndouble_correct _ H5 H6); case ndouble; simpl.
    case ZEll.ndouble; intros r1 rc1; simpl.
    intros a3 sc3 (H7,H8) (H9,H10); subst r1 rc1.
    replace (ZEll.nopp (vN exx) (e2E x)) with
      (e2E (nopp x)).
    apply nadd_correct; auto.
    generalize H1; case x; auto.
    intros x1 y1 z1 [HH1 [HH2 HH3]]; split; auto.
    rewrite nopp_correct; auto.
    apply f_equal2 with (f := ZEll.nopp); auto.
    generalize H1; case x; simpl; auto; clear x H1.
    intros x1 y1 z1 [HH1 [HH2 HH3]];
      apply f_equal3 with (f := ZEll.ntriple); auto.
    repeat rewrite nsubz; auto.
    rewrite zc0.
    unfold ZEll.nsub; simpl.
    rewrite <- (Z_mod_plus) with (b := -(-z2Z y1 /exx.(vN))); auto with zarith.
    rewrite <- Zopp_mult_distr_l.
    rewrite <- Zopp_plus_distr.
    rewrite Zmult_comm; rewrite Zplus_comm.
    rewrite <- Z_div_mod_eq_full.
    rewrite Z.opp_involutive.
    apply Zmod_small, z2Z_bound; auto.
    generalize H1; case x; auto.
    intros x1 y1 z1 [HH1 [HH2 HH3]]; split; auto.
intros p Hrec b x sc H1 H2.
  case b; unfold scalb; fold scalb.
    generalize (scalb_wf p false x H1 H2);
    generalize (Hrec false _ _ H1 H2); case scalb; simpl.
    case ZEll.scalb; intros r1 rc1; simpl.
    intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
    generalize (ndouble_wf _ H5 H6);
      generalize (ndouble_correct _ H5 H6); case ndouble; simpl.
    case ZEll.ndouble; intros r1 rc1; simpl.
    intros a3 sc3 (H7,H8) (H9,H10); subst r1 rc1.
    replace (ZEll.nopp (vN exx) (e2E x)) with
      (e2E (nopp x)).
    apply nadd_correct; auto.
    rewrite nopp_correct; auto.
    apply f_equal2 with (f := ZEll.nopp); auto.
    generalize H1; case x; simpl; auto; clear x H1.
    intros x1 y1 z1 [HH1 [HH2 HH3]];
      apply f_equal3 with (f := ZEll.ntriple); auto.
    repeat rewrite nsubz; auto.
    rewrite zc0.
    unfold ZEll.nsub; simpl.
    rewrite <- (Z_mod_plus) with (b := -(-z2Z y1 /exx.(vN))); auto with zarith.
    rewrite <- Zopp_mult_distr_l.
    rewrite <- Zopp_plus_distr.
    rewrite Zmult_comm; rewrite Zplus_comm.
    rewrite <- Z_div_mod_eq_full.
    rewrite Z.opp_involutive.
    apply Zmod_small, z2Z_bound; auto.
    generalize H1; case x; auto.
    intros x1 y1 z1 [HH1 [HH2 HH3]]; split; auto.
    generalize (scalb_wf p false x H1 H2);
    generalize (Hrec false _ _ H1 H2); case scalb; simpl.
    case ZEll.scalb; intros r1 rc1; simpl.
    intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
    apply ndouble_correct; auto.
intros b x sc H H1.
case b; simpl; auto.
apply ndouble_correct; auto.
Qed.


Lemma scal_correct: forall n x sc,
  wfe x -> wft sc ->
  e2E (fst (scal sc x n)) = fst (ZEll.scal exx.(vN) exx.(vA) (z2Z sc) (e2E x) n)/\
  z2Z (snd (scal sc x n)) = snd (ZEll.scal exx.(vN) exx.(vA) (z2Z sc) (e2E x) n).
Proof.
intros n; exact (scalb_correct n false).
Qed.

Lemma scal_list_correct: forall l x sc,
  wfe x -> wft sc ->
  e2E (fst (scal_list sc x l)) = fst (ZEll.scal_list exx.(vN) exx.(vA) (z2Z sc) (e2E x) l)/\
  z2Z (snd (scal_list sc x l)) = snd (ZEll.scal_list exx.(vN) exx.(vA) (z2Z sc) (e2E x) l).
Proof.
intros l1; elim l1; simpl; auto.
unfold scal_list, ZEll.scal_list; simpl; intros a l2 Hrec x sc H1 H2.
generalize (scal_correct a _ H1 H2) (scal_wf a _ H1 H2); case scal.
case ZEll.scal; intros r1 rsc1; simpl.
simpl; intros a1 sc1 (H3, H4) (H5, H6); subst r1 rsc1; auto.
Qed.

Lemma scal_list_wf: forall l x sc,
  wfe x -> wft sc ->
  wfe (fst (scal_list sc x l)) /\  wft (snd (scal_list sc x l)).
Proof.
intros l1; elim l1; simpl; auto.
unfold scal_list; intros a l Hrec x sc H1 H2; simpl.
generalize (@scal_wf a _ _ H1 H2);
  case (scal sc x a); simpl; intros x1 sc1 [H3 H4]; auto.
Qed.

Lemma scalL_wf: forall l x sc,
  wfe x -> wft sc ->
  wfe (fst (scalL sc x l)) /\  wft (snd (scalL sc x l)).
Proof.
intros l1; elim l1; simpl; auto.
intros a l2 Hrec x sc H1 H2.
generalize (scal_wf a _ H1 H2); case scal; simpl.
intros a1 sc1 (H3, H4); auto.
generalize (scal_list_wf l2 _ H1 H4); case scal_list; simpl.
intros a2 sc2; case a2; simpl; auto.
intros x1 y1 z1 ((V1, (V2, V3)), V4); apply Hrec; auto.
Qed.

Lemma scalL_correct: forall l x sc,
  wfe x -> wft sc ->
  e2E (fst (scalL sc x l)) = fst (ZEll.scalL exx.(vN) exx.(vA) (z2Z sc) (e2E x) l)/\
  z2Z (snd (scalL sc x l)) = snd (ZEll.scalL exx.(vN) exx.(vA) (z2Z sc) (e2E x) l).
Proof.
intros l1; elim l1; simpl; auto.
intros a l2 Hrec x sc H1 H2.
generalize (scal_wf a _ H1 H2) (scal_correct a _ H1 H2); case scal; simpl.
case ZEll.scal; intros r1 rsc1; simpl.
intros a1 sc1 (H3, H4) (H5, H6); subst r1 rsc1.
generalize (scal_list_wf l2 _ H1 H4) (scal_list_correct l2 _ H1 H4); case scal_list; simpl.
case ZEll.scal_list; intros r1 rsc1; simpl.
intros a2 sc2 (H7, H8) (H9, H10); subst r1 rsc1.
generalize H7; clear H7; case a2; simpl; auto.
rewrite zc0; auto.
intros x1 y1 z1 (V1, (V2, V3)); auto.
generalize (nmulw H8 V3) (nmulz H8 V3); intros V4 V5; rewrite <- V5.
apply Hrec; auto.
Qed.

Lemma f4 : wft (Z2z 4).
Proof.
apply z2Zx1.
Qed.

Lemma f27 : wft (Z2z 27).
Proof.
apply z2Zx1.
Qed.

Lemma Bw : wft B.
Proof.
unfold B; apply z2Zx1.
Qed.

Hint Resolve f4 f27 Bw : core.

Lemma mww: forall x y, ZEll.nmul (vN exx) (x mod (vN exx) ) y = ZEll.nmul (vN exx) x y.
intros x  y; unfold ZEll.nmul; rewrite Zmult_mod_idemp_l; auto.
Qed.

Lemma wwA: forall x, ZEll.nmul (vN exx) x exx.(vA) = ZEll.nmul (vN exx) x (z2Z A).
intros x; unfold ZEll.nmul.
rewrite HA, z2Zx; rewrite Zmult_mod_idemp_r; auto.
Qed.

Lemma wwB: forall x, ZEll.nmul (vN exx) x exx.(vB) = ZEll.nmul (vN exx) x (z2Z B).
intros x; unfold ZEll.nmul.
unfold B; rewrite z2Zx; rewrite Zmult_mod_idemp_r; auto.
Qed.

 Lemma  scalL_prime:
  let a := ntriple (Z2z (exx.(vx))) (Z2z (exx.(vy))) c1 in
  let isc := (Z2z 4) ** A ** A ** A  ++ (Z2z 27) ** B ** B in
  let (a1, sc1) := scal isc a exx.(vS) in
  let (S1,R1) := psplit exx.(vR) in
  let (a2, sc2) := scal sc1 a1 S1 in
  let (a3, sc3) := scalL sc2 a2 R1 in
    match a3 with
     nzero => if (Z.eqb (Z.gcd (z2Z sc3) exx.(vN)) 1) then prime exx.(vN)
              else True
   | _ => True
   end.
  Proof.
  intros a isc.
  case_eq (scal isc a (vS exx)); intros a1 sc1 Ha1.
  case_eq (psplit (vR exx)); intros S1 R1 HS1.
  case_eq (scal sc1 a1 S1); intros a2 sc2 Ha2.
  case_eq (scalL sc2 a2 R1); intros a3 sc3; case a3; auto.
  intros Ha3; case_eq (Z.eqb (Z.gcd (z2Z sc3) (vN exx)) 1); auto.
  intros H1.
  assert (F0:
     (vy exx mod vN exx) ^ 2 mod vN exx =
       ((vx exx mod vN exx) ^ 3 + vA exx * (vx exx mod vN exx) +
        vB exx) mod vN exx).
      generalize exxs.(inC).
      simpl; unfold Zpower_pos; simpl.
      repeat rewrite Zmult_1_r.
      intros HH.
      (rewrite_strat (bottomup (terms Zmult_mod_idemp_l Zmult_mod_idemp_r))).
      rewrite HH.
      rewrite Zplus_mod; auto; symmetry; rewrite Zplus_mod; auto; symmetry.
      apply f_equal2 with (f := Z.modulo); auto.
      apply f_equal2 with (f := Zplus); auto.
      rewrite Zplus_mod; auto; symmetry; rewrite Zplus_mod; auto; symmetry.
      apply f_equal2 with (f := Z.modulo); auto.
      apply f_equal2 with (f := Zplus); auto.
      rewrite Zmult_mod; auto; symmetry; rewrite Zmult_mod; auto; symmetry.
      apply f_equal2 with (f := Z.modulo); auto.
      apply f_equal2 with (f := Zmult); auto.
      rewrite Zmod_mod; auto.
      (rewrite_strat (bottomup (terms Zmult_mod_idemp_l Zmult_mod_idemp_r))); auto.
      rewrite Zmult_mod; auto; symmetry; rewrite Zmult_mod; auto; symmetry.
      apply f_equal2 with (f := Z.modulo); auto.
      rewrite Zmod_mod; auto.
   generalize (@ZEll.scalL_prime exx.(vN)
               (exx.(vx) mod exx.(vN))
               (exx.(vy) mod exx.(vN))
               exx.(vA)
               exx.(vB)
               exxs.(n_pos) exxs.(n2_div) exx.(vR)
               exxs.(lprime) exx.(vS) exxs.(lbig) F0); simpl.
generalize (@scal_wf (vS exx) a isc) (@scal_correct (vS exx) a isc).
unfold isc.
rewrite nplusz; auto; try nw; auto.
repeat rewrite nmulz; auto; try nw; auto.
  repeat rewrite z2Zx.
repeat rewrite wwA || rewrite wwB|| rewrite mww.
replace (e2E a) with (ZEll.ntriple (vx exx mod vN exx) (vy exx mod vN exx) 1).
case ZEll.scal.
fold isc; rewrite HS1; rewrite Ha1; simpl; auto.
intros r1 rsc1 HH1 HH2.
case HH1; clear HH1.
  unfold c1; repeat split; try apply z2Zx1.
  unfold isc; nw.
case HH2; clear HH2.
  unfold c1; repeat split; try apply z2Zx1.
  unfold isc; nw.
intros U1 U2 W1 W2; subst r1 rsc1.
generalize (@scal_wf S1 a1 sc1) (@scal_correct S1 a1 sc1).
case ZEll.scal.
intros r1 rsc1 HH1 HH2.
case HH1; clear HH1; auto.
case HH2; clear HH2; auto.
rewrite Ha2; simpl.
intros U1 U2 W3 W4; subst r1 rsc1.
generalize (@scalL_wf R1 a2 sc2) (@scalL_correct R1 a2 sc2).
case ZEll.scalL.
intros n; case n; auto.
rewrite Ha3; simpl.
intros rsc1 HH1 HH2.
case HH1; clear HH1; auto.
case HH2; clear HH2; auto.
intros _ U2 _ W5; subst rsc1.
rewrite H1; auto.
intros x1 y1 z1 sc4; rewrite Ha3; simpl; auto.
intros _ HH; case HH; auto.
intros; discriminate.
unfold a; simpl.
unfold c1; repeat rewrite z2Zx.
rewrite (Zmod_small 1); auto.
generalize exxs.(n_pos).
auto with zarith.
Qed.

End NEll.

Definition isM2 p :=
  match p with
    xH   => false
|    xO _ => false
|     _ => true
end.

Lemma isM2_correct: forall p,
  if isM2 p then ~(Z.divide 2 p) /\ 2 < p else True.
Proof.
intros p; case p; simpl; auto; clear p.
intros p1; split; auto.
intros HH; inversion_clear HH.
generalize H; rewrite Zmult_comm.
case x; simpl; intros; discriminate.
case p1; red; simpl; auto.
Qed.

Definition ell_test (N S: positive) (l: List.list (positive * positive))
                      (A B x y: Z) :=
    if isM2 N then
    match (4 * N) ?= (ZEll.Zmullp l - 1) ^ 2  with
      Lt =>
       match y ^ 2 mod N ?= (x ^ 3 + A * x + B) mod N with
       Eq =>
          let ex := mkEx N S l A B x y in
          (* the data of the modulus, computed once *)
          let MN := positive_to_num N in
          let nM := length MN in
          let mM := invM (0 - 1)%uint63 (nhead MN) in
          let rM := r_square MN nM in
          let e := Z2z ex MN mM nM rM in
          let c0 := e 0 in
          let c2 := e 2 in
          let c3 := e 3 in
          let dA := e A in
          let dB := e B in
          let a := ntriple (e x) (e y) (e 1)  in
          let d4 := e 4 in
          let d27 := e 27 in
          let da := nplus MN in
          let dm := nmul MN mM nM in
          let isc := (da (dm (dm  (dm d4 dA) dA) dA) (dm (dm d27 dB) dB)) in
          let (a1, sc1) := scal MN mM nM c0 c2 c3 dA isc a S in
          let (S1,R1) := ZEll.psplit l in
          let (a2, sc2) := scal MN mM nM c0 c2 c3 dA sc1 a1 S1 in
          let (a3, sc3) := scalL MN mM nM c0 c2 c3 dA sc2 a2 R1 in
          match a3 with
           nzero => if (Z.eqb (Z.gcd (z2Z MN mM nM sc3) N) 1) then true
                    else false
          | _ => false
          end
      | _  => false
       end
    | _  => false
    end
    else false.

Lemma Zcompare_correct: forall x y,
  match x ?= y with Eq => x = y | Gt => x > y | Lt => x < y end.
Proof.
intros x y; unfold Z.lt, Z.gt; generalize (Zcompare_Eq_eq x y); case Z.compare; auto.
Qed.

Lemma ell_test_correct: forall (N S: positive) (l: List.list (positive * positive))
                      (A B x y: Z),
  (forall p, List.In p l -> prime (fst p)) ->
  if ell_test N S l A B x y then prime N else True.
Proof.
intros N S1 l A1 B1 x y H; unfold ell_test.
generalize (isM2_correct N); case isM2; auto.
intros (H1, H2).
match goal with |- context[?x ?= ?y] =>
  generalize (Zcompare_correct x y); case Z.compare; auto
end; intros H3.
match goal with |- context[?x ?= ?y] =>
  generalize (Zcompare_correct x y); case Z.compare; auto
end; intros H4.
set (exx := mkEx N S1 l A1 B1 x y).
assert (exxs: ex_spec exx).
  constructor; auto.
set (MN := positive_to_num N).
set (nM := length MN).
set (mM := invM (0 - 1)%uint63 (nhead MN)).
set (rM := r_square MN nM).
assert (MN_Z : [MN] = vN exx) by apply positive_to_Z.
assert (Hmm' : φ (nhead MN * mM)%uint63 = wB - 1) by (apply mont_const; auto).
assert (M_small : [MN] < Zpower_nat wB nM) by apply num_lt_length.
generalize (@scalL_prime exx exxs MN mM nM rM MN_Z Hmm' M_small eq_refl
  _ _ _ _ eq_refl eq_refl eq_refl eq_refl).
lazy zeta.
unfold c1, B, nplus, nmul;
  simpl (exx.(vA)); simpl (exx.(vB)); simpl (exx.(vx)); simpl (exx.(vy));
  simpl (exx.(vS)); simpl (exx.(vR)); simpl (exx.(vN)).
case scal; intros a1 sc1.
case ZEll.psplit; intros S2 R2.
case scal; intros a2 sc2.
case scalL; intros a3 sc3.
case a3; auto.
case Z.eqb; auto.
Qed.

Time Eval vm_compute in (ell_test
  329719147332060395689499
  8209062
  (List.cons (40165264598163841%positive,1%positive) List.nil)
  (-94080)
  9834496
  0
  3136).

Time Eval vm_compute in (ell_test
  1384435372850622112932804334308326689651568940268408537
  13077052794
  (List.cons (105867537178241517538435987563198410444088809%positive, 1%positive) List.nil)
  (-677530058123796416781392907869501000001421915645008494)
  0
  (- 169382514530949104195348226967375250000355478911252124)
  1045670343788723904542107880373576189650857982445904291
).
