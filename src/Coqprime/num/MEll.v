(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

From Stdlib Require Import ZArith Lia Znumtheory Zpow_facts.
From Stdlib Require Import CyclicAxioms DoubleType Cyclic63.
From Coqprime Require Import Int63Compat.
From Bignums Require Import DoubleCyclic BigN.
From Coqprime Require Import W Mod_op ZEll Bits MontMod.
Import CyclicAxioms DoubleType DoubleBase.
From Stdlib Require Import Zmod.

(* NEll with Montgomery multiplication on the words of BigN: the elements
   of Z/NZ are BigN words in Montgomery form (x R mod N, R the base of
   the words); the product needs three multiplications and no division. *)

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



Section NEll.

Variable exx: ex.
Variable exxs: ex_spec exx.

(* the words of BigN, the modulus wN, N' = - N^-1 mod R and R^2 mod N,
   with R = wB: all computed once by ell_test *)
Variable w : univ_of_cycles.
Variable op : ZnZ.Ops w.
Variable op_spec : ZnZ.Specs op.

Notation "[| x |]" := (ZnZ.to_Z x) (at level 0, x at level 99).
Notation wB := (base (@ZnZ.digits _ op)).

Variable wN wN' wR2 : w.
Variable mop : mod_op w.
Hypothesis HwN : [|wN|] = exx.(vN).
Hypothesis mop_spec : mod_spec op wN mop.
Hypothesis Hinv : [|ZnZ.mul wN wN'|] = wB - 1.
Hypothesis HR2 : [|wR2|] = (wB * wB) mod exx.(vN).

Definition mmul x y := @mont_mul _ op wN wN' x y.

(* An element of Z/NZ is stored in Montgomery form: z2Z reads it back. *)
Definition z2Z t := [|mmul t ZnZ.one|].
Definition Z2z z := mmul (ZnZ.of_Z (z mod exx.(vN))) wR2.

Lemma vN_pos: 0 < exx.(vN).
Proof. red; simpl; auto. Qed.

Hint Resolve vN_pos : core.

Lemma vN_gt1 : 1 < exx.(vN).
Proof. generalize exxs.(n_pos); auto with zarith. Qed.

Lemma wN_pos : 0 < [|wN|].
Proof. rewrite HwN; auto. Qed.

(* the invariant of a stored w: it is reduced modulo N *)
Definition wft t := [|t|] = [|t|] mod exx.(vN).

Lemma wft_lt t : wft t -> 0 <= [|t|] < exx.(vN).
Proof. intros Ht; rewrite Ht; apply Z.mod_pos_bound; auto. Qed.

Lemma wft_intro t : 0 <= [|t|] < exx.(vN) -> wft t.
Proof. intros Ht; unfold wft; rewrite Zmod_small; auto. Qed.

Lemma one_wft : wft ZnZ.one.
Proof. apply wft_intro; rewrite ZnZ.spec_1; generalize vN_gt1; auto with zarith. Qed.

Lemma mmul_spec x y : wft x -> wft y ->
  wft (mmul x y) /\ ([|mmul x y|] * wB) mod exx.(vN) = ([|x|] * [|y|]) mod exx.(vN).
Proof.
intros Hx Hy; apply wft_lt in Hx; apply wft_lt in Hy.
rewrite <- HwN in Hx, Hy |- *.
destruct (@mont_mul_spec _ op op_spec wN wN' wN_pos Hinv x y) as [H1 H2];
  try tauto.
split; auto.
apply wft_intro; rewrite <- HwN; split; auto.
case (ZnZ.spec_to_Z (mont_mul op wN wN' x y)); auto.
Qed.

(* R is invertible modulo N: (N N' + 1) / R is its inverse *)
Lemma R_cancel a b : (a * wB) mod exx.(vN) = (b * wB) mod exx.(vN) ->
  a mod exx.(vN) = b mod exx.(vN).
Proof.
intros H.
assert (HR : 0 < wB).
{ unfold base; apply Z.pow_pos_nonneg; auto with zarith. }
set (q := ([|wN|] * [|wN'|]) / wB + 1).
assert (Hq : (q * wB) mod exx.(vN) = 1).
{ assert (H1 : ([|wN|] * [|wN'|]) mod wB = wB - 1).
  { rewrite <- Hinv; symmetry; apply ZnZ.spec_mul. }
  assert (H2 := Z_div_mod_eq_full ([|wN|] * [|wN'|]) wB).
  replace (q * wB) with (1 + [|wN'|] * [|wN|]).
  - rewrite HwN, Z_mod_plus_full, Zmod_small; generalize vN_gt1; auto with zarith.
  - unfold q; rewrite H1 in H2; lia. }
assert (E : forall c, c mod exx.(vN) = ((c * wB) * q) mod exx.(vN)).
{ intros c.
  replace (c * wB * q) with (c * (q * wB)) by ring.
  rewrite Zmult_mod, Hq, Z.mul_1_r, Zmod_mod; reflexivity. }
rewrite (E a), (E b), Zmult_mod, H, <- Zmult_mod; reflexivity.
Qed.

Lemma z2Z_spec t : wft t ->
  wft (mmul t ZnZ.one) /\ (z2Z t * wB) mod exx.(vN) = [|t|] mod exx.(vN).
Proof.
intros Ht; destruct (mmul_spec Ht one_wft) as [H1 H2].
split; auto.
unfold z2Z; rewrite H2, ZnZ.spec_1, Z.mul_1_r; reflexivity.
Qed.

Lemma z2Z_bound t : wft t -> 0 <= z2Z t < exx.(vN).
Proof. intros Ht; apply wft_lt, (z2Z_spec Ht). Qed.

Lemma z2Z_R t : wft t -> (z2Z t * wB) mod exx.(vN) = [|t|] mod exx.(vN).
Proof. intros Ht; apply (z2Z_spec Ht). Qed.

(* z2Z t is the only z in [0, N) with z * R = [t] modulo N *)
Lemma z2Z_char t z : wft t -> 0 <= z < exx.(vN) ->
  (z * wB) mod exx.(vN) = [|t|] mod exx.(vN) -> z2Z t = z.
Proof.
intros Ht Hz Hzt.
assert (Hb := z2Z_bound Ht).
assert (H := R_cancel (z2Z t) z).
rewrite (Zmod_small (z2Z t)), (Zmod_small z) in H by auto.
apply H; rewrite Hzt; apply z2Z_R; auto.
Qed.

Definition nplus x y := mop.(add_mod) x y.
Definition nsub x y := mop.(sub_mod) x y.
Definition nmul x y := mmul x y.
Definition neq x y := match ZnZ.compare x y with Eq => true | _ => false end.

Definition S := exx.(vS).
Definition R := exx.(vR).
(* the constants used by the point operations: computed once by ell_test *)
Variable c0 c2 c3 A : w.
Hypothesis Hc0 : c0 = Z2z 0.
Hypothesis Hc2 : c2 = Z2z 2.
Hypothesis Hc3 : c3 = Z2z 3.
Hypothesis HA : A = Z2z exx.(vA).
Definition B := Z2z exx.(vB).
Definition xx := Z2z exx.(vx).
Definition yy := Z2z exx.(vy).
Definition c1 := Z2z 1.

Inductive nelt: Type :=
  nzero | ntriple: w -> w -> w  -> nelt.

Definition pp := ntriple xx yy c1.


Notation "x ++ y " := (nplus x y).
Notation "x -- y" := (nsub x y) (at level 50, left associativity).
Notation "x ** y" := (nmul x y) (at level 40, left associativity).
Notation "x ?= y" := (neq x y).

Definition ndouble: w -> nelt -> (nelt * w):= fun (sc: w) (p1: nelt) =>
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


Definition nadd := fun (sc: w) (p1 p2: nelt) =>
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

Fixpoint scalb (sc: w) (b:bool) (a: nelt) (p: positive) {struct p}:
 nelt * w :=
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
  (fun (asc: nelt * w) p1 => let (a,sc) := asc in scal sc a p1) l (a,sc).

Fixpoint scalL (sc:w) (a: nelt) (l: List.list positive) {struct l}: (nelt * w) :=
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




Lemma wft_b t : wft t -> [|t|] = [|t|] mod [|wN|].
Proof. rewrite HwN; auto. Qed.

Lemma nplusw: forall x y, wft x -> wft y ->  wft (x ++ y).
Proof.
intros x y Hx Hy; unfold wft, nplus.
rewrite (mop_spec.(add_mod_spec) _ _ _ _ (wft_b Hx) (wft_b Hy)), HwN.
rewrite Zmod_mod; auto.
Qed.

Lemma nsubw: forall x y, wft x -> wft y ->  wft (x -- y).
Proof.
intros x y Hx Hy; unfold wft, nsub.
rewrite (mop_spec.(sub_mod_spec) _ _ _ _ (wft_b Hx) (wft_b Hy)), HwN.
rewrite Zmod_mod; auto.
Qed.

Lemma nmulw: forall x y, wft x -> wft y ->  wft (x ** y).
Proof. intros x y Hx Hy; apply (mmul_spec Hx Hy). Qed.

Hint Resolve nmulw nplusw nsubw : core.

Lemma nplusz: forall x y, wft x -> wft y ->
      z2Z (x ++ y) = ZEll.nplus (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy; unfold ZEll.nplus.
apply z2Z_char; auto.
- apply Z.mod_pos_bound; auto.
- unfold nplus; rewrite (mop_spec.(add_mod_spec) _ _ _ _ (wft_b Hx) (wft_b Hy)), HwN.
  rewrite Zmod_mod, Zmult_mod_idemp_l, Z.mul_add_distr_r.
  rewrite Z.add_mod by auto with zarith.
  rewrite (z2Z_R Hx), (z2Z_R Hy), <- Z.add_mod by auto with zarith; reflexivity.
Qed.

Lemma nsubz: forall x y, wft x -> wft y ->
      z2Z (x -- y) = ZEll.nsub (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy; unfold ZEll.nsub.
apply z2Z_char; auto.
- apply Z.mod_pos_bound; auto.
- unfold nsub; rewrite (mop_spec.(sub_mod_spec) _ _ _ _ (wft_b Hx) (wft_b Hy)), HwN.
  rewrite Zmod_mod, Zmult_mod_idemp_l, Z.mul_sub_distr_r.
  rewrite Zminus_mod, (z2Z_R Hx), (z2Z_R Hy), <- Zminus_mod; reflexivity.
Qed.

Lemma nmulz: forall x y, wft x -> wft y ->
      z2Z (x ** y) = ZEll.nmul (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy; unfold ZEll.nmul.
apply z2Z_char; auto.
- apply Z.mod_pos_bound; auto.
- rewrite Zmult_mod_idemp_l.
  (* cancel one factor R: both sides times R are [x] * [y] *)
  assert (H : ([|x ** y|] * wB) mod exx.(vN) = (z2Z x * z2Z y * wB * wB) mod exx.(vN)).
  { unfold nmul; rewrite (proj2 (mmul_spec Hx Hy)).
    replace (z2Z x * z2Z y * wB * wB) with ((z2Z x * wB) * (z2Z y * wB)) by ring.
    rewrite (Z.mul_mod (z2Z x * wB)), (z2Z_R Hx), (z2Z_R Hy), <- Z.mul_mod
      by auto with zarith; reflexivity. }
  rewrite (R_cancel _ _ H); reflexivity.
Qed.

Definition wfe p := match p with
  ntriple x y z => wft x /\ wft y /\ wft z
| _ => True
end.

Lemma of_Z_mod x : [|ZnZ.of_Z (x mod exx.(vN))|] = x mod exx.(vN).
Proof.
apply ZnZ.of_Z_correct.
assert (H := ZnZ.spec_to_Z wN); rewrite HwN in H.
generalize (Z.mod_pos_bound x (vN exx) vN_pos); auto with zarith.
Qed.

Lemma R2_wft : wft wR2.
Proof. apply wft_intro; rewrite HR2; apply Z.mod_pos_bound; auto. Qed.

Lemma Z2z_spec x : wft (Z2z x) /\
  ([|Z2z x|] * wB) mod exx.(vN) = (x * wB * wB) mod exx.(vN).
Proof.
assert (Hu : wft (ZnZ.of_Z (ops := op) (x mod exx.(vN)))).
{ apply wft_intro; rewrite of_Z_mod; apply Z.mod_pos_bound; auto. }
destruct (mmul_spec Hu R2_wft) as [H1 H2].
split; auto.
unfold Z2z; rewrite H2, of_Z_mod, HR2.
rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r, Z.mul_assoc; reflexivity.
Qed.

Lemma z2Zx: forall x, z2Z (Z2z x) = x mod exx.(vN).
Proof.
intros x; destruct (Z2z_spec x) as [H1 H2].
apply z2Z_char; auto.
- apply Z.mod_pos_bound; auto.
- rewrite Zmult_mod_idemp_l.
  apply R_cancel; rewrite H2; reflexivity.
Qed.

Lemma z2Zx1: forall x, wft (Z2z x).
Proof. intros x; apply (Z2z_spec x). Qed.

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
 rewrite ZnZ.spec_compare; case Z.compare_spec; intros Hxy.
 - assert (H : z2Z y = z2Z x).
   { apply z2Z_char; auto.
     - apply z2Z_bound; auto.
     - rewrite (z2Z_R Hx), Hxy; reflexivity. }
   rewrite H, Z.eqb_refl; reflexivity.
 - case Z.eqb_spec; auto; intros H; exfalso.
   assert (H1 : [|x|] mod exx.(vN) = [|y|] mod exx.(vN)).
   { rewrite <- (z2Z_R Hx), <- (z2Z_R Hy), H; reflexivity. }
   rewrite <- Hx, <- Hy in H1; auto with zarith.
 - case Z.eqb_spec; auto; intros H; exfalso.
   assert (H1 : [|x|] mod exx.(vN) = [|y|] mod exx.(vN)).
   { rewrite <- (z2Z_R Hx), <- (z2Z_R Hy), H; reflexivity. }
   rewrite <- Hx, <- Hy in H1; auto with zarith.
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
Proof.
intros x  y; unfold ZEll.nmul; rewrite Zmult_mod_idemp_l; auto.
Qed.

Lemma wwA: forall x, ZEll.nmul (vN exx) x exx.(vA) = ZEll.nmul (vN exx) x (z2Z A).
Proof.
intros x; unfold ZEll.nmul.
rewrite HA, z2Zx; rewrite Zmult_mod_idemp_r; auto.
Qed.

Lemma wwB: forall x, ZEll.nmul (vN exx) x exx.(vB) = ZEll.nmul (vN exx) x (z2Z B).
Proof.
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
  let k := Peano.pred (nat_of_P (get_height 63 (plength N))) in
  let op := cmk_op k in
  let wN := ZnZ.of_Z (ops := op) N in
  let mop := Mod_op.make_mod_op op wN in
  (* N' = - N^-1 mod R by Newton iteration; checked below *)
  let wN' := ZnZ.sub ZnZ.zero
    (List.fold_left (fun u _ => ZnZ.mul u (ZnZ.sub (ZnZ.of_Z 2) (ZnZ.mul wN u)))
       (List.repeat tt (k + 7)) ZnZ.one) in
  (* R^2 mod N *)
  let wR := rmodn op mop (ZnZ.digits op) in
  let wR2 := mop.(mul_mod) wR wR in
    if isM2 N then
    match (4 * N) ?= (ZEll.Zmullp l - 1) ^ 2  with
      Lt =>
       match y ^ 2 mod N ?= (x ^ 3 + A * x + B) mod N with
       Eq =>
         match ZnZ.compare (ZnZ.mul wN wN') (ZnZ.sub ZnZ.zero ZnZ.one) with
         Eq =>
          let ex := mkEx N S l A B x y in
          let e := Z2z ex op wN wN' wR2 in
          let c0 := e 0 in
          let c2 := e 2 in
          let c3 := e 3 in
          let dA := e A in
          let dB := e B in
          let a := ntriple (e x) (e y) (e 1)  in
          let d4 := e 4 in
          let d27 := e 27 in
          let da := nplus mop in
          let dm := nmul op wN wN' in
          let isc := (da (dm (dm  (dm d4 dA) dA) dA) (dm (dm d27 dB) dB)) in
          let (a1, sc1) := scal op wN wN' mop c0 c2 c3 dA isc a S in
          let (S1,R1) := ZEll.psplit l in
          let (a2, sc2) := scal op wN wN' mop c0 c2 c3 dA sc1 a1 S1 in
          let (a3, sc3) := scalL op wN wN' mop c0 c2 c3 dA sc2 a2 R1 in
          match a3 with
           nzero _ => if (Z.eqb (Z.gcd (z2Z op wN wN' sc3) N) 1) then true
                    else false
          | _ => false
          end
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
set (n := Peano.pred (nat_of_P (get_height 63 (plength N)))).
set (op := cmk_op n).
set (op_spec := cmk_spec n).
set (exx := mkEx N S1 l A1 B1 x y).
assert (exxs: ex_spec exx).
  constructor; auto.
assert (H0: N < base (ZnZ.digits op)).
  apply Z.lt_le_trans with (1 := plength_correct N).
  unfold op, base.
  rewrite cmk_op_digits.
  apply Zpower_le_monotone; split. auto with zarith.
  generalize (get_height_correct 63 (plength N)); unfold n.
  set (p := plength N).
  replace (Z_of_nat (Peano.pred (nat_of_P (get_height 63 p)))) with
       ((Zpos (get_height 63 p) - 1) ). auto with zarith.
  rewrite <- Nat.sub_1_r; rewrite inj_minus1.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; reflexivity.
  generalize (lt_O_nat_of_P (get_height 63 p)); auto with zarith.
set (wN := ZnZ.of_Z (ops := op) N).
assert (HwN : ZnZ.to_Z wN = vN exx).
  unfold wN; rewrite ZnZ.of_Z_correct; auto with zarith.
set (mop := Mod_op.make_mod_op op wN).
assert (mspec: mod_spec op wN mop).
  unfold mop; apply Mod_op.make_mod_spec; auto.
  rewrite HwN; simpl; auto with zarith.
match goal with |- context[ZnZ.compare ?a ?b] =>
  generalize (ZnZ.spec_compare a b); case ZnZ.compare; auto
end; intros Hc.
set (wN' := ZnZ.sub ZnZ.zero _) in Hc |- *.
assert (Hinv : ZnZ.to_Z (ZnZ.mul wN wN') = base (ZnZ.digits op) - 1).
  assert (HB : 0 < base (ZnZ.digits op)).
    unfold base; apply Z.pow_pos_nonneg; auto with zarith.
  rewrite (Z.compare_eq _ _ (eq_sym Hc)), ZnZ.spec_sub, ZnZ.spec_0, ZnZ.spec_1.
  rewrite <- (Z_mod_plus_full (0 - 1) 1), Zmod_small; auto with zarith.
set (wR := rmodn op mop (ZnZ.digits op)).
assert (HR2 : ZnZ.to_Z (mop.(mul_mod) wR wR) =
              (base (ZnZ.digits op) * base (ZnZ.digits op)) mod vN exx).
  assert (HN1 : 1 < ZnZ.to_Z wN) by (rewrite HwN; simpl; auto with zarith).
  assert (HR := rmodn_spec op_spec mspec HN1 (ZnZ.digits op)); fold op in HR; fold wR in HR.
  rewrite (mspec.(mul_mod_spec) _ _ _ _ HR HR), HR, HwN, <- Zmult_mod.
  unfold base; reflexivity.
generalize (@scalL_prime exx exxs _ op op_spec wN wN' (mop.(mul_mod) wR wR) mop
  HwN mspec Hinv HR2 _ _ _ _ eq_refl eq_refl eq_refl eq_refl).
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
