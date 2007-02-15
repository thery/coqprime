
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)


Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import ZnZ.
Require Import W.
Require Import Mod_op.
Require Import ZEll.

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

Fixpoint plength (p: positive) : positive :=
  match p with 
    xH => xH
  | xO p1 => Psucc (plength p1)
  | xI p1 => Psucc (plength p1)
  end.

Definition gl l := plength (plength (l * l)) - 3.

Variable exx: ex.
Variable exxs: ex_spec exx.

Definition l := Zabs_nat (gl exx.(vN)).
(*
Eval compute in l.
*)



(*
Definition op := cmk_op l.
Definition zZ := word W8_basic.w8 l.
*)
Variable zZ: Set.
Variable op: znz_op zZ.
Variable op_spec: znz_spec op.
Definition z2Z z := op.(znz_to_Z) z.
Definition zN := snd (op.(znz_of_pos) exx.(vN)).
Definition mop :=  make_mod_op op zN.
Variable mop_spec: mod_spec op zN mop.
Variable N_small: fst (op.(znz_of_pos) exx.(vN)) = 0%N.


Lemma z2ZN: z2Z zN = exx.(vN).
generalize (op_spec.(spec_of_pos) (exx.(vN))).
rewrite N_small; auto.
Qed.

Definition Z2z z :=
 match z mod exx.(vN) with
 | Zpos p => snd (op.(znz_of_pos) p)
 | _ => op.(znz_0)
 end.


Definition S := exx.(vS).
Definition R := exx.(vR).
Definition A := Z2z exx.(vA).
Definition B := Z2z exx.(vB).
Definition xx := Z2z exx.(vx).
Definition yy := Z2z exx.(vy).
Definition c3 := Z2z 3.
Definition c2 := Z2z 2.
Definition c1 := Z2z 1.
Definition c0 := Z2z 0.

Inductive nelt: Set :=
  nzero | ntriple: zZ -> zZ -> zZ  -> nelt | nstop.

Definition pp := ntriple xx yy c1.

Definition nplus x y := mop.(add_mod) x y.
Definition nmul x y :=  mop.(mul_mod) x y.
Definition nsub x y :=  mop.(sub_mod) x y.
Definition neq x y := match op.(znz_compare) x y with Eq => true | _ => false end.

Notation "x ++ y " := (nplus x y) (at level 50, left associativity).
Notation "x -- y" := (nsub x y) (at level 50, left associativity).
Notation "x ** y" := (nmul x y) (at level 40, left associativity).
Notation "x ?= y" := (neq x y).

Definition ndouble: zZ -> nelt -> (nelt * zZ):= fun (sc: zZ) (p1: nelt) =>
 match p1 with
  nzero => (p1, sc)
 | nstop => (nstop, sc)
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


Definition nadd := fun (sc: zZ) (p1 p2: nelt) =>
 match p1, p2 with
  nzero, _ => (p2, sc)
 | _ , nzero => (p1, sc)
 | nstop, _ => (nstop, sc)
 | _, nstop => (nstop, sc)
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

 Fixpoint npow (sc: zZ) (a: nelt) (p: positive) {struct p}:
   nelt * zZ :=
   match p with
     xH => (a, sc)
   | xO p1 => let (a1, sc1) := npow sc a p1 in
              ndouble sc1 a1
   | xI p1 => let (a1, sc1) := npow sc a p1 in
              let (a2, sc2) := ndouble sc1 a1 in
              nadd sc2 a a2
   end.

 Definition npowl sc a l :=
  List.fold_left 
  (fun (asc: nelt * zZ) p1 => let (a,sc) := asc in npow sc a p1) l (a,sc).

 Fixpoint npowl1 (sc:zZ) (a: nelt) (l: List.list positive) {struct l}: (nelt * zZ) :=
   match l with
     List.nil => (a,sc)
   | List.cons n l1 =>
        let (a1, sc1) := npow sc a n in
        let (a2, sc2) := npowl sc1 a l1 in
          match a2 with
             nzero => (nstop, c0)
          |  nstop => (nstop, c0)
          |  ntriple _ _ z => npowl1 (sc2 ** z) a1 l1
          end
   end.

Definition zpow sc p n :=
  let (p,sc') := npow sc p n in
  (p, op.(znz_to_Z) (op.(znz_gcd) sc' zN)).

Definition e2E n := 
  match n with 
    nzero => ZEll.nzero
  | nstop => ZEll.nstop
  | ntriple x1 y1 z1 => ZEll.ntriple (z2Z x1) (z2Z y1) (z2Z z1)
  end.


Definition wft t :=  z2Z t = (z2Z t) mod (z2Z zN).

Lemma vN_pos: 0 < exx.(vN).
red; simpl; auto.
Qed.

Hint Resolve vN_pos.

Lemma nplusz: forall x y, wft x -> wft y -> 
      z2Z (x ++ y) = ZEll.nplus (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy.
unfold z2Z, nplus.
rewrite (mop_spec.(add_mod_spec) _ _ _ _ Hx Hy); auto.
rewrite <- z2ZN; auto.
Qed.

Lemma nplusw: forall x y, wft x -> wft y ->  wft (x ++ y).
Proof.
intros x y Hx Hy.
unfold wft.
pattern (z2Z (x ++ y)) at 2; rewrite (nplusz Hx Hy).
unfold ZEll.nplus; rewrite z2ZN.
rewrite Zmod_mod; auto.
apply (nplusz Hx Hy).
Qed.

Lemma nsubz: forall x y, wft x -> wft y -> 
      z2Z (x -- y) = ZEll.nsub (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy.
unfold z2Z, nsub.
rewrite (mop_spec.(sub_mod_spec) _ _ _ _ Hx Hy); auto.
rewrite <- z2ZN; auto.
Qed.

Lemma nsubw: forall x y, wft x -> wft y ->  wft (x -- y).
Proof.
intros x y Hx Hy.
unfold wft.
pattern (z2Z (x -- y)) at 2; rewrite (nsubz Hx Hy).
unfold ZEll.nsub; rewrite z2ZN.
rewrite Zmod_mod; auto.
apply (nsubz Hx Hy).
Qed.

Lemma nmulz: forall x y, wft x -> wft y -> 
      z2Z (x ** y) = ZEll.nmul (vN exx) (z2Z x) (z2Z y).
Proof.
intros x y Hx Hy.
unfold z2Z, nmul.
rewrite (mop_spec.(mul_mod_spec) _ _ _ _ Hx Hy); auto.
rewrite <- z2ZN; auto.
Qed.

Lemma nmulw: forall x y, wft x -> wft y ->  wft (x ** y).
Proof.
intros x y Hx Hy.
unfold wft.
pattern (z2Z (x ** y)) at 2; rewrite (nmulz Hx Hy).
unfold ZEll.nmul; rewrite z2ZN.
rewrite Zmod_mod; auto.
apply (nmulz Hx Hy).
Qed.

Hint Resolve nmulw nplusw nsubw.


Definition wfe p := match p with
  ntriple x y z => wft x /\ wft y /\ wft z
| _ => True
end.

Lemma z2Zx: forall x, z2Z (Z2z x) = x mod exx.(vN).
unfold Z2z; intros x.
generalize (Z_mod_lt x exx.(vN)).
case_eq (x mod exx.(vN)).
intros _ _.
simpl; unfold z2Z; rewrite op_spec.(spec_0); auto.
intros p Hp HH; case HH; auto with zarith; clear HH.
intros _ HH1.
case (op_spec.(spec_to_Z) zN).
generalize  z2ZN; unfold z2Z; intros HH; rewrite HH; auto.
intros _ H0.
set (v := znz_of_pos op p); generalize HH1.
rewrite (op_spec.(spec_of_pos) p); fold v.
case (fst v).
  simpl; auto.
intros p1 H1.
contradict H0; apply Zle_not_lt.
apply Zlt_le_weak; apply Zle_lt_trans with (2:= H1).
apply Zle_trans with (1 * base (znz_digits op) + 0); auto with zarith.
apply Zplus_le_compat; auto.
apply Zmult_gt_0_le_compat_r; auto with zarith.
  case (op_spec.(spec_to_Z) (snd v)); auto with zarith.
  case p1; red; simpl; intros; discriminate.
  case (op_spec.(spec_to_Z) (snd v)); auto with zarith.
intros p Hp; case (Z_mod_lt x exx.(vN)); auto with zarith.
rewrite Hp; intros HH; case HH; auto.
Qed.


Lemma z2Zx1: forall x, z2Z (Z2z x) = z2Z (Z2z x) mod z2Z zN.
Proof.
unfold Z2z; intros x.
generalize (Z_mod_lt x exx.(vN)).
case_eq (x mod exx.(vN)).
intros _ _.
simpl; unfold z2Z; rewrite op_spec.(spec_0).
rewrite Zmod_def_small; split; auto with zarith.
generalize  z2ZN; unfold z2Z; intros HH; rewrite HH; auto.
intros p H1 H2.
case (op_spec.(spec_to_Z) zN).
generalize  z2ZN; unfold z2Z; intros HH; rewrite HH; auto.
intros _ H0.
case H2; auto with zarith; clear H2; intros _ H2.
rewrite Zmod_def_small; auto.
set (v := znz_of_pos op p).
split.
  case (op_spec.(spec_to_Z) (snd v)); auto.
generalize H2; rewrite (op_spec.(spec_of_pos) p); fold v.
case (fst v).
  simpl; auto.
intros p1 H.
contradict H0; apply Zle_not_lt.
apply Zlt_le_weak; apply Zle_lt_trans with (2:= H).
apply Zle_trans with (1 * base (znz_digits op) + 0); auto with zarith.
apply Zplus_le_compat; auto.
apply Zmult_gt_0_le_compat_r; auto with zarith.
  case (op_spec.(spec_to_Z) (snd v)); auto with zarith.
  case p1; red; simpl; intros; discriminate.
  case (op_spec.(spec_to_Z) (snd v)); auto with zarith.
intros p Hp; case (Z_mod_lt x exx.(vN)); auto with zarith.
rewrite Hp; intros HH; case HH; auto.
Qed.


Lemma c0w: wft c0.
Proof.
red; unfold c0; apply z2Zx1.
Qed.

Lemma c2w: wft c2.
Proof.
red; unfold c2; apply z2Zx1.
Qed.

Lemma c3w: wft c3.
Proof.
red; unfold c3; apply z2Zx1.
Qed.

Lemma Aw: wft A.
Proof.
red; unfold A; apply z2Zx1.
Qed.

Hint Resolve c0w c2w c3w Aw.

Ltac nw :=
  repeat (apply nplusw || apply nsubw || apply nmulw || apply c2w ||
          apply c3w || apply Aw); auto.


Lemma nadd_wf: forall x y sc,
  wfe x -> wfe y -> wft sc ->
  wfe (fst (nadd sc x y)) /\  wft (snd (nadd sc x y)).
Proof.
intros x; case x; clear; auto.
intros x1 y1 z1 y; case y; clear; auto.
  intros x2 y2 z2 sc (wfx1,(wfy1, wfz1)) (wfx2,(wfy2, wfz2)) wfsc; 
    simpl; auto.
  repeat (case neq; repeat split; simpl; nw; auto).
intros y sc; case y; auto.
Qed.

 Lemma ztest: forall x y,
     x ?= y =Zeq_bool (z2Z x) (z2Z y).
 Proof.
 intros x y; generalize (op_spec.(spec_compare) x y);
   unfold neq; case znz_compare; intros H.
 symmetry; apply GZnZ.Zeq_iok; auto.
 case_eq (Zeq_bool (z2Z x) (z2Z y)); intros H1; auto;
   generalize H; generalize (Zeqb_ok _ _ H1); unfold z2Z;
   intros HH; rewrite HH; auto with zarith.
 case_eq (Zeq_bool (z2Z x) (z2Z y)); intros H1; auto;
   generalize H; generalize (Zeqb_ok _ _ H1); unfold z2Z;
   intros HH; rewrite HH; auto with zarith.
 Qed.

 Lemma zc0: z2Z c0 = 0.
 Proof.
 unfold z2Z, c0, z2Z; simpl.
 generalize op_spec.(spec_0); auto.
 Qed.


Ltac iftac t := 
  match t with 
   context[if ?x ?= ?y then _ else _] =>
      case_eq (x ?= y)
  end.

Ltac ftac := match goal with
  |- context[?x = ?y] => (iftac x); 
    let H := fresh "tmp" in 
     (try rewrite ztest; try rewrite zc0; intros H;
      repeat ((rewrite nmulz in H || rewrite nplusz in H || rewrite nsubz in H); auto);
      try (rewrite H; clear H))
    end.

Require Import Zmod.

Lemma c2ww: forall x, ZEll.nmul (vN exx) 2 x = ZEll.nmul (vN exx) (z2Z c2) x.
intros x; unfold ZEll.nmul.
unfold c2; rewrite z2Zx; rewrite Zmodml; auto.
Qed.
Lemma c3ww: forall x, ZEll.nmul (vN exx) 3 x = ZEll.nmul (vN exx) (z2Z c3) x.
intros x; unfold ZEll.nmul.
unfold c3; rewrite z2Zx; rewrite Zmodml; auto.
Qed.

Lemma Aww: forall x, ZEll.nmul (vN exx) exx.(vA) x = ZEll.nmul (vN exx) (z2Z A) x.
intros x; unfold ZEll.nmul.
unfold A; rewrite z2Zx; rewrite Zmodml; auto.
Qed.

Lemma nadd_correct: forall x y sc,
  wfe x -> wfe y -> wft sc ->
  e2E (fst (nadd sc x y)) = fst (ZEll.nadd exx.(vN) exx.(vA) (z2Z sc) (e2E x) (e2E y) )/\
  z2Z (snd (nadd sc x y)) = snd (ZEll.nadd exx.(vN) exx.(vA) (z2Z sc) (e2E x) (e2E y)).
Proof.
intros x; case x; clear; auto.
intros x1 y1 z1 y; case y; clear; auto.
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
  intros y; case y; auto.
  Qed.


 Lemma ndouble_wf: forall x sc,
  wfe x -> wft sc ->
  wfe (fst (ndouble sc x)) /\  wft (snd (ndouble sc x)).
Proof.
intros x; case x; clear; auto.
intros x1 y1 z1 sc (wfx1,(wfy1, wfz1)) wfsc; 
    simpl; auto.
  repeat (case neq; repeat split; simpl; nw; auto).
Qed.


Lemma ndouble_correct: forall x sc,
  wfe x -> wft sc ->
  e2E (fst (ndouble sc x)) = fst (ZEll.ndouble exx.(vN) exx.(vA) (z2Z sc) (e2E x))/\
  z2Z (snd (ndouble sc x)) = snd (ZEll.ndouble exx.(vN) exx.(vA) (z2Z sc) (e2E x)).
Proof.
intros x; case x; clear; auto.
  intros x1 y1 z1 sc (wfx1,(wfy1, wfz1))  wfsc; simpl.
  ftac.
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz); auto).
  simpl; split; auto.
  repeat ((rewrite nmulz || rewrite nplusz || rewrite nsubz ||
           rewrite c2ww || rewrite c3ww || rewrite Aww); try nw; auto).
  Qed.

 Lemma npow_wf: forall n x sc,
  wfe x -> wft sc ->
  wfe (fst (npow sc x n)) /\  wft (snd (npow sc x n)).
Proof.
intros n; elim n; unfold npow; fold npow; auto.
intros n1 Hrec x sc H H1; case (Hrec x sc H H1).
case npow; auto.
simpl; intros a1 sc1 H2 H3.
case (ndouble_wf _ H2 H3); auto;
case ndouble; auto.
intros a2 sc2 H4 H5;apply nadd_wf; auto.
intros n1 Hrec x sc H H1; case (Hrec x sc H H1).
simpl; intros H2 H3.
case (ndouble_wf _ H2 H3); auto; case npow; auto.
Qed.

Lemma npow_correct: forall n x sc,
  wfe x -> wft sc ->
  e2E (fst (npow sc x n)) = fst (ZEll.npow exx.(vN) exx.(vA) (z2Z sc) (e2E x) n)/\
  z2Z (snd (npow sc x n)) = snd (ZEll.npow exx.(vN) exx.(vA) (z2Z sc) (e2E x) n).
Proof.
intros n; elim n; clear; simpl; auto.
intros n1 Hrec a1 sc1 H1 H2.
generalize (npow_wf n1 _ H1 H2); generalize (Hrec _ _ H1 H2); case npow; simpl.
case ZEll.npow; intros r1 rc1; simpl.
intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
generalize (ndouble_wf _ H5 H6); generalize (ndouble_correct _ H5 H6); case ndouble; simpl.
case ZEll.ndouble; intros r1 rc1; simpl.
intros a3 sc3 (H7,H8) (H9,H10); subst r1 rc1.
apply nadd_correct; auto.
intros n1 Hrec a1 sc1 H1 H2.
generalize (npow_wf n1 _ H1 H2); generalize (Hrec _ _ H1 H2); case npow; simpl.
case ZEll.npow; intros r1 rc1; simpl.
intros a2 sc2 (H3, H4) (H5, H6); subst r1 rc1.
apply ndouble_correct; auto.
Qed.

Lemma npowl_wf: forall l x sc,
  wfe x -> wft sc ->
  wfe (fst (npowl sc x l)) /\  wft (snd (npowl sc x l)).
Proof.
intros l1; elim l1; simpl; auto.
unfold npowl; simpl; intros a l2 Hrec x sc H1 H2.
generalize (npow_wf a _ H1 H2); case npow.
intros a1 sc1 (H3, H4); auto.
Qed. 

Lemma npowl_correct: forall l x sc,
  wfe x -> wft sc ->
  e2E (fst (npowl sc x l)) = fst (ZEll.npowl exx.(vN) exx.(vA) (z2Z sc) (e2E x) l)/\
  z2Z (snd (npowl sc x l)) = snd (ZEll.npowl exx.(vN) exx.(vA) (z2Z sc) (e2E x) l).
Proof.
intros l1; elim l1; simpl; auto.
unfold npowl, ZEll.npowl; simpl; intros a l2 Hrec x sc H1 H2.
generalize (npow_correct a _ H1 H2) (npow_wf a _ H1 H2); case npow.
case ZEll.npow; intros r1 rsc1; simpl.
simpl; intros a1 sc1 (H3, H4) (H5, H6); subst r1 rsc1; auto.
Qed.

Lemma npowl1_wf: forall l x sc,
  wfe x -> wft sc ->
  wfe (fst (npowl1 sc x l)) /\  wft (snd (npowl1 sc x l)).
Proof.
intros l1; elim l1; simpl; auto.
intros a l2 Hrec x sc H1 H2.
generalize (npow_wf a _ H1 H2); case npow; simpl.
intros a1 sc1 (H3, H4); auto.
generalize (npowl_wf l2 _ H1 H4); case npowl; simpl.
intros a2 sc2; case a2; simpl; auto.
intros x1 y1 z1 ((V1, (V2, V3)), V4); apply Hrec; auto.
Qed. 

Lemma npowl1_correct: forall l x sc,
  wfe x -> wft sc ->
  e2E (fst (npowl1 sc x l)) = fst (ZEll.npowl1 exx.(vN) exx.(vA) (z2Z sc) (e2E x) l)/\
  z2Z (snd (npowl1 sc x l)) = snd (ZEll.npowl1 exx.(vN) exx.(vA) (z2Z sc) (e2E x) l).
Proof.
intros l1; elim l1; simpl; auto.
intros a l2 Hrec x sc H1 H2.
generalize (npow_wf a _ H1 H2) (npow_correct a _ H1 H2); case npow; simpl.
case ZEll.npow; intros r1 rsc1; simpl.
intros a1 sc1 (H3, H4) (H5, H6); subst r1 rsc1.
generalize (npowl_wf l2 _ H1 H4) (npowl_correct l2 _ H1 H4); case npowl; simpl.
case ZEll.npowl; intros r1 rsc1; simpl.
intros a2 sc2 (H7, H8) (H9, H10); subst r1 rsc1.
generalize H7; clear H7; case a2; simpl; auto.
rewrite zc0; auto.
intros x1 y1 z1 (V1, (V2, V3)); auto.
generalize (nmulw H8 V3) (nmulz H8 V3); intros V4 V5; rewrite <- V5.
apply Hrec; auto.
rewrite zc0; auto.
Qed.

Lemma f4 : wft (Z2z 4).
Proof.
red; apply z2Zx1.
Qed.

Lemma f27 : wft (Z2z 27).
Proof.
red; apply z2Zx1.
Qed.

Lemma Bw : wft B.
Proof.
red; unfold B; apply z2Zx1.
Qed.

Hint Resolve f4 f27 Bw.

Lemma mww: forall x y, ZEll.nmul (vN exx) (x mod (vN exx) ) y = ZEll.nmul (vN exx) x y.
intros x  y; unfold ZEll.nmul; rewrite Zmodml; auto.
Qed.

Lemma wwA: forall x, ZEll.nmul (vN exx) x exx.(vA) = ZEll.nmul (vN exx) x (z2Z A).
intros x; unfold ZEll.nmul.
unfold A; rewrite z2Zx; rewrite Zmodmr; auto.
Qed.

Lemma wwB: forall x, ZEll.nmul (vN exx) x exx.(vB) = ZEll.nmul (vN exx) x (z2Z B).
intros x; unfold ZEll.nmul.
unfold B; rewrite z2Zx; rewrite Zmodmr; auto.
Qed.

 Lemma  npowl1_prime: 
  let a := ntriple (Z2z (exx.(vx))) (Z2z (exx.(vy))) c1 in
  let isc := (Z2z 4) ** A ** A ** A  ++ (Z2z 27) ** B ** B in
  let (a1, sc1) := npow isc a exx.(vS) in
  let (S1,R1) := psplit exx.(vR) in
  let (a2, sc2) := npow sc1 a1 S1 in
  let (a3, sc3) := npowl1 sc2 a2 R1 in
    match a3 with
     nzero => if (Zeq_bool (Zgcd (z2Z sc3) exx.(vN)) 1) then prime exx.(vN)
              else True
   | _ => True
   end.
  Proof.
  intros a isc.
  case_eq (npow isc a (vS exx)); intros a1 sc1 Ha1.
  case_eq (psplit (vR exx)); intros S1 R1 HS1.
  case_eq (npow sc1 a1 S1); intros a2 sc2 Ha2.
  case_eq (npowl1 sc2 a2 R1); intros a3 sc3; case a3; auto.
  intros Ha3; case_eq (Zeq_bool (Zgcd (z2Z sc3) (vN exx)) 1); auto.
  intros H1.
  assert (F0: 
     (vy exx mod vN exx) ^ 2 mod vN exx =
       ((vx exx mod vN exx) ^ 3 + vA exx * (vx exx mod vN exx) +
        vB exx) mod vN exx).
      generalize exxs.(inC).
      simpl; unfold Zpower_pos; simpl.
      repeat rewrite Zmult_1_r.
      intros HH.
      match goal with |- ?t1 = ?t2 => rmod t1; auto end.
      rewrite HH.
      rewrite Zmod_plus; auto; symmetry; rewrite Zmod_plus; auto; symmetry.
      apply f_equal2 with (f := Zmod); auto.
      apply f_equal2 with (f := Zplus); auto.
      rewrite Zmod_plus; auto; symmetry; rewrite Zmod_plus; auto; symmetry.
      apply f_equal2 with (f := Zmod); auto.
      apply f_equal2 with (f := Zplus); auto.
      rewrite Zmod_mult; auto; symmetry; rewrite Zmod_mult; auto; symmetry.
      apply f_equal2 with (f := Zmod); auto.
      apply f_equal2 with (f := Zmult); auto.
      rewrite Zmod_mod; auto.
      match goal with |- ?t1 = ?t2 => rmod t2; auto end.
      rewrite Zmod_mult; auto; symmetry; rewrite Zmod_mult; auto; symmetry.
      apply f_equal2 with (f := Zmod); auto.
      rewrite Zmod_mod; auto.
   generalize (@ZEll.npowl1_prime exx.(vN) 
               (exx.(vx) mod exx.(vN))
               (exx.(vy) mod exx.(vN))
               exx.(vA)
               exx.(vB) 
               exxs.(n_pos) exxs.(n2_div) exx.(vR) 
               exxs.(lprime) exx.(vS) exxs.(lbig) F0); simpl.
generalize (@npow_wf (vS exx) a isc) (@npow_correct (vS exx) a isc).
unfold isc.
rewrite nplusz; auto; try nw; auto.
repeat rewrite nmulz; auto; try nw; auto.
  repeat rewrite z2Zx.
repeat rewrite wwA || rewrite wwB|| rewrite mww.
replace (e2E a) with (ZEll.ntriple (vx exx mod vN exx) (vy exx mod vN exx) 1).
case ZEll.npow.
fold isc; rewrite HS1; rewrite Ha1; simpl; auto.
intros r1 rsc1 HH1 HH2.
case HH1; clear HH1.
  unfold c1; repeat split; red; try apply z2Zx1.
  unfold isc; nw.
case HH2; clear HH2.
  unfold c1; repeat split; red; try apply z2Zx1.
  unfold isc; nw.
intros U1 U2 W1 W2; subst r1 rsc1.
generalize (@npow_wf S1 a1 sc1) (@npow_correct S1 a1 sc1).
case ZEll.npow.
intros r1 rsc1 HH1 HH2.
case HH1; clear HH1; auto.
case HH2; clear HH2; auto.
rewrite Ha2; simpl.
intros U1 U2 W3 W4; subst r1 rsc1.
generalize (@npowl1_wf R1 a2 sc2) (@npowl1_correct R1 a2 sc2).
case ZEll.npowl1.
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
intros sc4; rewrite Ha3; simpl; auto.
intros _ HH; case HH; auto.
intros; discriminate.
unfold a; simpl.
unfold c1; repeat rewrite z2Zx.
rewrite (Zmod_def_small 1); auto.
generalize exxs.(n_pos).
auto with zarith.
Qed.

End NEll.

