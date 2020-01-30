(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Import Ring.
Require Import Field_tac.
Require Import Ring_tac.
Require Import Eqdep_dec.
Require Import ZArith.
Require Import ZCAux.
Require Import Ppow.
Require Import GZnZ.
Require Import EGroup.
Require Import SMain.
Require Import Zmod.

Set Implicit Arguments.

Open Scope Z_scope.

Section Nell.

 Variable N: Z.
 Variable (A B: Z).
 Hypothesis N_lt_2: 2 < N.
 Hypothesis N_not_div_2: ~(2 | N).
 Hypothesis NonSingular: rel_prime N (4 * A * A * A  + 27 * B * B).

 Inductive nelt: Set :=
   nzero | ntriple: Z -> Z -> Z  -> nelt.

 Definition nplus x y := (Zmod (x + y) N).
 Definition nmul x y := (Zmod (x * y) N).
 Definition nsub x y := (Zmod (x - y) N).
 Definition ninv x := (Zmod (-x) N).

 Notation "x ++ y " := (nplus x y).
 Notation "x -- y" := (nsub x y) (at level 50, left associativity).
 Notation "x ** y" := (nmul x y) (at level 40, left associativity).
 Notation "-- x" := (ninv x) (at level 40, left associativity).

 Notation "x ?= y" := (Zeq_bool x y).

 Definition ndouble := fun (sc: Z) (p1: nelt) =>
 match p1 with
  nzero => (p1, sc)
 | (ntriple x1 y1 z1) =>
    if (y1 ?= 0) then (nzero, z1 ** sc) else
     (* we do 2p *)
    let m' := 3 ** x1 ** x1 ++ A ** z1 ** z1 in
    let l' := 2 ** y1 ** z1 in
    let m'2 := m' ** m' in
    let l'2 := l' ** l' in
    let l'3 := l'2 ** l' in
    let x3 := m'2 ** z1 -- 2 ** x1 ** l'2 in
    (ntriple
          (l' ** x3)
          (l'2 ** (m' ** x1 -- y1 ** l') -- m' ** x3)
          (z1 ** l'3), sc)
  end.

 Definition nadd := fun (sc: Z) (p1 p2: nelt) =>
 match p1, p2 with
  nzero, _ => (p2, sc)
 | _ , nzero => (p1, sc)
 | (ntriple x1 y1 z1), (ntriple x2 y2 z2) =>
  let d1 := x2 ** z1 in
  let d2 := x1 ** z2 in
  let l := d1 -- d2 in
  let dl := d1 ++ d2 in
  let m := y2 ** z1 -- y1 ** z2 in
  if (l ?= 0) then
   (* we have p1 = p2 o p1 = -p2 *)
   if (m ?= 0) then
    if (y1 ?= 0) then (nzero, z1 ** z2 ** sc) else
     (* we do 2p *)
    let m' := 3 ** x1 ** x1 ++ A ** z1 ** z1 in
    let l' := 2 ** y1 ** z1 in
    let m'2 := m' ** m' in
    let l'2 := l' ** l' in
    let l'3 := l'2 ** l' in
    let x3 := m'2 ** z1 -- 2 ** x1 ** l'2 in
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

 Definition inversible n x := exists y, Zmod (x * y) n = 1%Z.


 Lemma inversible_1: forall n, 1 < n -> inversible n 1.
 Proof.
 intros n Hn; exists 1%Z; rewrite Zmult_1_r;
   apply Zmod_small; split; auto with zarith.
 Qed.


 Notation "[ x ]" := (inversible N x).

 Lemma inversible_0: ~[0].
 Proof.
 intros HH; inversion_clear HH as [xz H1].
 rewrite Zmod_small in H1; auto with zarith.
 Qed.

 Lemma inversible_mult_inv: forall x y, [x ** y] -> [x] /\ [y].
 Proof.
 assert (F1 := N_lt_2).
 intros x y (z, Hz); split.
 exists (y * z)%Z; rewrite <- Hz.
 unfold nmul.
 rewrite Zmodml; auto with zarith.
 rewrite Zmult_assoc; auto.
 exists (x * z)%Z; rewrite <- Hz.
 unfold nmul.
 rewrite Zmodml; auto with zarith.
 rewrite Zmult_assoc; auto.
 rewrite (Zmult_comm x); auto.
 Qed.

 Inductive nInversible: nelt * Z -> Prop :=
  nInv_z: forall sc, inversible N sc -> nInversible (nzero, sc)
 |nInv_e: forall x y z sc,
     inversible N (sc ** z) -> nInversible (ntriple x y z, sc).

 Notation "[[ x ]]" := (nInversible x).

 Lemma inversible_mult: forall a b, [a] -> [b] -> [a ** b].
 Proof.
 assert (F1 := N_lt_2).
 intros a b (z1, H1) (z2, H2).
 exists (z1 * z2)%Z.
 unfold nmul.
 rewrite Zmodml; auto with zarith.
 replace (a * b * (z1 * z2))%Z with ((a * z1) * (b * z2))%Z; try ring.
 rewrite Zmult_mod; auto with zarith.
 rewrite H1; rewrite H2; rewrite Zmod_small; auto with zarith.
 Qed.

 Ltac itac :=
  match goal with
   H: inversible _ (_ ** _) |- _ =>
        case (inversible_mult_inv _ _ H); clear H;
         let H1 := fresh "NI" in
         let H2 := fresh "NI" in intros H1 H2
 | |- inversible _ (_ ** _) =>
         apply inversible_mult
 end; auto.

 Lemma nInversible_double: forall sc x,
  [[ndouble sc x]] -> [[(x,1%Z)]] /\ [sc].
 Proof.
 assert (F1 := N_lt_2).
 assert (F2: inversible N 1).
   apply inversible_1; auto with zarith.
 unfold ndouble; intros sc x; case x; auto.
   intros H; inversion_clear H.
   repeat split; auto; try constructor; auto.
 intros x1 y1 z1; case Zeq_bool; auto.
   intros H; inversion_clear H.
   repeat split; auto; try constructor; auto; repeat itac.
 intros H; inversion_clear H; auto.
 repeat split; auto; try constructor; repeat itac; auto.
 Qed.

 Lemma nInversible_add: forall sc x y,
  [[nadd sc x y]] -> [[(x,1%Z)]] /\ [[(y,1%Z)]] /\ [sc].
 Proof.
 assert (F1 := N_lt_2).
 assert (F2: inversible N 1).
   apply inversible_1; auto with zarith.
 unfold nadd; intros sc x y; case x; auto.
   intros H; inversion_clear H.
   repeat split; auto; try constructor; auto.
   repeat split; auto; try constructor; repeat itac.
 intros x1 y1 z1; case y; auto.
   intros H; inversion_clear H.
   repeat split; auto; try constructor; repeat itac.
 intros x2 y2 z2; case Zeq_bool.
 case Zeq_bool.
 case Zeq_bool.
 intros H; inversion_clear H; auto.
 repeat split; auto; try constructor; repeat itac.
 intros H; inversion_clear H; auto.
 repeat split; auto; try constructor; repeat itac.
 intros H; inversion_clear H; auto.
 repeat split; auto; try constructor; repeat itac.
 intros H; inversion_clear H; auto.
 repeat split; auto; try constructor; repeat itac.
 Qed.


 Definition nopp p :=
   match p with nzero => p | (ntriple x1 y1 z1) => (ntriple x1 (-- y1) z1) end.

 Fixpoint scalb (sc: Z) (b:bool) (a: nelt) (p: positive) {struct p}:
   nelt * Z :=
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

 Lemma nInversible_scalb: forall b sc a1 p1,
  [[scalb sc b a1 p1]] -> [[(a1,1%Z)]] /\ [sc].
 Proof.
 assert (F1 := N_lt_2).
 assert (F2: [1]).
   apply inversible_1; auto with zarith.
 intros b sc a p0; generalize sc b a; elim p0; simpl; auto;
    clear sc b a p0.
 intros p0 Hrec sc b a.
   generalize (Hrec sc true a).
   case scalb.
   intros a1 sc1 H; case b; intros H1; try apply H; clear b H.
     case (nInversible_double sc1 a1 H1); auto; clear H1.
     intros H2 H3; inversion_clear H2; try constructor;
       repeat itac; auto.
     generalize H1 (nInversible_double sc1 a1); case ndouble.
     intros a2 sc2 H2 H3; case H3.
       generalize (nInversible_add sc2 (nopp a) a2 H2).
        intros H4; case H4; intros _ [H5 H6].
        inversion_clear H5; constructor; repeat itac; auto.
        intros H4; inversion_clear H4; constructor; repeat itac; auto.
 intros p0 Hrec sc b a.
   generalize (Hrec sc false a).
   case scalb.
   intros a1 sc1 H; case b; intros H1; try apply H; clear b H.
     generalize H1 (nInversible_double sc1 a1); case ndouble.
     intros a2 sc2 H2 H3; case H3.
       generalize (nInversible_add sc2 a a2 H2).
        intros H4; case H4; intros _ [H5 H6].
        inversion_clear H5; constructor; repeat itac; auto.
        intros H4; inversion_clear H4; constructor; repeat itac; auto.
     case (nInversible_double sc1 a1 H1); auto; clear H1.
     intros H2 H3; inversion_clear H2; try constructor;
       repeat itac; auto.
 intros sc b a; case b; intros H.
   case (nInversible_double _ _ H); auto; clear H.
 inversion_clear H; split; try constructor; repeat itac; auto.
 Qed.

 Lemma nInversible_scal: forall sc a1 p1,
  [[scal sc a1 p1]] -> [[(a1,1%Z)]] /\ [sc].
 Proof.
 exact (nInversible_scalb false).
 Qed.

  Definition scal_list sc a l :=
   List.fold_left
  (fun (asc: nelt * Z) p1 => let (a,sc) := asc in scal sc a p1) l (a,sc).

 Lemma nInversible_scal_list: forall sc a l,
  [[scal_list sc a l]] -> [[(a,1%Z)]] /\ [sc].
 Proof.
 assert (F1 := N_lt_2).
 assert (F2: [1]).
   apply inversible_1; auto with zarith.
 intros sc a l; generalize sc a; unfold scal;
   elim l; simpl; auto;
    clear sc a l.
  intros sc a; unfold scal_list; simpl.
    intros HH; inversion_clear HH; split; auto;
      try constructor; repeat itac; auto.
 intros n1 l1 Hrec sc a.
 unfold scal_list; simpl.
   generalize (nInversible_scal sc a n1).
   case scal.
   intros n z H1 H2.
   case (Hrec _ _ H2).
   intros H3 H4; apply H1; auto.
     inversion_clear H3; constructor; repeat itac; auto.
 Qed.


 Definition Zmull l := List.fold_left Pmult l 1%positive.

 Lemma Zmull_cons: forall a l, Zmull (List.cons a l) = (a * (Zmull l))%positive.
 Proof.
 intros a l.
 assert (F1:= Pmult_assoc).
 assert (F2:= Pmult_comm).
 unfold Zmull.
 repeat rewrite List.fold_symmetric; simpl; auto; intros; rewrite F2; auto.
 Qed.

 Fixpoint scalL (sc:Z) (a: nelt) (l: List.list positive) {struct l}: (nelt * Z) :=
   match l with
     List.nil => (a,sc)
   | List.cons n l1 =>
        let (a1, sc1) := scal sc a n in
        let (a2, sc2) := scal_list sc1 a l1 in
          match a2 with
             nzero => (nzero, 0)
          |  ntriple _ _ z => scalL (sc2 ** z) a1 l1
          end
   end.

 Lemma nInversible_scalL: forall sc a l,
  [[scalL sc a l]] -> [[(a,1%Z)]] /\ [sc].
 Proof.
 assert (F1 := N_lt_2).
 assert (F2: [1]).
   apply inversible_1; auto with zarith.
 intros sc a l; generalize sc a;
   elim l; simpl; auto;
    clear sc a l.
  intros sc a; unfold scal_list; simpl.
    intros HH; inversion_clear HH; split; auto;
      try constructor; repeat itac; auto.
 intros n1 l1 Hrec sc a.
   generalize (nInversible_scal sc a n1).
   case scal.
 intros n z H.
   generalize (nInversible_scal_list z a l1).
   case scal_list.
 intros m z1; case m.
   intros _ HH; inversion_clear HH.
   case inversible_0; auto.
 intros x2 y2 z2 H1 H2.
 case (Hrec _ _ H2).
 intros H3 H4.
 case H1; try intros H5 H6.
  constructor; auto.
 split; auto.
 case H; auto.
 inversion_clear H3; auto; constructor; auto.
 repeat itac.
 Qed.

Local Coercion Zpos : positive >-> Z.

 Lemma Zmull_div: forall a l, List.In a l ->
    Zmull l  = (Zmull l / a) * a :> Z.
 intros a l; generalize a; elim l; clear a l; auto.
 intros a H; inversion H.
 simpl List.In; intros a l Hrec b [H | H]; subst.
   rewrite Zmull_cons.
   repeat rewrite Zpos_mult_morphism.
   rewrite (Zmult_comm b).
   repeat rewrite Z_div_mult; auto.
   red; simpl; auto.
 repeat rewrite Zmull_cons.
 repeat rewrite Zpos_mult_morphism.
 rewrite (Hrec b); auto.
 rewrite Zmult_assoc.
 rewrite Z_div_mult; auto.
 red; simpl; auto.
 Qed.

 Definition Zmullp l :=
    List.fold_left (fun y x => (Pmult (Ppow (fst x) (snd x)) y)) l 1%positive.


 Lemma Zmullp_cons: forall a l,
    Zmullp (List.cons a l) = ((Ppow (fst a) (snd a)) * (Zmullp l))%positive.
 Proof.

 intros a l.
 assert (F1:= Pmult_assoc).
 assert (F2:= Pmult_comm).
 unfold Zmullp.
 simpl.
 rewrite F2; simpl Pmult.
 generalize (Ppow (fst a) (snd a)).
 elim l; simpl; auto.
   intros p; rewrite F2; auto.
 intros a1 l1 Hrec p; rewrite Hrec.
 symmetry; rewrite Hrec.
 symmetry; rewrite F1.
 rewrite (F2 p); rewrite (fun x => (F2 x 1%positive)); auto.
 Qed.

 Fixpoint psplit l: positive * (List.list positive) := match l with
   List.nil => (xH, List.nil)
 | List.cons (a, xH) l1 =>
              let (v, l2) := psplit l1 in (v, (List.cons a l2))
 | List.cons (a, n) l1 =>
              let (v, l2) := psplit l1 in
             (Pmult (Ppow a (Pos.pred n)) v, (List.cons a l2))
 end.

 Lemma psplit_correct: forall l,
   Pmult (fst (psplit l)) (Zmull (snd (psplit l))) = Zmullp l.
 Proof.
 assert (F1:= Pmult_assoc).
 assert (F2:= Pmult_comm).
 intros l; elim l; unfold psplit; fold psplit.
   simpl; auto.
   intros (a, n); case n.
     intros n1 l1; case_eq (psplit l1); simpl fst; simpl snd.
       intros p1 l2 Hp1 H1.
       rewrite Zmullp_cons; simpl fst; simpl snd.
       rewrite Zmull_cons; rewrite <- H1.
       simpl Ppow.
       symmetry; rewrite <- F1; rewrite (F2 a).
       rewrite (F2 a); repeat rewrite F1; auto.
     intros n1 l1; set (u := Pos.pred (xO n1));
       case_eq (psplit l1); simpl fst; simpl snd.
       intros p1 l2 Hp1 H1.
       rewrite Zmullp_cons; simpl fst; simpl snd.
       case (Psucc_pred (xO n1)).
         intros HH; discriminate.
       intros HH; rewrite <- HH.
       rewrite Pplus_one_succ_l; rewrite Ppow_plus.
       fold u; simpl Ppow.
       rewrite Zmull_cons; rewrite <- H1.
       repeat rewrite F1.
       rewrite (F2 a).
       rewrite <- (F1 (Ppow a u)); rewrite (F2 p1).
       repeat rewrite F1; auto.
     intros l1; case_eq (psplit l1); simpl fst; simpl snd.
       intros p1 l2 Hp1 H1.
       rewrite Zmullp_cons; simpl fst; simpl snd.
       rewrite Zmull_cons; rewrite <- H1.
       simpl Ppow.
       repeat rewrite F1.
       rewrite (F2 a); auto.
 Qed.

 Lemma psplit_prime: forall l (p: positive),
  (forall (q: positive * positive), List.In q l -> prime (fst q)) ->
   prime p -> (p | Zmullp l)%Z -> List.In p (snd (psplit l)).
 Proof.
 intros l; elim l.
   unfold Zmullp; simpl.
   intros p _ H1 H2.
    case H1.
    absurd (p <= 1).
      apply Zlt_not_le; case H1; auto.
      apply Zdivide_le; auto with zarith.
   intros (a1, n1) l1 Hrec p Hp Hp1 Hp2.
   rewrite Zmullp_cons in Hp2.
   rewrite Zpos_mult_morphism in Hp2.
   case (prime_mult _ Hp1 _ _ Hp2); intros H1.
     assert (Hap: prime a1).
       change a1 with (fst (a1, n1)); apply Hp; auto with datatypes.
     simpl; case n1; try intros p1; case psplit; intros p2 l2; simpl snd;
      left;
      assert (HH: Zpos a1 = p); try (injection HH; auto);
     symmetry; apply prime_div_Zpower_prime with (Zpos n1); auto with zarith;
       rewrite <- Ppow_correct; auto.
   assert (HH: List.In p (snd (psplit l1))).
     apply Hrec; auto with datatypes.
   generalize HH; simpl.
   case psplit; case n1; simpl snd; auto with datatypes.
 Qed.

 Section pell.

  Variable p: Z.
  Hypothesis p_prime: prime p.
  Hypothesis p_div_N: (p | N)%Z.

  Let p_pos:= GZnZ.p_pos _ p_prime.

  Definition pK := (znz p).

  Let to_p x:pK := mkznz _ _ (modz _  x).

  Notation "x :%p" := (to_p x) (at level 30).

  Definition pkO: pK := (zero _).

  Definition pkI: pK := (one _).

  Definition pkplus: pK -> pK -> pK := (GZnZ.add _).

  Definition pkmul: pK -> pK -> pK := (mul _).

  Definition pksub: pK -> pK -> pK := (sub _).

  Definition pkopp: pK -> pK := (GZnZ.opp _).

  Definition pkinv: pK -> pK := (inv _).

  Definition pkdiv: pK -> pK -> pK := (div _).

  Definition pA: pK := to_p A.

  Definition pB: pK := to_p B.

  Definition pKfth:  field_theory pkO pkI pkplus pkmul pksub pkopp
                      pkdiv pkinv (@eq pK)
               := (FZpZ _ p_prime).

  (* K notations *)
  Notation "x + y" := (pkplus x y).  Notation "x * y " := (pkmul x y).
  Notation "x - y " := (pksub x y). Notation "- x" := (pkopp x).
  Notation "/ x" := (pkinv x). Notation "x / y" := (pkdiv x y).
  Notation "0" := pkO.
  Notation "1" := pkI.
  Notation "2" := (1+1).
  Notation "3" := (1+1 +1).
  (* Non singularity *)
  Notation "4" := (2 * 2).
  Notation "27" := (3 * 3 * 3).

  Add Ring RFth : (F_R pKfth).
  Add Field KFth : pKfth.


  Lemma pNonSingular: 4 * pA * pA * pA  + 27 * pB * pB <> 0.
  Proof.
  assert (F1 := p_pos).
  intros H; generalize (znz_inj _ _ _ H).
  unfold pkO,pkI,pA, pB, to_p, zero, one, pkplus, GZnZ.add, pkmul, mul, val.
  repeat match goal with |- ?t = 0 mod p -> _ =>
   rmod t; auto
  end.
  rewrite (Zmod_small 0); auto with zarith.
  intros H1.
  apply (fun H HH => rel_prime_mod H HH H1).
  generalize (prime_ge_2 _ p_prime); auto with zarith.
  apply rel_prime_sym; auto.
  apply rel_prime_div with N; try apply p_div_N.
  generalize NonSingular.
  repeat rewrite Zmult_assoc; auto.
  Qed.

  (* Characteristic greater than 3 *)

  Lemma pone_not_zero: 1 <> 0.
  Proof.
  intros H; generalize (znz_inj _ _ _ H); simpl val.
  repeat (rewrite Zmod_small); generalize (prime_ge_2 _ p_prime);
    auto with zarith.
  Qed.

  Lemma ptwo_not_zero: 2 <> 0.
  Proof.
  intros H; generalize (znz_inj _ _ _ H); simpl val.
  repeat (rewrite Zmod_small); generalize (prime_ge_2 _ p_prime);
    auto with zarith.
  intros H1; case (Zle_lt_or_eq _ _ H1); intros H2; auto with zarith.
  case N_not_div_2; rewrite H2; auto.
  Qed.

  Definition pis_zero: pK -> bool.
  intros (k, Hk); case k; [exact true | idtac | idtac];
    intros; exact false.
  Defined.

  Lemma pis_zero_correct: forall k: pK, pis_zero k = true <-> k = 0.
  Proof.
  assert (F0 := p_pos).
  intros (k, Hk); generalize Hk; case k; simpl.
    intros Hk1; split; auto; intros H; unfold pkO, zero.
    apply (zirr p); rewrite Zmod_small; auto with zarith.
  intros Hk1; split; auto; intros H; try discriminate.
  intros Hk1; split; auto; intros H; try discriminate.
  Qed.

  Lemma pell_theory: ell_theory pkO pkI pkplus pkmul pksub pkopp pkinv
                                 pkdiv pA pB pis_zero.
  Proof.
  constructor.
  apply pKfth.
  apply pNonSingular.
  exact pone_not_zero.
  exact ptwo_not_zero.
  exact pis_zero_correct.
  Qed.


  Definition pG:=  (EFGroup pell_theory (uniq_all_znz _ p_pos)
                                         (in_all_znz _ p_pos)).

  Lemma gorder_pG: FGroup.g_order pG <= 2 * p + 1.
  Proof.
  replace p with (Z_of_nat (List.length (all_znz _ p_pos))).
  unfold pG; apply EFGroup_order.
  rewrite all_znz_length.
  generalize (prime_ge_2 _ p_prime).
  case p; simpl; auto.
   intros p1 Hp1; rewrite Zpos_eq_Z_of_nat_o_nat_of_P; auto.
   intros p1 HH; case HH; auto.
  Qed.


  Let pelt := pelt pkI pkplus pkmul pA pB.
  Let mk_pelt := mk_pelt pkI pkplus pkmul pA pB.

  Lemma is_zero_correct: forall x y,
    if (x ?= y) then x = y else x <> y.
  Proof.
  intros x y; unfold Zeq_bool.
  case (Zcompare_Eq_iff_eq x y).
  case Z.compare; auto.
  intros _ H1 H2; assert (H3:= H1 H2); discriminate.
  intros _ H1 H2; assert (H3:= H1 H2); discriminate.
  Qed.

  Lemma inversible_is_not_k0: forall x, [x] -> x :%p  <> 0.
  Proof.
  intros x1 (k, Hk) H1.
  assert (F2: 2 < p).
    case (Zle_lt_or_eq _ _  (prime_ge_2 p p_prime)); auto.
    intros HH1; case N_not_div_2; rewrite HH1.
    apply p_div_N.
  assert (F3:= N_lt_2).
  injection H1; clear H1; rewrite (Zmod_small 0);
    auto with zarith; intros HH.
  absurd ((x1 * k) mod p = ((x1 * k) mod N) mod p).
    rewrite Hk.
    rewrite Zmult_mod; auto with zarith.
    rewrite HH; rewrite Zmult_0_l.
    repeat rewrite Zmod_small; auto with zarith.
  apply Zmod_div_mod; auto with zarith.
  Qed.

  Lemma inversible_is_zero: forall x,
    [x] -> pis_zero (x :%p) = false.
  Proof.
  intros x1 H1.
  case (pis_zero_correct (to_p x1)); case pis_zero; auto.
  intros HH _; generalize (HH (refl_equal true)); clear HH;
    intros HH.
  case (@inversible_is_not_k0 x1); auto.
  Qed.

  Lemma to_p_nmul: forall x y, (x ** y):%p =  x:%p * y:%p.
  Proof.
  intros x y.
  unfold nmul, to_p, pkmul, mul.
  unfold pK; apply zirr; simpl.
  assert (F1:= p_pos).
  rewrite <- Zmod_div_mod; auto.
  rewrite Zmult_mod; auto.
  generalize N_lt_2; auto with zarith.
  Qed.

  Lemma to_p_pow: forall x n,
     (x ^ (Z_of_nat n)):%p  =  pow pkI pkmul (x:%p) n.
  Proof.
  intros x n; elim n; clear n.
    simpl Z_of_nat; simpl pow; rewrite Zpower_0_r; auto.
  intros n Hrec; rewrite inj_S; unfold Z.succ; rewrite Zpower_exp; auto with zarith.
  assert (tmp: forall n x, pow 1 pkmul x (S n) = x * pow 1 pkmul x n).
    intros n1 x1; case n1; simpl; auto; ring.
  rewrite tmp; clear tmp.
  rewrite <- Hrec; rewrite <- to_p_nmul.
  rewrite Zpower_1_r; rewrite Zmult_comm.
  unfold to_p, nmul, pkmul, pK; apply zirr; simpl.
  assert (F1:= p_pos).
  rewrite <- Zmod_div_mod; auto with zarith.
  Qed.

  Lemma to_p_nplus: forall x y, (x ++ y):%p = x:%p + y:%p.
  Proof.
  intros x y.
  unfold nplus, to_p, pkplus, GZnZ.add.
  unfold pK; apply zirr; simpl.
  assert (F1:= p_pos).
  rewrite <- Zmod_div_mod; auto.
  rewrite Zplus_mod; auto.
  generalize N_lt_2; auto with zarith.
  Qed.

  Lemma to_p_nsub: forall x y, (x -- y):%p = x:%p - y:%p.
  Proof.
  intros x y.
  unfold nsub, to_p, pksub, GZnZ.sub.
  unfold pK; apply zirr; simpl.
  assert (F1:= p_pos).
  rewrite <- Zmod_div_mod; auto.
  rewrite Zminus_mod; auto.
  generalize N_lt_2; auto with zarith.
  Qed.

  Lemma to_p_2: 2:%p = 2.
  Proof.
  unfold to_p, pkplus, pkI, GZnZ.add, pK; apply zirr; simpl.
  assert (F1:= p_pos).
  rewrite <- Zplus_mod; auto.
  Qed.

  Lemma to_p_3: 3:%p = 3.
  Proof.
  unfold to_p, pkplus, pkI, GZnZ.add, pK; apply zirr; simpl.
  assert (F1:= p_pos).
  repeat match goal with |- _ = ?t =>
   rmod t; auto
  end.
  Qed.

  Ltac to_p_tac :=  repeat (rewrite to_p_nmul || rewrite to_p_nplus ||
         rewrite to_p_nsub || rewrite to_p_2 ||
         rewrite to_p_3); auto.

  Lemma inversible_kO: forall z1 z2,
     z2 = 0 -> z1:%p = z2 -> [z1] -> False.
  Proof.
  intros z1 z2 H1 H2 H3.
  generalize (inversible_is_not_k0 H3).
  rewrite H2; rewrite H1.
  intros H; case H; auto.
  Qed.

  Let pdouble: pelt -> pelt := pdouble (pell_theory).

  Let padd: pelt -> pelt -> pelt := padd (pell_theory).
  Let elt := (elt pkI pkplus pkmul pA pB).
  Let inf_elt := (inf_elt pkI pkplus pkmul pA pB).
  Let curve_elt := (curve_elt pkI pkplus pkmul pA pB).

  Inductive equiv: nelt -> elt -> Prop :=
     z_equiv:equiv nzero inf_elt
  |  n_equiv: forall x y z x1 y1 H,
      x:%p / z:%p = x1 ->
      y:%p / z:%p  = y1 ->
      equiv (ntriple x y z) (@curve_elt x1 y1 H).

  Infix "=~~=" := equiv (at level 40, no associativity).

  Let pe2e := pe2e pell_theory.
  Let add := add pell_theory.
  Let opp := opp pell_theory.
  Let pow := pow pkI pkmul.

  Lemma nedouble_correct: forall sc n1 p1,
    n1 =~~= p1 -> [[ndouble sc n1]] ->
       fst (ndouble sc n1) =~~= add p1 p1.
  Proof.
  intros sc n1 p1 H; inversion_clear H.
    simpl; intros; constructor.
  intros V1.
  case (nInversible_double _ _ V1); intros V2 _.
  inversion_clear V2.
  simpl.
  case Kdec; [idtac | intros HH; case HH]; auto.
  intros e.
  match goal with |- context[?x ?= ?y] =>
    generalize (is_zero_correct x y); case (Zeq_bool x y)
  end.
  intros HH; case Kdec.
     intros; constructor.
  intros HH1; case HH1; subst y1; rewrite HH.
  change (to_p 0) with pkO.
     field.
     intros HH2; apply inversible_kO with (2 := HH2); itac.
  intros HH1.
  assert (N1: inversible N y).
    inversion V1.
       generalize H3; generalize (Zeq_bool_eq y 0); case Zeq_bool.
         intros; case HH1; auto.
       intros; discriminate.
       generalize H3; case Zeq_bool; clear H3.
         intros; discriminate.
      intros HH; injection HH; clear HH.
      intros _ HH _ _; subst z0.
      repeat itac.
   assert (N2: to_p y <> pkO).
     intros HH; apply inversible_kO with (2 := HH); auto.
   assert (N3: to_p z <> pkO).
     intros HH; apply inversible_kO with (2 := HH); itac.
   case Kdec.
   intros HH; case N2.
     case (Kmult_integral pell_theory (1 + 1) y1).
      apply trans_equal with (y1 + y1); try ring.
      pattern y1 at 1; rewrite HH; ring.
    intros; case ptwo_not_zero; auto.
    intros; subst y1; field_simplify_eq in H3; auto.
   intros; simpl; constructor;
    to_p_tac; subst x1 y1; fold pA;
    set (v3 := (1 + (1 + 1)));
    set (v2 := (1 + 1)); field; repeat split; auto;
    apply ptwo_not_zero.
  Qed.

  Lemma neadd_correct: forall sc n1 p1 n2 p2,
    n1 =~~= p1 -> n2 =~~= p2 -> [[nadd sc n1 n2]] ->
      fst (nadd sc n1 n2) =~~= add p1 p2.
  Proof.
  intros sc n1 p1 n2 p2 H; inversion_clear H.
    simpl; auto.
  intros H; inversion_clear H.
    simpl; intros; constructor; auto.
  intros V1.
  case (nInversible_add _ _ _ V1); intros V2 (V3, _).
  inversion_clear V2.
  inversion_clear V3.
  repeat itac.
  simpl.
  assert (F0:= (inversible_is_not_k0 NI2)).
  assert (F0b:= (inversible_is_not_k0 NI0)).
  generalize V1; simpl.
  repeat match goal with |- context[?x ?= ?y] =>
    generalize (is_zero_correct x y); case (Zeq_bool x y)
  end; repeat case Kdec; auto.
  intros; constructor.
  intros n e K1 K2 K3 U1; subst y.
   match type of K2 with ?X = 0%Z =>
     cut ((to_p X) = pkO); [idtac | rewrite K2; auto];
     to_p_tac; clear K2; intros K2
   end.
   case (Kmult_integral pell_theory (to_p y0) (to_p z)); auto.
     rewrite <- K2; change (to_p 0) with pkO; ring.
   intros HH; case n; subst y1 y2; rewrite HH; auto.
   intros; case F0; auto.
  intros n K1 K2 K3 U1.
   case n; subst x1 x2.
    field_simplify_eq; auto.
    match type of K3 with ?X = 0%Z =>
       cut ((to_p X) = pkO); [idtac | rewrite K3; auto];
       to_p_tac; clear K3; intros K3
    end.
    match goal with |- ?X = _ =>
      apply trans_equal with (X + pkO); try ring
    end.
    rewrite <- K3; ring.
   intros K1 K2 K3 K4 _ U1; subst y1 y2.
   match type of K4 with ?X = 0%Z =>
     cut ((to_p X) = pkO); [idtac | rewrite K4; auto];
     to_p_tac; clear K4; intros K4
   end.
   field_simplify_eq in K1; auto.
  rewrite K1 in K4.
  case (Kmult_integral pell_theory (1 + 1) (to_p z * to_p y0)); auto.
  set (u := to_p z * to_p y0) in * |- *.
  apply trans_equal with (u + u); try ring.
  unfold u; rewrite <- K4; ring.
  intros; case ptwo_not_zero; auto.
  intros HH; case (Kmult_integral pell_theory _ _ HH); clear HH; intros HH.
  case F0; auto.
  rewrite HH in K1; ring_simplify in K1.
  case (Kmult_integral pell_theory (to_p y) (to_p z0)); auto.
(*    rewrite K1; ring. *)
  intros HH1.
  inversion_clear U1.
     repeat itac; auto.
     case (@inversible_is_not_k0 y); auto.
   intros; case F0b; auto.
   intros.
   assert (VV: to_p y <> pkO).
     apply inversible_is_not_k0.
     inversion_clear V0.
     repeat itac; auto.
   intros; simpl fst; constructor;
     to_p_tac; subst x1 y1; fold pA;
     set (v3 := (1 + (1 + 1)));
     set (v2 := (1 + 1)); field; repeat split; auto;
     apply ptwo_not_zero.
   intros n K1 K2 K3; case n; subst x1 x2.
     field_simplify_eq; auto.
     match type of K3 with ?X = 0%Z =>
       cut ((to_p X) = pkO); [idtac | rewrite K3; auto];
       to_p_tac; clear K3; intros K3
     end.
   apply trans_equal with (to_p z * to_p x0 - pkO); try ring.
   rewrite <- K3; try ring.
   intros; simpl fst; constructor.
   intros n K1 K2 K3 K4.
     inversion K4.
     repeat itac.
     case (inversible_is_not_k0 NI3).
     to_p_tac.
     rewrite <- K1 in H3.
     rewrite <- H3 in H0; simpl in H0.
     case (Kmult_integral pell_theory (y1 + y2) (y1 - y2)).
       ring [H0].
       intros HH; case n.
       apply trans_equal with (y1 - pkO); try ring;
         rewrite <- HH; ring.
     intros HH; subst y1 y2.
     assert (HH1:= Keq_minus_eq pell_theory _ _ HH).
     field_simplify_eq in HH1; auto.
     change (znz p) with pK; ring [HH1].
   intros n K1 K2 K3.
     case n; subst x1 x2; field_simplify_eq; auto.
     match type of K2 with ?X = 0%Z =>
       cut ((to_p X) = pkO); [idtac | rewrite K2; auto];
       to_p_tac; clear K2; intros K2
     end.
     assert (HH1:= Keq_minus_eq pell_theory _ _ K2); auto.
     ring [HH1].
   intros K1 K2 K3 K4.
     inversion_clear K4.
     repeat itac.
     case (inversible_is_not_k0 NI6).
     to_p_tac.
     apply (Keq_minus_eq_inv pell_theory).
     subst x1 x2; field_simplify_eq in K2; auto; ring [K2].
   intros K1 K2 K3 K4.
     inversion_clear K4.
     repeat itac.
     case (inversible_is_not_k0 NI6).
     to_p_tac.
     apply (Keq_minus_eq_inv pell_theory).
     subst x1 x2; field_simplify_eq in K2; auto; ring [K2].
   intros; simpl; constructor; to_p_tac;
     subst y2 x2 y1 x1; field; repeat split; auto.
   intros H1; case n; field_simplify_eq; auto.
     ring [(Keq_minus_eq pell_theory _ _ H1)]; auto.
   inversion_clear V0.
     repeat itac.
     intros H2; case (inversible_is_not_k0 NI6).
     to_p_tac.
  Qed.

 Lemma nopp_correct: forall a1 p1,
   a1 =~~= p1 -> [[(a1,1%Z)]] -> nopp a1 =~~= opp p1.
 Proof.
 assert (F0: 0 < p); auto with zarith.
 intros a1 p1 H; inversion_clear H; simpl; constructor; auto.
 rewrite <- H2.
 field_simplify_eq; auto.
 unfold ninv, pkopp, GZnZ.opp, to_p, pK; apply zirr.
 simpl; rewrite <- Zmod_div_mod; auto with zarith.
 pattern y at 1; rewrite (Z_div_mod_eq y p); auto with zarith.
 rewrite Zopp_plus_distr.
 rewrite Zopp_mult_distr_r.
 rewrite Zmult_comm; rewrite Zplus_comm;
   rewrite Z_mod_plus; auto with zarith.
 inversion_clear H.
 case (inversible_mult_inv _ _ H3); intros _ H4.
 intros H5; apply (@inversible_kO z 0); auto.
 Qed.

 Lemma scalb_correct: forall p sc b a1 p1,
   a1 =~~= p1 ->  [[scalb sc b a1 p]] ->
     fst (scalb sc b a1 p) =~~=
     EGroup.gpow p1 pG (if b then (Pos.succ p) else p).
 Proof.
 assert (F0: forall p1, List.In p1 (FGroup.s pG)).
    intros p1.
    apply (FELLK_in pell_theory _ (in_all_znz _ p_pos)).
 intros p0; unfold scalb; elim p0; clear p0; fold scalb.
   intros p0 Hrec sc b a1 p1; case b; clear b; intros H1.
     generalize (Hrec sc true a1 p1 H1)
                (nInversible_scalb true sc a1 p0); case scalb.
     intros a2 sc2 H2 H3.
     generalize (@nedouble_correct sc2 a2)
                (nInversible_double sc2 a2); case ndouble.
     intros a3 sc3 H4 H5 H6.
     case (H5 H6); clear H5; intros H5 H7.
     simpl Pos.succ.
     rewrite ZCmisc.Zpos_xO_add.
     repeat rewrite gpow_add; auto with zarith.
     apply H4; auto.
     apply H2.
     inversion_clear H5; try constructor; repeat itac;
       auto.
     generalize (Hrec sc true a1 p1 H1)
                (nInversible_scalb true sc a1 p0); case scalb.
     intros a2 sc2 H2 H3.
     generalize (@nedouble_correct sc2 a2)
                (nInversible_double sc2 a2); case ndouble.
     intros a3 sc3 H4 H5.
     generalize (fun p1 p2 => (@neadd_correct sc3 (nopp a1) p1 a3 p2))
                (nInversible_add sc3 (nopp a1) a3); case nadd.
     intros a4 sc4 H6 H7 H8.
     case (H7 H8); clear H7; intros H7 [H9 H10].
     case H5; clear H5.
        inversion_clear H9; try constructor; repeat itac; auto.
     intros H11 H12.
     case H3; clear H3.
        inversion_clear H11; try constructor; repeat itac; auto.
     intros H13 H14.
     rewrite ZCmisc.Zpos_xI_add.
     replace (gpow p1 pG (p0 + p0 + 1)) with
             (add (opp p1) (gpow p1 pG ((Pos.succ p0) + (Pos.succ p0)))).
     apply H6; auto.
       apply nopp_correct; auto.
     rewrite gpow_add; auto with zarith.
     apply H4; auto.
     apply H2; auto.
     inversion_clear H11; try constructor; repeat itac; auto.
     inversion_clear H9; try constructor; repeat itac; auto.
     rewrite ZCmisc.Psucc_Zplus.
     repeat rewrite gpow_add; auto with zarith.
     repeat rewrite gpow_1; auto with zarith.
     unfold add.
     repeat rewrite add_assoc.
     apply f_equal2 with (f := SMain.add pell_theory); auto.
     rewrite add_comm with (p2 := p1).
     repeat rewrite add_assoc.
     unfold opp; rewrite add_opp; simpl; auto.
   intros p0 Hrec sc b a1 p1; case b; clear b; intros H1.
     generalize (Hrec sc false a1 p1 H1)
                (nInversible_scalb false sc a1 p0); case scalb.
     intros a2 sc2 H2 H3.
     generalize (@nedouble_correct sc2 a2)
                (nInversible_double sc2 a2); case ndouble.
     intros a3 sc3 H4 H5.
     generalize (fun p1 p2 => (@neadd_correct sc3 a1 p1 a3 p2))
                (nInversible_add sc3 a1 a3); case nadd.
     intros a4 sc4 H6 H7 H8.
     case (H7 H8); clear H7; intros H7 [H9 H10].
     case H5; clear H5.
        inversion_clear H9; try constructor; repeat itac; auto.
     intros H11 H12.
     case H3; clear H3.
        inversion_clear H11; try constructor; repeat itac; auto.
     intros H13 H14.
     simpl Pos.succ.
     rewrite ZCmisc.Zpos_xI_add.
     replace (p0 + p0 + 1)%Z with
             (1 + (p0 + p0))%Z; auto with zarith.
     repeat rewrite gpow_add; auto with zarith.
     repeat rewrite gpow_1; auto with zarith.
     apply H6; auto.
     apply H4; auto.
     apply H2; auto.
     inversion_clear H11; try constructor; repeat itac; auto.
     inversion_clear H9; try constructor; repeat itac; auto.
     generalize (Hrec sc false a1 p1 H1)
                (nInversible_scalb false sc a1 p0); case scalb.
     intros a2 sc2 H2 H3.
     generalize (@nedouble_correct sc2 a2)
                (nInversible_double sc2 a2); case ndouble.
     intros a3 sc3 H4 H5 H6.
     case (H5 H6); clear H5; intros H5 H7.
     rewrite ZCmisc.Zpos_xO_add.
     repeat rewrite gpow_add; auto with zarith.
     apply H4; auto.
     apply H2; auto.
     inversion_clear H5; try constructor; repeat itac; auto.
  intros sc b a1 p1 H1; case b; intros H2; simpl gpow;
    rewrite add_0_r; auto.
  apply nedouble_correct; auto.
  Qed.

 Lemma scal_correct: forall p sc a1 p1,
   a1 =~~= p1 ->  [[scal sc a1 p]] ->
     fst (scal sc a1 p) =~~= EGroup.gpow p1 pG p.
 Proof.
 intros p1 sc; exact (scalb_correct p1 sc false).
 Qed.

 Lemma scal_list_correct: forall l sc a1 p1,
   a1 =~~= p1 ->  [[scal_list sc a1 l]] ->
     fst (scal_list sc a1 l) =~~= EGroup.gpow p1 pG (Zmull l).
 Proof.
 assert (F0: forall p1, List.In p1 (FGroup.s pG)).
    intros p1.
    apply (FELLK_in pell_theory _ (in_all_znz _ p_pos)).
 intros l; elim l; auto; clear l.
 intros sc a1 p1 H H1.
 change (Zmull List.nil) with (1%positive).
 rewrite gpow_1; auto.
 intros a l Hrec sc a1 p1 H1 H2.
 rewrite Zmull_cons.
 rewrite Zpos_mult_morphism.
 rewrite gpow_gpow; auto with zarith.
 unfold scal_list; simpl List.fold_left.
 case_eq (scal sc a1 a); intros a2 sc2 Ha2.
 change (equiv (fst (scal_list sc2 a2 l)) (gpow (gpow p1 pG a) pG (Zmull l))).
 apply Hrec.
   change a2 with (fst (a2, sc2)).
   rewrite <- Ha2.
   apply scal_correct; auto.
   case (nInversible_scal_list sc2 a2 l); auto.
     unfold scal_list; simpl; rewrite <- Ha2; auto.
     intros; rewrite Ha2.
     inversion_clear H; constructor; repeat itac; auto.
   unfold scal_list; simpl; rewrite <- Ha2; auto.
 Qed.


 Lemma scalL_not_1: forall l sc a p1 n,
    a =~~= p1 -> [[scalL sc a l]] ->  List.In n l ->
    gpow p1  pG (Zmull l / n) <> pG.(FGroup.e).
 Proof.
 assert (F0: forall p1, List.In p1 (FGroup.s pG)).
    intros p1.
    apply (FELLK_in pell_theory _ (in_all_znz _ p_pos)).
 intros l; elim l; auto; clear l.
 simpl (List.In).
 intros a l Hrec sc a1 p1 n H H1 [H2 | H2]; subst.
 case (nInversible_scalL _ _ _ H1); intros H3 H4.
 rewrite Zmull_cons.
 repeat rewrite Zpos_mult_morphism.
 rewrite (Zmult_comm n).
 repeat rewrite Z_div_mult; auto.
 generalize H1; simpl scalL.
 case scal.
 intros n1 sc1.
 generalize (@scal_list_correct l sc1 a1 p1 H).
 case scal_list.
 intros n2; case n2; clear n2.
 intros z2 _ HH; inversion HH; case inversible_0; auto.
 intros x1 y1 z1 sc2 H5 H6 H7.
 rewrite H7 in H5.
 simpl fst in H5.
 case (nInversible_scalL _ _ _ H6); intros H8 H9.
 absurd (ntriple x1 y1 z1 =~~= FGroup.e pG).
   intros HH; inversion HH.
 apply H5; constructor; auto.
 red; simpl; auto.
 rewrite Zmull_cons; auto.
 repeat rewrite Zpos_mult_morphism.
 case (nInversible_scalL _ _ _ H1); intros U1 U2.
 rewrite (Zmull_div n); auto.
 rewrite Zmult_assoc.
 rewrite Z_div_mult; auto.
 rewrite gpow_gpow; auto.
 case (nInversible_scalL _ _ _ H1); auto.
 intros H3 H4.
 simpl in H1; revert H1.
   case_eq (scal sc a1 a).
   intros n1 sc1 Hn1.
   case_eq (scal_list sc1 a1 l).
   intros n2 sc2; case n2.
     intros _ HH; inversion HH.
     case inversible_0; auto.
 intros x1 y1 z1 Hn2 H5.
 apply (@Hrec (sc2 ** z1)%Z n1); auto.
   change n1 with (fst (n1, sc1)).
   rewrite <- Hn1.
   apply scal_correct; auto.
   case (nInversible_scalL _ _ _ H5).
   intros H6 H7.
   case (nInversible_scal_list sc1 a1 l).
     rewrite Hn2; constructor; auto.
   intros H8 H9.
   rewrite Hn1; inversion H6; constructor; auto;
      repeat itac.
 red; simpl; auto; intros HH; discriminate.
 apply Z.ge_le; apply Z_div_ge0; red; simpl; auto;
   intros HH; discriminate.
 red; simpl; auto.
 Qed.


 Lemma  scalL_1: forall l sc a p1,
  a =~~= p1 -> [[scalL sc a l]] ->
  fst (scalL sc a l) =~~= gpow p1  pG (Zmull l).
 Proof.
 assert (F0: forall p1, List.In p1 (FGroup.s pG)).
    intros p1.
    apply (FELLK_in pell_theory _ (in_all_znz _ p_pos)).
 intros l; elim l; auto; clear l.
   simpl scalL; simpl fst; simpl Zmull.
     unfold Zmull; simpl List.fold_left.
     intros; rewrite gpow_1; auto.
 intros a l Hrec sc a1 p1 H1 H2.
 rewrite Zmull_cons.
 repeat rewrite Zpos_mult_morphism.
 rewrite gpow_gpow; auto.
   2: red;simpl; auto; intros HH; discriminate.
  2: red;simpl; auto; intros HH; discriminate.
 simpl in H2; revert H2; simpl scalL.
   case_eq (scal sc a1 a).
   intros n1 sc1 Hn1.
   case_eq (scal_list sc1 a1 l).
   intros n2 sc2; case n2.
     intros _ HH; inversion HH.
     case inversible_0; auto.
 intros x1 y1 z1 Hn2 H5.
 apply Hrec; auto.
 change n1 with (fst (n1, sc1)).
 rewrite <- Hn1.
 apply scal_correct; auto.
 case (nInversible_scalL _ _ _ H5).
 intros H6 H7.
 case (nInversible_scal_list sc1 a1 l).
 rewrite Hn2; constructor; auto.
 intros H8 H9.
 rewrite Hn1; inversion H6; constructor; auto; repeat itac.
 Qed.
 End pell.

End Nell.

Section pell.

 Variable N: Z.
 Variable (x y A B: Z).
 Hypothesis N_lt_2: 2 < N.
 Hypothesis N_not_div_2: ~(2 | N).
 Variable lR: List.list (positive * positive).

 Local Coercion Zpos : positive >-> Z.
 Hypothesis lR_prime: forall p, List.In p lR -> prime (fst p).
 Variable F: positive.
 Hypothesis lR_big: (4 * N < ((Zmullp lR) -1) ^2)%Z.
 Hypothesis on_curve: y^2 mod N = (x^3 + A * x + B) mod N.


 Notation "x ++ y " := (nplus N x y).
 Notation "x -- y" := (nsub N x y) (at level 50, left associativity).
 Notation "x ** y" := (nmul N x y) (at level 40, left associativity).
 Notation "x ?= y" := (Zeq_bool x y).

 Ltac itac :=
  match goal with
   H: inversible _ (_ ** _) |- _ =>
        case (inversible_mult_inv  N_lt_2 _ _ H); clear H;
         let H1 := fresh "NI" in
         let H2 := fresh "NI" in intros H1 H2
 | |- inversible _ (_ ** _) =>
         apply inversible_mult
 end; auto.

 Let z2p x := match x with Zpos p => p | Zneg p => p | Z0 => xH end.

 Lemma  scalL_prime:
  let a := ntriple x y 1 in
  let isc := 4 ** A ** A ** A  ++ 27 ** B ** B in
  let (a1, sc1) := scal N A isc a F in
  let (S1,R1) := psplit lR in
  let (a2, sc2) := scal N A sc1 a1 S1 in
  let (a3, sc3) := scalL N A sc2 a2 R1 in
    match a3 with
     nzero => if (Zeq_bool (Z.gcd sc3 N) 1) then prime N
              else True
   | _ => True
   end.
  Proof.
  assert (F0: 0 < N); try auto with zarith.
  intros a isc.
  case_eq (scal N A isc a F); intros a1 sc1 Ha1.
  case_eq (psplit lR); intros S1 R1 HS1.
  case_eq (scal N A sc1 a1 S1); intros a2 sc2 Ha2.
  case_eq (scalL N A sc2 a2 R1); intros a3.
  case a3; auto.
  intros sc3 Hsc3.
  generalize (Zeq_bool_eq (Z.gcd sc3 N) 1); case Zeq_bool; intros Hz; auto.
  case (prime_dec N); auto; intros Hn.
  case (Zdivide_div_prime_le_square N); auto with zarith.
  intros p (Hp, (Hp1, Hp2)).
  pose (p_pos:= GZnZ.p_pos _ Hp).
  pose (to_p := fun x =>  mkznz _ _ (modz p x)).
  assert (Ni1: nInversible N (scalL N A sc2 a2 R1)).
    rewrite Hsc3; constructor.
    assert (tmp: Bezout sc3 N 1).
      apply Zis_gcd_bezout.
      rewrite <- Hz; auto; apply Zgcd_is_gcd.
   inversion_clear tmp as [u v Huv].
   exists u.
   rewrite Zmult_comm.
   rewrite <- Z_mod_plus with (b := v); auto with zarith.
   rewrite Huv; rewrite Zmod_small; auto with zarith.
  case nInversible_scalL with (2 := Ni1); auto with zarith.
  intros Nt1 Nt2.
  assert (Ni2: nInversible N (scal N A sc1 a1 S1)).
    rewrite Ha2.
    inversion_clear Nt1; constructor; auto; repeat itac.
  case nInversible_scal with (2 := Ni2); auto with zarith.
  clear Nt1 Nt2; intros Nt1 Nt2.
  assert (Ni3: nInversible N (scal N A isc a F)).
    rewrite Ha1.
    inversion_clear Nt1; constructor; auto; repeat itac.
  case nInversible_scal with (2 := Ni3); auto with zarith.
  clear Nt1 Nt2; intros Ni4 Ni5.
  assert (Rp: rel_prime N (4 * A * A * A  + 27 * B * B)).
    case Ni5; intros z1 Hz1.
    apply bezout_rel_prime.
    set (d := 4 * A * A * A + 27 * B * B).
    apply Bezout_intro with (- ((d * z1)/N)) z1.
    generalize Hz1; unfold isc.
    unfold nplus, nmul.
    rewrite (Zmodml (4 * A)); auto.
    rewrite (Zmodml (4 * A * A)); auto.
    rewrite (Zmodml (27 * B)); auto.
    rewrite <- Zplus_mod; auto.
    rewrite Zmodml; auto; fold d; clear Hz1; intros Hz1.
    rewrite (Z_div_mod_eq (z1 * d) N); auto with zarith.
    rewrite (Zmult_comm z1).
    rewrite (Zmult_comm N).
    rewrite Zplus_assoc.
    rewrite (fun x y => Zplus_comm (x * y)).
    rewrite <- Zopp_mult_distr_l.
    rewrite Zplus_opp_r; auto.
  pose (pell := pell_theory A B N_not_div_2 Rp Hp Hp1).
  pose (pequiv := @equiv A B p).
  assert (Hoc: pow  (pkI p) (@pkmul p) (to_p y) 2 =
                pkplus
                 (pkplus
                    (pow (pkI p) (@pkmul p) (to_p x) 3)
                    (pkmul (pA A p) (to_p x)))
                 (pB B p)).
    unfold pA, pB, to_p.
    repeat rewrite <- (to_p_pow N_lt_2 Hp); auto.
    simpl Z_of_nat.
    repeat rewrite <- (to_p_nmul N_lt_2 Hp); auto.
    repeat rewrite <- (to_p_nplus N_lt_2 Hp); auto.
    apply (zirr p).
    rewrite (@Zmod_div_mod p N); auto;
       rewrite on_curve; rewrite <- Zmod_div_mod; auto.
       unfold nmul, nplus.
       rewrite (fun xx => @Zmodpr xx (x^3)); auto.
       rewrite Zmodpl; auto; rewrite <- Zmod_div_mod; auto.
  pose (pcurve_elt := curve_elt (pkI p) (@pkplus p)
                                (@pkmul p) (pA A p) (pB B p)).
  assert (E1: pequiv a (pcurve_elt (to_p x) (to_p y) Hoc)).
    unfold pequiv, a, pcurve_elt.
    apply n_equiv.
    unfold pkdiv, div, to_p.
    fold p_pos; set (pp := mkznz p (x mod p) (modz p x)).
    fold p_pos; set (p1 := mkznz p (1 mod p) (modz p 1)).
    pattern pp at 1; rewrite <- ((FZpZ _ Hp).(F_R).(Rmul_1_l) pp).
    unfold one; fold p_pos; fold p1.
    rewrite ((FZpZ _ Hp).(F_R).(Rmul_comm) p1).
    rewrite <- (FZpZ _ Hp).(F_R).(Rmul_assoc).
    rewrite ((FZpZ _ Hp).(F_R).(Rmul_comm) p1).
    rewrite (FZpZ _ Hp).(Finv_l); auto.
    rewrite (FZpZ _ Hp).(F_R).(Rmul_comm).
    rewrite (FZpZ _ Hp).(F_R).(Rmul_1_l); auto.
    apply (FZpZ _ Hp).(F_1_neq_0).
    unfold pkdiv, div, to_p.
    fold p_pos; set (pp := mkznz p (y mod p) (modz p y)).
    fold p_pos; set (p1 := mkznz p (1 mod p) (modz p 1)).
    pattern pp at 1; rewrite <- ((FZpZ _ Hp).(F_R).(Rmul_1_l) pp).
    unfold one; fold p_pos; fold p1.
    rewrite ((FZpZ _ Hp).(F_R).(Rmul_comm) p1).
    rewrite <- (FZpZ _ Hp).(F_R).(Rmul_assoc).
    rewrite ((FZpZ _ Hp).(F_R).(Rmul_comm) p1).
    rewrite (FZpZ _ Hp).(Finv_l); auto.
    rewrite (FZpZ _ Hp).(F_R).(Rmul_comm).
    rewrite (FZpZ _ Hp).(F_R).(Rmul_1_l); auto.
    apply (FZpZ _ Hp).(F_1_neq_0).
    assert(T1 := scal_correct N_lt_2 N_not_div_2 Rp Hp Hp1 _ _ E1 Ni3).
    rewrite Ha1 in T1; simpl fst in T1.
    match type of T1 with equiv _ ?X =>
      set (p1 := X); fold p1 in T1
    end.
    assert(T2 := scal_correct N_lt_2 N_not_div_2 Rp Hp Hp1 _ _ T1 Ni2).
    rewrite Ha2 in T2; simpl fst in T2.
    pose (ppG := pG A B N_not_div_2 Rp Hp Hp1).
    assert (F1: forall p1, List.In p1 (FGroup.s ppG)).
      intros p2.
      apply (FELLK_in pell _ (in_all_znz _ p_pos)).
    assert (F2 := fun u =>
        @scalL_not_1 N A B N_lt_2 N_not_div_2 Rp _ Hp Hp1 R1 sc2 _ _ u T2 Ni1).
    fold ppG in F2.
    assert (F3 :=
        @scalL_1 N A B N_lt_2 N_not_div_2 Rp _ Hp Hp1 R1 sc2 _ _ T2 Ni1).
    fold ppG in F3.
    rewrite <- psplit_correct in lR_big.
    rewrite HS1 in lR_big; simpl fst in lR_big; simpl snd in lR_big.
    assert (E2: e_order (ceqb pell) p1 ppG = (Zmullp lR)).
      apply order_div; auto.
      red; simpl; auto.
      intros z1 Hz1 Hz2.
        assert (E2: Zpos (z2p z1) = z1).
          generalize Hz1; case z1; simpl; auto; try (intros p2 HH || intro HH).
            case not_prime_0; auto.
          generalize (prime_ge_2 _ HH); unfold Z.le; simpl;
              intros HH1; case HH1; auto.
        rewrite <- psplit_correct.
        rewrite HS1; simpl fst; simpl snd.
        assert (Hl: List.In (z2p z1) R1).
          change R1 with (snd (S1, R1)).
          rewrite <- HS1.
          apply psplit_prime; auto.
          rewrite E2; auto.
          rewrite E2; auto.
       rewrite Zpos_mult_morphism.
       rewrite (Zmull_div (z2p z1)); auto.
       rewrite E2; rewrite Zmult_assoc.
       assert (Hpz1: z1 > 0).
         apply Z.lt_gt; apply Z.lt_le_trans with 2; try apply prime_ge_2; auto with zarith.
         red; auto.
       rewrite Z_div_mult; auto.
       rewrite gpow_gpow.
       rewrite <- E2; apply F2; auto.
       apply (FELLK_in pell _ (in_all_znz _ p_pos)); auto.
       red; simpl; intros HH; discriminate.
       apply Z_div_pos; auto with zarith.
       rewrite Hsc3 in F3; simpl fst in F3.
       rewrite <- psplit_correct.
       rewrite HS1; simpl fst; simpl snd.
       rewrite Zpos_mult_morphism; rewrite gpow_gpow; auto.
       set (p2 := gpow (gpow p1 ppG S1) ppG (Zmull R1)).
       fold p2 in F3; inversion F3; auto.
       red; simpl; intros; discriminate.
       red; simpl; intros; discriminate.
    absurd (e_order(ceqb pell) p1 ppG <= (FGroup.g_order ppG)).
      apply Zlt_not_le.
      apply Z.le_lt_trans with (1 := gorder_pG A B N_not_div_2 Rp Hp Hp1).
      rewrite E2.
      replace (Zpos (Zmullp lR)) with ((Zmullp lR - 1) + 1)%Z; try ring.
      apply Zplus_lt_compat_r.
      apply Zlt_square_simpl.
      change 0 with (1-1).
      unfold Zminus; apply Zplus_le_compat_r.
      case Zmullp; try intros p1; red; simpl; intros; discriminate.
      apply Z.le_lt_trans with (4 * N).
      replace (2 * p * (2 * p))%Z with (4 * (p * p))%Z. auto with zarith.
      ring.
      rewrite <- psplit_correct; rewrite HS1; simpl fst; simpl snd; auto.
      assert (tmp: forall x, x ^2 = x * x).
        intros x1; replace 2 with (1 + 1); auto; rewrite Zpower_exp.
        rewrite Zpower_1_r; auto.
        red; simpl; intros; discriminate.
        red; simpl; intros; discriminate.
      rewrite <- tmp; auto.
     apply Zdivide_le; auto.
     apply Zlt_le_weak.
     apply e_order_pos; auto.
     apply FGroup.g_order_pos.
     apply e_order_divide_g_order; auto.
Qed.

End pell.
