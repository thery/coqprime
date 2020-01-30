(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Import Arith_base.
Require Import Field_tac.
Require Import Ring.
Require Import Eqdep_dec.
Require Import FGroup.
Require Import List.
Require Import UList.
Require Import ZArith.

Set Implicit Arguments.

Section ELLIPTIC.

 (* Field elements *)
 Variable K:Set.
 Variable (kO kI : K) (kplus kmul ksub: K->K->K) (kopp : K->K) (kinv: K -> K)
                 (kdiv: K -> K -> K).
 Variable (A B: K).
 (* Test to zero *)
 Variable is_zero: K -> bool.

(* K notations *)
 Notation "x + y" := (kplus x y).  Notation "x * y " := (kmul x y).
 Notation "x - y " := (ksub x y). Notation "- x" := (kopp x).
 Notation "/ x" := (kinv x). Notation "x / y" := (kdiv x y).
 Notation "0" := kO.
 Notation "1" := kI.
 Notation "2" := (1+1).
 Notation "3" := (1+1 +1).


 (* Non singularity *)
 Notation "4" := (2 * 2).
 Notation "27" := (3 * 3 * 3).

 Record ell_theory: Prop := mk_ell_theory {

 (* field properties *)
    Kfth :  field_theory kO kI kplus kmul ksub kopp kdiv kinv (@eq K);
    NonSingular: 4 * A * A * A  + 27 * B * B <> 0;
 (* Characteristic greater than 2 *)
    one_not_zero: 1 <> 0;
    two_not_zero: 2 <> 0;
    is_zero_correct: forall k, is_zero k = true <-> k = 0
  }.


Variable Eth: ell_theory.

Fixpoint pow (k: K) (n: nat) :=
 match n with O => 1 | 1%nat => k | S n1 => k * pow k n1 end.

Notation "x ^ y" := (pow x y).

Theorem pow_S: forall k n, k ^ (S n) = k * k ^ n.
intros k n; simpl; auto; case n; auto.
simpl; rewrite Eth.(Kfth).(F_R).(Rmul_comm).
rewrite Eth.(Kfth).(F_R).(Rmul_1_l); auto.
Qed.

Let Mkmul := rmul_ext3_Proper (Eq_ext kplus kmul kopp).

Lemma Kpower_theory :
  power_theory 1 kmul (eq (A:=K)) BinNat.nat_of_N pow.
constructor.
intros r n; case n; simpl; auto.
intros p; elim p using BinPos.Pind; auto.
intros p1 H.
rewrite Pnat.nat_of_P_succ_morphism;
  rewrite pow_S.
rewrite (pow_pos_succ (Eqsth K) Mkmul); auto.
  rewrite H; auto.
exact Eth.(Kfth).(F_R).(Rmul_assoc).
Qed.

Ltac iskpow_coef t :=
  match t with
  | (S ?x) => iskpow_coef x
  | O => true
  | _ => false
  end.

Ltac kpow_tac t :=
 match iskpow_coef t with
 | true => constr:(BinNat.N_of_nat t)
 | _ => constr:(NotConstant)
 end.

Add Ring Rfth :  (F_R (Eth.(Kfth))) (power_tac Kpower_theory [kpow_tac]).
Add Field Kfth : Eth.(Kfth) (power_tac Kpower_theory [kpow_tac]).

Let Kdiv_def := (Fdiv_def Eth.(Kfth)).

Lemma Kinv_ext : forall p q, p = q -> / p = / q.
Proof.
intros p q H; rewrite H; auto.
Qed.

Let Ksth := (Eqsth K).
Let Keqe := (Eq_ext kplus kmul kopp).
Let AFth :=  Field_theory.F2AF Ksth Keqe Eth.(Kfth).
Let Kmorph := InitialRing.gen_phiZ_morph Ksth Keqe (F_R Eth.(Kfth)).

Hint Resolve one_not_zero two_not_zero : core.

Theorem Kdiv1: forall r, r /1 = r.
Proof.
intros r; field; auto.
Qed.

(* Some stuff for K *)

Notation  "x ?0" := (is_zero x) (at level 10).

Fixpoint n2k (n: nat) : K := match n with
  O => kO | (S O) => kI | (S n1) => (1 + n2k n1) end.

Coercion N2k := n2k.

Theorem Kdiff_2_0: (2:K) <> 0.
Proof.
simpl; auto.
Qed.
Hint Resolve Kdiff_2_0 : core.

Theorem Keq_minus_eq: forall x y, x - y = 0 -> x = y.
Proof.
intros x y H.
apply trans_equal with (y + (x - y)); try ring.
rewrite H; ring.
Qed.

Theorem Keq_minus_eq_inv: forall x y, x = y -> x - y = 0.
Proof.
intros x y HH; rewrite HH; ring.
Qed.

Theorem Kdiff_diff_minus_eq: forall x y, x <> y -> x - y <> 0.
Proof.
intros x y H H1; case H; apply Keq_minus_eq; auto.
Qed.

Hint Resolve Kdiff_diff_minus_eq : core.

Theorem Kmult_integral: forall x y, x * y = 0 -> x = 0 \/ y = 0.
Proof.
intros x y H.
generalize (Eth.(is_zero_correct) x); case (is_zero x); intros (H1, H2);
  auto; right.
apply trans_equal with ((/x) * (x * y)); try field.
  intros H3; assert (H4 := H2 H3); discriminate.
rewrite H; ring.
Qed.

Theorem Kmult_integral_contrapositive:
  forall x y, x <> 0 -> y <> 0 -> x * y <> 0.
Proof.
intros x y H H1 H2.
case (Kmult_integral H2); auto.
Qed.
Hint Resolve Kmult_integral_contrapositive : core.

Theorem Kmult_eq_compat_l: forall x y z, y = z -> x * y = x * z.
intros x y z H; rewrite H; auto.
Qed.

Theorem Keq_opp_is_zero: forall x, x = - x -> x = 0.
Proof.
intros x H.
case (@Kmult_integral (1+1:K) x); simpl; auto.
  apply trans_equal with (x + x); simpl; try ring.
  pattern x at 1; rewrite H; ring.
intros H1; case two_not_zero; auto.
Qed.

Theorem Kdiv_inv_eq_0:
  forall x y, x/y = 0 -> y<>0 -> x = 0.
Proof.
intros x y H1 H2.
apply trans_equal with (y * (x/y)); try field; auto.
rewrite H1; ring.
Qed.

Theorem is_zero_diff: forall x y, (x - y) ?0 = true -> x = y.
Proof.
intros x y H.
apply trans_equal with (y + (x - y)); try ring.
case (Eth.(is_zero_correct) (x - y)); intros H1 H2; rewrite H1;
  auto; ring.
Qed.

Theorem is_zero_diff_inv: forall x y, x = y -> (x - y) ?0 = true.
Proof.
intros x y H; rewrite H.
case (Eth.(is_zero_correct) (y - y)); intros H1 H2; apply H2; ring.
Qed.

Theorem Ksqr_eq: forall x y, x^2 = y^2 -> x = y \/ x = - y.
Proof.
intros x y H.
case (@Kmult_integral (x - y) (x + y)); auto.
  ring [H].
  intros H1; left; apply trans_equal with (y + (x - y));
     try ring.
  rewrite H1; ring.
intros H1; right; apply trans_equal with (-y + (x + y));
     try ring.
rewrite H1; ring.
Qed.

Theorem diff_rm_quo: forall x y, x/y <> 0 -> y<>0 -> x <> 0.
intros x y H H0 H1; case H; field [H1]; auto.
Qed.

Ltac dtac H :=
  match type of H with
    ?X <> 0 =>
       field_simplify X in H
  end; [
  match type of H with
    ?X/?Y <> 0 =>
       cut (X <> 0);
      [clear H; intros H | apply diff_rm_quo with Y; auto]
  end
  | auto].




(***********************************************************)
(*                                                         *)
(*      Definition of the elements of the curve            *)
(*                                                         *)
(***********************************************************)

Inductive elt: Set :=
  (* The infinity point *)
  inf_elt: elt
  (* A point of the curve *)
| curve_elt: forall x y,  y^2 = x^3 +  A * x + B -> elt.

Definition Kdec : forall a b: K, {a = b} + {a <> b}.
intros a b; case_eq ((a - b) ?0); intros H.
  left; apply is_zero_diff; auto.
right; intros H1.
rewrite (is_zero_diff_inv H1) in H; discriminate.
Defined.

Theorem curve_elt_irr: forall x1 x2 y1 y2 H1 H2,
 x1 = x2 -> y1 = y2 -> @curve_elt x1 y1 H1 = @curve_elt x2 y2 H2.
Proof.
intros x1 x2 y1 y2 H1 H2 H3 H4.
subst.
rewrite (fun H => eq_proofs_unicity H H1 H2); auto.
intros x y; case (Kdec x y); auto.
Qed.

Theorem curve_elt_irr1: forall x1 x2 y1 y2 H1 H2,
  x1 = x2 -> (x1 = x2 -> y1 = y2) -> @curve_elt x1 y1 H1 = @curve_elt x2 y2 H2.
Proof.
intros x1 x2 y1 y2 H1 H2 H3 H4.
apply curve_elt_irr; auto.
Qed.


Notation  "x ?= y" := (Kdec x y) (at level 70).

Definition ceqb: forall a b: elt, {a = b} + {a<>b}.
Proof.
intros a b; case a; case b; auto;
  try (intros; right; intros; discriminate).
intros x1 y1 H1 x2 y2 H2; case (Kdec x1 x2); intros H3.
  case (Kdec y1 y2); intros H4.
    left; apply curve_elt_irr1; auto.
  right; intros H; injection H; intros H5 H6; case H4; auto.
right; intros H; injection H; intros H4 H5; case H3; auto.
Defined.

Theorem is_zero_true: forall e, is_zero e = true -> e = 0.
intro e; generalize (Eth.(is_zero_correct) e); case is_zero; auto;
 intros (H,_); auto.
Qed.


Theorem is_zero_false: forall e, is_zero e = false -> e <> 0.
intro e; generalize (Eth.(is_zero_correct) e); case is_zero; auto;
 intros (_,H); auto.
  intros; discriminate.
intros _ H1; generalize (H H1); discriminate.
Qed.

Lemma opp_lem:
forall x y,
 y ^ 2 = x ^ 3 + A * x + B -> (- y) ^ 2  = x ^ 3 + A * x + B.
Proof.
intros x y H.
Time field [H].
Qed.

(***********************************************************)
(*                                                         *)
(*      Opposite function                                  *)
(*                                                         *)
(***********************************************************)

Definition opp: elt -> elt.
refine (fun p => match p with inf_elt =>
                   inf_elt
                | @curve_elt x y H => @curve_elt x (-y) _ end).
apply opp_lem; auto.
Defined.

Theorem opp_opp: forall p, opp (opp p) = p.
Proof.
intros p; case p; simpl; auto; intros; apply curve_elt_irr; ring.
Qed.


Theorem curve_elt_opp:
  forall x1 x2 y1 y2 H1 H2,
    x1 = x2 -> @curve_elt x1 y1 H1 = @curve_elt x2 y2 H2
           \/ @curve_elt x1 y1 H1 = opp (@curve_elt x2 y2 H2).
intros x1 x2 y1 y2 H1 H2 H3.
case (@Kmult_integral (y1 - y2) (y1 + y2));  try intros H4.
  ring_simplify.
  ring [H1 H2 H3].
left; apply curve_elt_irr; auto.
  apply Keq_minus_eq; auto.
right; unfold opp; apply curve_elt_irr; auto.
apply Keq_minus_eq; rewrite <- H4; ring.
Qed.

Lemma add_lem1: forall x1 y1,
 y1 <> 0 ->
 y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
 let l := (3 * x1 * x1 + A) / (2 * y1) in
 let x3 := l ^ 2 - 2 * x1  in
 (- y1 - l * (x3 - x1)) ^ 2 = x3 ^ 3 + A * x3 + B.
Proof.
intros x1 y1 H H1 l x3; unfold x3, l.
Time field [H1].
split; auto.
Qed.

Lemma add_lem2: forall x1 y1 x2 y2,
  x1 <> x2 ->
  y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
  y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
  let l := (y2 - y1) / (x2 - x1) in
  let x3 := l ^ 2 - x1 - x2 in
  (- y1 - l * (x3 - x1)) ^ 2 = x3 ^ 3 + A * x3 + B.
Proof.
intros x1 y1 x2 y2 H H1 H2 l x3; unfold x3, l.
Time field [H1 H2]; auto.
Qed.

Lemma add_zero: forall x1 x2 y1 y2,
 x1 = x2 ->
 y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
 y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
 y1 <> -y2 -> y1 = y2.
Proof.
intros x1 x2 y1 y2 H H1 H2 H3; subst x2.
case (@Kmult_integral (y1 - y2) (y1 + y2));
 try (intros H4; apply Keq_minus_eq; auto).
ring [H1 H2].
case H3; apply Keq_minus_eq; rewrite <- H4; ring.
Qed.

Lemma add_zero_diff: forall x1 x2 y1 y2,
 x1 = x2 ->
  y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
  y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
 y1 <> -y2 -> y1 <>0.
Proof.
intros x1 x2 y1 y2 H H1 H2 H3 H4.
assert (H5:= add_zero H H1 H2 H3).
case H3; rewrite <- H5; ring [H4].
Qed.

(***********************************************************)
(*                                                         *)
(*      Addition                                           *)
(*                                                         *)
(***********************************************************)

Definition add: elt -> elt -> elt.
refine (fun p1 p2 =>
             match p1 with
               inf_elt => p2
             | @curve_elt x1 y1 H1 =>
             match p2 with
               inf_elt => p1
             | @curve_elt x2 y2 H2 =>
                  if x1 ?= x2 then
                     (* we have p1 = p2 or p1 = - p2 *)
                     if (y1 ?= -y2) then
                       (* we do p - p *) inf_elt
                     else
                     (* we do the tangent *)
                      let l := (3*x1*x1 + A)/(2*y1) in
                      let x3 := l^2 - 2 * x1 in
                        @curve_elt x3 (-y1 - l * (x3 - x1)) _
                  else
                    (* general case *)
                    let l := (y2 - y1)/(x2 - x1) in
                      let x3 := l ^ 2 - x1 -x2 in
                        @curve_elt x3 (-y1 - l * (x3 - x1)) _
                end end).
apply (@add_lem1 x1 y1); auto.
apply (@add_zero_diff x1 x2 y1 y2); auto.
apply (@add_lem2 x1 y1 x2 y2); auto.
Defined.

(***********************************************************)
(*                                                         *)
(*      Direct case predicate for add                      *)
(*                                                         *)
(***********************************************************)

Ltac kauto := auto; match goal with
  H: ~ ?A, H1: ?A |- _ => case H; auto
end.

(* A little tactic to split kdec *)
Ltac ksplit :=
  let h := fresh "KD" in
  case Kdec; intros h; try (case h; kauto; fail).

Theorem add_case: forall P,
  (forall p, P inf_elt p p) ->
  (forall p, P p inf_elt p) ->
  (forall p, P p (opp p) inf_elt) ->
  (forall p1 x1 y1 H1 p2 x2 y2 H2 l,
      p1 = (@curve_elt x1 y1 H1) -> p2 = (@curve_elt x2 y2 H2) ->
      p2 = add p1 p1 -> y1<>0 ->
      l = (3 * x1 * x1 + A) / (2 * y1) ->
      x2 = l ^ 2 - 2 * x1 -> y2 = - y1 - l * (x2 - x1) ->
      P p1 p1 p2) ->
  (forall p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l,
      p1 = (@curve_elt x1 y1 H1) -> p2 = (@curve_elt x2 y2 H2) ->
      p3 = (@curve_elt x3 y3 H3) -> p3 = add p1 p2 ->
     x1 <> x2 ->
     l = (y2 - y1) / (x2 - x1) ->
     x3 = l ^ 2 - x1 - x2 -> y3 = -y1 - l * (x3 - x1) ->
     P p1 p2 p3)->
  forall p q, P p q (add p q).
Proof.
intros P H1 H2 H3 H4 H5 p q; case p; case q; auto.
intros x2 y2 e2 x1 y1 e1; unfold add.
repeat ksplit.
  replace (@curve_elt x2 y2 e2) with
          (opp (@curve_elt x1 y1 e1)); auto; simpl.
  apply curve_elt_irr; auto; ring [KD0].
assert (HH: y1 <> 0).
  apply (@add_zero_diff x1 x2 y1 y2); auto.
replace (@curve_elt x2 y2 e2) with
  (@curve_elt x1 y1 e1); auto.
eapply H4; eauto; simpl; repeat ksplit;
  try apply curve_elt_irr; auto.
  case HH; apply  Keq_opp_is_zero; auto.
apply curve_elt_irr; auto.
case (@Kmult_integral (y1 - y2) (y1 + y2)); try intros HH1.
  ring [e1 e2 KD].
apply Keq_minus_eq; auto.
case KD0; apply Keq_minus_eq; ring_simplify; auto.
eapply H5; eauto; simpl; repeat ksplit.
apply curve_elt_irr; auto.
Qed.

Theorem add_casew: forall P,
  (forall p, P inf_elt p p) ->
  (forall p, P p inf_elt p) ->
  (forall p, P p (opp p) inf_elt) ->
  (forall p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l,
      p1 = (@curve_elt x1 y1 H1) -> p2 = (@curve_elt x2 y2 H2) ->
      p3 = (@curve_elt x3 y3 H3) -> p3 = add p1 p2 -> p1 <> opp p2 ->
     ((x1 = x2 /\ y1 = y2 /\ l = (3 * x1 * x1 + A) / (2 * y1)) \/
      (x1 <> x2 /\ l = (y2 - y1) / (x2 - x1))
     ) ->
     x3 = l ^ 2 - x1 - x2 -> y3 = -y1 - l * (x3 - x1) ->
     P p1 p2 p3)->
  forall p q, P p q (add p q).
intros; apply add_case; auto.
intros; eapply X2; eauto.
rewrite H; simpl; intros tmp; case H4; injection tmp;
  apply Keq_opp_is_zero.
ring [H6].
intros; eapply X2; eauto.
rewrite H; rewrite H0; simpl; intros tmp; case H6;
  injection tmp; auto.
Qed.

Definition is_tangent p1 p2 :=
  p1 <> inf_elt /\ p1 = p2 /\ p1 <> opp p2.

Definition is_generic p1 p2 :=
  p1 <> inf_elt /\ p2 <> inf_elt /\
  p1 <> p2 /\ p1 <> opp p2.

Definition is_gotan p1 p2 :=
  p1 <> inf_elt /\ p2 <> inf_elt /\  p1 <> opp p2.

Ltac kcase X Y :=
pattern X, Y, (add X Y); apply add_case; auto;
  clear X Y.

Ltac kcasew X Y :=
pattern X, Y, (add X Y); apply add_casew; auto;
  clear X Y.


(***********************************************************)
(*                                                         *)
(*      Generic case for associativity                     *)
(*       (A + B) + C = A + (B + C)                         *)
(*                                                         *)
(***********************************************************)

Theorem spec1_assoc:
  forall p1 p2 p3,
   is_generic p1 p2 ->
   is_generic p2 p3 ->
   is_generic (add p1 p2) p3 ->
   is_generic  p1 (add p2 p3) ->
   add p1 (add p2 p3) = add (add p1 p2) p3.
intros p1 p2; kcase p1 p2.
intros p p3  _ _ (HH, _); case HH; auto.
intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ p5 (_, (_, (HH, _)));
  case HH; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 p4 x4 y4 H4 l
       Hp Hp2 Hp4 Hp4b Hx Hl Hx4 Hy4 p3.
generalize Hp2 Hp4b; clear Hp2 Hp4b; kcase p2 p3.
intros; discriminate.
intros p _ _ _ (_,(HH, _)); case HH; auto.
intros p _ _ _ (_,(_,(_,HH)));  case HH; rewrite opp_opp; auto.
intros p2 _ _ _ p3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (_, (HH, _)));
  case HH; auto.
intros p2 x2b y2b H2b p3 x3 y3 H3 p5 x5 y5 H5 l1.
intros Hp2; pattern p2 at 2; rewrite Hp2; clear Hp2.
intros Hp3 Hp5 Hp5b Hd Hl1 Hx5 Hy5 tmp.
injection tmp; intros; subst y2b x2b; clear tmp H2b.
generalize Hp Hp5 Hp5b Hp4b H6 H9;
  clear Hp Hp5 Hp5b Hp4b H6 H9.
kcase p1 p5.
  intros; discriminate.
  intros; discriminate.
intros p _ _ _ _ _ (_,(_,(_,HH))); case HH; rewrite opp_opp;
  auto.
intros p1 _ _ _ p5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_,(_,(HH,_)));
  case HH; auto.
intros p1 x1b y1b H1b.
intros p5b x5b y5b H5b p6 x6 y6 H6 l2.
intros Hp1; pattern p1 at 2; rewrite Hp1; clear Hp1.
intros Hp5; pattern p5b at 2; rewrite Hp5; clear Hp5.
intros Hp6 _ Hd2 Hl2 Hx6 Hy6.
intros tmp; injection tmp; intros HH1 HH2; subst y1b x1b;
  clear tmp H1b.
intros tmp; injection tmp; intros HH1 HH2; subst y5b x5b;
  clear tmp H5b.
intros _ Hp4b _ _.
generalize Hp3 Hp4 Hp4b H7 H8; clear Hp3 Hp4 Hp4b H7 H8.
kcase p4 p3.
  intros; discriminate.
  intros; discriminate.
intros p _ _ _ _ (_, (_, (_,HH))); case HH; rewrite opp_opp;
  auto.
intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_,(_,(HH, _)));
  case HH; auto.
intros p4b x4b y4b H4b p3b x3b y3b H3b p7 x7 y7 H7
       l3.
intros Hp4b; pattern p4b at 2; rewrite Hp4b; clear Hp4b.
intros Hp3b; pattern p3b at 2; rewrite Hp3b; clear Hp3b.
intros Hp7 _ Hd3 Hl3 Hx7 Hy7.
intros tmp; injection tmp; intros HH1 HH2; subst y3b x3b;
  clear tmp H3b.
intros tmp; injection tmp; intros HH1 HH2; subst y4b x4b;
  clear tmp H4b.
intros _ _ _.
subst p6 p7; apply curve_elt_irr; clear H6 H7;
  apply Keq_minus_eq; clear H4 H5; subst.
Time field [H1 H2 H3]; auto; repeat split; auto.
intros VV; field_simplify_eq[H1 H2] in VV.
case Hd3; symmetry; apply Keq_minus_eq;
  field_simplify_eq [H1 H2]; auto.
intros VV; field_simplify_eq[H1 H2] in VV.
case Hd2; symmetry; apply Keq_minus_eq;
  field_simplify_eq [H1 H2]; auto.
Time field [H1 H2 H3]; auto; repeat split; auto.
intros VV; field_simplify_eq[H1 H2] in VV.
case Hd3; symmetry; apply Keq_minus_eq;
  field_simplify_eq [H1 H2]; auto.
intros VV; field_simplify_eq[H1 H2] in VV.
case Hd2; symmetry; apply Keq_minus_eq;
  field_simplify_eq [H1 H2]; auto.
Qed.


(***********************************************************)
(*                                                         *)
(*      Tangent case for associativity                     *)
(*       A + (B + B) = (A + B) + B                         *)
(*                                                         *)
(***********************************************************)

Theorem spec2_assoc:
  forall p1 p2 p3,
   is_generic p1 p2 ->
   is_tangent p2 p3 ->
   is_generic (add p1 p2) p3 ->
   is_generic  p1 (add p2 p3) ->
   add p1 (add p2 p3) = add (add p1 p2) p3.
intros p1 p2; kcase p1 p2.
intros p p3  _ _ (HH, _); case HH; auto.
intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ p5 (_, (_, (HH, _)));
  case HH; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 p4 x4 y4 H4 l
       Hp Hp2 Hp4 Hp4b Hx Hl Hx4 Hy4 p3.
generalize Hp2 Hp4b; clear Hp2 Hp4b.
kcase p2 p3.
intros; discriminate.
intros p _ _ _ _ (_, (HH, _)); case HH; auto.
intros p _ _ _ _ _ (_, (HH, _)); case HH; auto.
intros p2 x2b y2b H2b p5 x5 y5 H5 l1.
intros Hp2b.
intros Hp5 Hp5b Hd Hl1 Hx5 Hy5 Hp2.
rewrite Hp2 in Hp2b.
injection Hp2b; intros HH HH1; subst y2b x2b; clear Hp2b.
generalize Hp Hp5 Hp5b; clear Hp Hp5 Hp5b.
kcase p1 p5.
  intros; discriminate.
  intros; discriminate.
intros p _ _ _ _ _ _ _ (_,(_,(_,HH)));
   case HH; rewrite opp_opp; auto.
intros p1 _ _ _ p5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_,(_,(HH,_)));
  case HH; auto.
intros p1 x1b y1b H1b.
intros p5b x5b y5b H5b p6 x6 y6 H6 l2.
intros Hp1; pattern p1 at 2; rewrite Hp1; clear Hp1.
intros Hp5; pattern p5b at 2; rewrite Hp5; clear Hp5.
intros Hp6 _ Hd2 Hl2 Hx6 Hy6.
intros tmp; injection tmp; intros HH1 HH2; subst y1b x1b;
  clear tmp H1b.
intros tmp; injection tmp; intros HH1 HH2; subst y5b x5b;
  clear tmp H5b.
intros _ Hp4b _ _.
generalize Hp2 Hp4 Hp4b; clear Hp2 Hp4 Hp4b.
kcase p4 p2.
  intros; discriminate.
  intros; discriminate.
intros p _ _ _ (_, (_, (_,HH))); case HH; rewrite opp_opp;
  auto.
intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_,(_,(HH, _)));
  case HH; auto.
intros p4b x4b y4b H4b p3b x3b y3b H3b p7 x7 y7 H7
       l3.
intros Hp4b; pattern p4b at 2; rewrite Hp4b; clear Hp4b.
intros Hp3b; pattern p3b at 2; rewrite Hp3b; clear Hp3b.
intros Hp7 _ Hd3 Hl3 Hx7 Hy7.
intros tmp; injection tmp; intros HH1 HH2; subst y3b x3b;
  clear tmp H3b.
intros tmp; injection tmp; intros HH1 HH2; subst y4b x4b;
  clear tmp H4b.
intros _ _ _.
subst p6 p7; apply curve_elt_irr; clear H6 H7 H2b;
  apply Keq_minus_eq; clear H4 H5; subst.
Time field [H1 H2]; auto; repeat split; auto.
intros VV; field_simplify_eq[H1 H2] in VV.
case Hd3; symmetry; apply Keq_minus_eq;
  field_simplify_eq [H1 H2]; auto.
intros VV; field_simplify_eq[H1 H2] in VV.
case Hd2; symmetry; apply Keq_minus_eq;
  field_simplify_eq [H1 H2]; auto.
Time field [H1 H2]; auto; repeat split; auto.
intros VV; field_simplify_eq[H1 H2] in VV.
case Hd3; symmetry; apply Keq_minus_eq;
  field_simplify_eq [H1 H2]; auto.
intros VV; field_simplify_eq[H1 H2] in VV.
case Hd2; symmetry; apply Keq_minus_eq;
  field_simplify_eq [H1 H2]; auto.
intros p3 x3 y3 H3 p5 x5 y5 H5 p6 x6 y6 H6 l1
  Hp3 Hp5 _ _ Hd  _ _ _ _ _ _.
rewrite Hp3; rewrite Hp5; intros (_, (HH,_));
 case Hd; injection HH; auto.
Time Qed.


(***********************************************************)
(*                                                         *)
(*      Identity case for associativity                    *)
(*       (A + A) + (A + A) = A + (A + (A + A))             *)
(*                                                         *)
(***********************************************************)


Theorem spec3_assoc:
  forall p1 p2 p3,
   is_generic p1 p2 ->
   is_tangent p2 p3 ->
   is_generic (add p1 p2) p3 ->
   is_tangent  p1 (add p2 p3) ->
   add p1 (add p2 p3) = add (add p1 p2) p3.
intros p1 p2.
kcase p1 p2.
intros p p3  _ _ (HH, _); case HH; auto.
intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ p5 (_, (_, (HH, _)));
  case HH; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 p4 x4 y4 H4 l
       Hp Hp2 Hp4 Hp4b Hx Hl Hx4 Hy4 p3.
generalize Hp2 Hp4b; clear Hp2 Hp4b.
kcase p2 p3.
intros; discriminate.
intros p _ _ _ _ (_, (HH, _)); case HH; auto.
intros p _ _ _ (_ ,(_ , HH)); case HH; rewrite opp_opp; auto.
intros p2 x2b y2b H2b p5 x5 y5 H5 l1.
intros Hp2b.
intros Hp5 Hp5b Hd Hl1 Hx5 Hy5 Hp2.
rewrite Hp2 in Hp2b.
injection Hp2b; intros HH HH1; subst y2b x2b; clear Hp2b H2b.
generalize Hp Hp5 Hp5b; clear Hp Hp5 Hp5b.
kcase p1 p5.
  intros; discriminate.
  intros; discriminate.
intros p _ _ _ _ _ _ _ (_, (_,HH)); case HH; rewrite opp_opp;
  auto.
intros p1 x1b y1b H1b.
intros p6 x6 y6 H6 l2.
intros Hp1; pattern p1 at 3 4; rewrite Hp1; clear Hp1.
intros Hp6 _ Hd2 Hl2 Hx6 Hy6.
intros tmp; injection tmp; intros HH1 HH2; subst y1b x1b;
  clear tmp.
intros tmp; injection tmp; intros HH1 HH2.
subst y5 x5; clear tmp H5.
rename HH1 into Hy1; rename HH2 into Hx1.
generalize Hp2 Hp4; clear Hp2 Hp4.
kcase p4 p2.
  intros; discriminate.
  intros; discriminate.
intros p _ _ _ _ _ _ (_, (_, (_, HH))); case HH; rewrite opp_opp;
  auto.
intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (_,(_,(HH, _))); case HH; auto.
intros p4b x4b y4b H4b p2b x2b y2b H2b.
intros p7 x7 y7 H7 l3.
intros Hp4b; pattern p4b at 2; rewrite Hp4b; clear Hp4b.
intros Hp2b; pattern p2b at 2; rewrite Hp2b; clear Hp2b.
intros Hp7 _ Hd1 Hl3 Hx7 Hy7.
intros tmp; injection tmp; intros HH1 HH2; subst y2b x2b;
  clear tmp H2b.
intros tmp; injection tmp; intros HH1 HH2; subst y4b x4b;
  clear tmp H4b.
intros _ _ _ _ _ _.
subst p6 p7; apply curve_elt_irr; clear H6 H7;
  apply Keq_minus_eq; clear H4 H1b; subst.
Time field [H2]; auto; repeat split; auto;
  intros HH; field_simplify_eq in HH; auto.
case Hx; symmetry; apply Keq_minus_eq.
  field_simplify_eq; auto.
case Hd1; symmetry; apply Keq_minus_eq;
  field_simplify_eq; repeat split; auto.
intros HH1; ring_simplify in HH1; auto.
case Hx; symmetry; apply Keq_minus_eq.
  field_simplify_eq; auto.
case Hd2; apply Keq_minus_eq;
  field_simplify_eq; auto.
Time field [H2]; auto; repeat split; auto;
  intros HH; field_simplify_eq in HH; auto.
case Hx; symmetry; apply Keq_minus_eq.
  field_simplify_eq; auto.
case Hd1; symmetry; apply Keq_minus_eq;
  field_simplify_eq; repeat split; auto.
intros HH1; ring_simplify in HH1; auto.
case Hx; symmetry; apply Keq_minus_eq.
  field_simplify_eq; auto.
case Hd2; apply Keq_minus_eq;
  field_simplify_eq; auto.
intros p1b x1b y1b H1b.
intros p5b x5b y5b H5b.
intros p3 x3 y3 H3 l2.
intros Hp1b; pattern p1b at 2 5; rewrite Hp1b; clear Hp1b.
intros Hp5b; pattern p5b at 2 4; rewrite Hp5b; clear Hp5b.
intros Hp3 _; rewrite Hp3; clear Hp3.
intros Hx1 _ _ _.
intros tmp; injection tmp; intros HH1 HH2; subst y1b x1b;
  clear tmp.
intros tmp; injection tmp; intros HH1 HH2; subst y5b x5b;
  clear tmp.
intros _ _ _ _ _ (_,(HH, _)); case Hx1; injection HH;
 auto.
intros p2b x2b y2b H2b.
intros p3 x3 y3 H3.
intros p5 x5 y5 H5 l2.
intros Hp2b; pattern p2b at 2 5; rewrite Hp2b; clear Hp2b.
intros Hp3; rewrite Hp3; clear Hp3.
intros _ _ Hx1 _ _ _.
intros tmp; injection tmp; intros HH1 HH2; subst y2b x2b;
  clear tmp.
intros _ _ (_,(HH, _)); case Hx1; injection HH; auto.
Time Qed.

(***********************************************************)
(*                                                         *)
(*      inf_elt is the zero                                *)
(*                                                         *)
(***********************************************************)

Theorem add_0_l: forall p, add inf_elt p = p.
Proof.
auto.
Qed.

Theorem add_0_r: forall p, add p inf_elt = p.
Proof.
intros p; case p; auto.
Qed.


(***********************************************************)
(*                                                         *)
(*      opp is the opposite                                *)
(*                                                         *)
(***********************************************************)

Theorem add_opp: forall p, add p (opp p) = inf_elt.
Proof.
intros p; case p; unfold add; simpl; auto.
intros x1 y1 H1.
repeat ksplit.
case KD0; ring.
Qed.


(***********************************************************)
(*                                                         *)
(*      Addition is commutative                            *)
(*                                                         *)
(***********************************************************)

Theorem add_comm: forall p1 p2, add p1 p2 = add p2 p1.
Proof.
intros p1 p2; case p1.
  rewrite add_0_r; rewrite add_0_l; auto.
intros x1 y1 H1; case p2.
  rewrite add_0_r; rewrite add_0_l; auto.
intros x2 y2 H2; simpl; repeat ksplit.
  case KD2; ring [KD0].
  case KD0; ring [KD2].
  assert (H3 := add_zero KD H1 H2 KD0).
  apply curve_elt_irr; subst x2 y2; auto.
  case KD; auto.
  case KD; auto.
apply curve_elt_irr; field; auto.
Qed.

Theorem aux1: forall x1 y1 x2 y2,
y1 ^ 2 = x1 ^ 3 + A * x1 + B -> y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
x1 <> x2 ->  y2 = 0 -> ((y2 - y1) / (x2 - x1))^2 - x1 - x2 = x2 -> False.
Proof.
intros x1 y1 x2 y2 H H1 H2 H3 H4.
subst y2.
assert (Hu : x2 ^ 3 = -(A * x2 + B)).
 apply trans_equal with
   ((x2 ^ 3 + A * x2 + B) - (A * x2 + B)); try ring.
 rewrite <- H1; ring.
assert (H5:= (Keq_minus_eq_inv H4)); clear H4.
field_simplify_eq [H Hu] in H5; auto.
generalize (Kmult_eq_compat_l x2 H5); rename H5 into H4.
replace (x2 * 0) with 0; try ring; intros H5.
field_simplify_eq [Hu] in H5.
generalize H5; clear H5.
match goal with |- (?X = _ -> _) => replace X with ((x2 - x1) * (2* A *x2 + 3* B));
try ring end.
intros tmp; case (Kmult_integral tmp); clear tmp; intros HH2.
  case H2; apply sym_equal; apply Keq_minus_eq; auto.
generalize (Kmult_eq_compat_l ((2 * A )^3) (sym_equal H1)).
replace ((2 * A)^3 * 0 ^ 2) with 0; try (ring).
intros H5; ring_simplify in H5; auto.
match type of H5 with  (?X + ?Y + _ = _) =>
  let x := (constr:(2 * A * x2)) in
     ((replace Y with (x ^ 3) in H5; try ring);
     (replace X with (4 * A^3 * x) in H5; try ring);
      replace x with (-(3) * B) in H5) end.
2: apply sym_equal; apply Keq_minus_eq; apply trans_equal with (2:= HH2); ring.
ring_simplify in H5; auto.
match type of Eth.(NonSingular) with ?X <> 0 =>
 case (@Kmult_integral (-B) X); try intros HH3;
 try (case NonSingular; auto; fail) end.
  rewrite <- H5; ring.
assert (HH3b : B = 0).
  replace B with (-(-B)); try ring; rewrite HH3; ring.
case (@Kmult_integral 2 (A * x2)); try intros HH4; auto.
  apply trans_equal with (2:= HH2).
  rewrite HH3b; ring.
case (Kmult_integral HH4); try intros HH5; auto.
case Eth.(NonSingular); rewrite HH3b; rewrite HH5; simpl; ring.
ring_simplify [HH5] in H4; auto.
case (@Kmult_integral A  x1); try intros HH6; auto.
  apply trans_equal with (2 := H4); rewrite HH3b; ring.
  case Eth.(NonSingular); rewrite HH3b; rewrite HH6; ring.
case H2; rewrite HH6; auto.
Qed.


(***********************************************************)
(*                                                         *)
(*      There is only one zero                             *)
(*                                                         *)
(***********************************************************)

Theorem uniq_zero: forall p1 p2, add p1 p2 = p2 -> p1 = inf_elt.
Proof.
intros p1 p2; kcase p1 p2.
intros p; case p; simpl; auto; intros; discriminate.
intros.
subst p1 p2; injection H8; intros H9 H10.
generalize (Keq_minus_eq_inv H7); clear H7; intros H7.
ring_simplify [H9 H10] in H7.
case (Kmult_integral H7); auto; intros H11.
case Kdiff_2_0; auto.
case H4; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hp3b Hd Hl Hx3 Hy3 Hp.
apply False_ind.
subst p2; subst p3; injection Hp; clear p1 Hp1 Hp Hp3b; intros.
case (@aux1 x1 y1 x2 y2); auto.
generalize (Keq_minus_eq_inv Hy3); rewrite Hl;
  rewrite H; rewrite H0; clear Hy3; intros Hy3.
field_simplify_eq in Hy3; auto.
assert (HH: 2 * y2 * (x2 - x1) = 0).
  rewrite Hy3; ring.
clear Hy3; rename HH into Hy3.
case (Kmult_integral Hy3); auto; clear Hy3; intros Hy3.
case (Kmult_integral Hy3); auto; clear Hy3; intros Hy3.
case Kdiff_2_0; auto.
case Hd.
symmetry; apply Keq_minus_eq; auto.
rewrite <- Hl; rewrite <- Hx3; auto.
Qed.


(***********************************************************)
(*                                                         *)
(*      There is only one opposite                         *)
(*                                                         *)
(***********************************************************)

Theorem uniq_opp: forall p1 p2, add p1 p2 = inf_elt -> p2 = opp p1.
Proof.
intros p1 p2; kcase p1 p2.
intros p H; rewrite H; auto.
intros; subst; discriminate.
intros; subst; discriminate.
Qed.


(***********************************************************)
(*                                                         *)
(*      Opposite of zero is zero                           *)
(*                                                         *)
(***********************************************************)

Theorem opp_0: opp (inf_elt) = inf_elt.
Proof.
auto.
Qed.


(***********************************************************)
(*                                                         *)
(*      Opposite of a sum is the sum of opposite           *)
(*                                                         *)
(***********************************************************)

Theorem opp_add: forall p1 p2, opp (add p1 p2) = add (opp p1) (opp p2).
Proof.
intros p1 p2; case p1.
rewrite opp_0; repeat rewrite add_0_l; auto.
intros x1 y1 H1; case p2.
rewrite opp_0; repeat rewrite add_0_r; auto.
intros x2 y2 H2; simpl; repeat ksplit; simpl.
case KD1; ring [KD0].
case KD0; apply trans_equal with (-(-y1));
  try ring; rewrite KD1; ring.
assert (HH:= add_zero_diff KD H1 H2 KD0).
apply curve_elt_irr; try field; repeat split; auto;
 intros HH1; case HH; symmetry; apply Keq_minus_eq;
 ring_simplify; auto.
apply curve_elt_irr; try field; auto.
Qed.

Theorem compat_add_opp: forall p1 p2,
add p1 p2 = add p1 (opp p2) ->  ~ p1 = opp p1 -> p2 = opp p2.
Proof.
intros p1 p2; kcase p1 p2.
intros p H H1; case H1.
apply uniq_opp.
pattern p at 2; rewrite <- opp_opp; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 l Hp1 Hp2 Hp2b Hy Hl Hx2 Hy2 He1 He2.
apply uniq_opp.
rewrite <- Hp2b; rewrite He1; rewrite add_opp; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hp3b Hx12
       Hl Hx3 Hy3 Hp3bb Hd.
generalize Hp3bb; clear Hp3bb.
subst p1 p2 p3; simpl; repeat ksplit.
intros tmp; injection tmp; clear tmp.
rewrite Hx3; rewrite Hl; intros _ HH.
assert (HH1:= (Keq_minus_eq_inv HH)).
field_simplify_eq in HH1; auto.
case (Kmult_integral HH1); try intros HH2; auto.
case (Kmult_integral HH2); try intros HH3; auto.
assert (HH8: 2 * 2 = 0).
  replace (2*2) with (-(-(2 * 2))); try ring
     ; try rewrite HH3; ring.
case (Kmult_integral HH8); try intro H9;
       case Kdiff_2_0; auto.
intros; apply curve_elt_irr; try rewrite HH3;
    intros; ring.
case Hd; simpl; apply curve_elt_irr; ring[HH2].
Qed.

Theorem compat_add_triple: forall p,
 p <> opp p -> add p p <> opp p -> add (add p p) (opp p) = p.
Proof.
intro p.
set (p1 := (add p p)).
set (p2 := opp p).
cut (p1 = add p p); auto.
cut (p2 = opp p); auto.
kcase p1 p2.
intros p1 Hp1; subst p1.
intros; symmetry; apply uniq_opp; auto.
intros p1 H1 _ H2 _; case H2.
rewrite <- (opp_opp p); rewrite <- H1; auto.
intros p1 H1 H2 H3 H4.
assert (H5: p = p1).
  rewrite <- (opp_opp p); rewrite <- H1; rewrite opp_opp; auto.
subst p1.
symmetry; apply uniq_zero with p; auto.
intros; case H11; auto.
case p; clear p.
  intros; subst p2; discriminate.
intros x y H.
set (p := (@curve_elt x y H)).
intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hp3b
       Hx12 Hl Hx3 Hy3 He1 He2 He3 He4.
generalize He1; unfold p; rewrite Hp2;
  simpl; intros tmp; injection tmp; clear tmp.
intros; subst x2 y2.
rewrite Hp3.
case (curve_elt_opp H3 H); auto.
rewrite Hx3; rewrite Hl.
generalize He2; unfold p; simpl; repeat ksplit.
  rewrite Hp1; intros; discriminate.
rewrite Hp1; intros tmp; injection tmp; intros; subst x1 y1.
set (l1 := (3 * x * x + A) / (2 * y)).
field; repeat split; auto.
rewrite <- Hp3; fold p; intros HH.
absurd (p1 = inf_elt).
  rewrite Hp1; intros; discriminate.
apply uniq_zero with p2.
rewrite <- Hp3b; rewrite He1; auto.
Qed.

Theorem add_opp_double_opp: forall p1 p2,
  add p1 p2 = opp p1 -> p2 = add (opp p1) (opp p1).
intros p1 p2; intros H1.
case (ceqb p1 (opp p1)); intros H2.
pattern (opp p1) at 1; rewrite <- H2.
rewrite add_opp; apply uniq_zero with p1.
rewrite add_comm; rewrite H1; auto.
rewrite <-opp_add.
assert (H: (p2 = add (opp p1) (opp p1)) \/ (p2 = opp (add (opp p1) (opp p1)))).
rewrite <- opp_add; rewrite opp_opp.
generalize H1 H2; clear H1 H2; kcase p1 p2.
intros p H2 H1; case H1; auto.
intros p H2 H1; rewrite opp_add; rewrite <- H2; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 l Hp1 Hp2 Hp2b Hy1 _ _ _ He1 He2.
rewrite <- Hp2b; rewrite He1; rewrite opp_opp; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hp3b
       Hx12 Hl Hx3 Hy3 He1 He2.
assert (Hy1: y1 <> 0).
  intros HH; case He2; rewrite Hp1; simpl; apply curve_elt_irr;
  ring[HH].
assert (Hy2: -y1 <> 0).
  intros Hy2; case Hy1; apply trans_equal with (-(-y1));
    try ring; rewrite Hy2; ring.
generalize He1; clear He1.
rewrite Hp1; rewrite Hp2; rewrite Hp3; simpl; repeat ksplit.
case Hy1; apply Keq_opp_is_zero; auto.
intros tmp; injection tmp; intros; subst x3 y3; clear tmp Hp1 Hp2 Hp3.
assert (tmp: forall P Q, P \/ Q -> Q \/ P).
  intuition.
apply tmp; apply curve_elt_opp; clear tmp.
rewrite Hl in H0.
assert (HH1:= (Keq_minus_eq_inv H0)); clear H0.
field_simplify_eq [H1 H2] in HH1; auto.
match type of HH1 with ?XX = 0 =>
 assert (HH2: 2 * y2 * y1 = XX + 2 * y2 * y1);
 try (rewrite HH1; ring); clear HH1; rename HH2 into HH1;
 ring_simplify in HH1
end.
match type of HH1 with _ = ?X =>
  assert (HH2: 4 * y2^2 * y1^2 = X * X);
   [rewrite <- HH1;ring | clear HH1; rename HH2 into HH1]
end.
assert (HH2:= Keq_minus_eq_inv HH1); clear HH1;
  rename HH2 into HH1.
ring_simplify [H1 H2] in HH1.
assert (HH2:
(x2 - (((3 * x1* x1  + A)/(2*-y1))^2 -2 * x1)) * (x2 -x1)^2 = 0).
  field_simplify_eq [H1]; auto.
  apply trans_equal with (2 := HH1); ring.
clear HH1; rename HH2 into HH1.
case (Kmult_integral HH1); intros HH2.
apply Keq_minus_eq; auto.
rewrite <- HH2; field; auto; split; auto.
simpl in HH2; auto.
case (Kmult_integral HH2); intros; case Hx12;
  symmetry; apply Keq_minus_eq; auto.
case H; auto; intros H3.
  rewrite <- opp_add in H3; auto.
rewrite opp_add in H3; rewrite opp_opp in H3.
case (ceqb (add p1 p1) (opp p1)); intros H4.
  rewrite H3; rewrite H4.
  rewrite <- H1; rewrite H3; rewrite H4.
  rewrite add_opp; auto.
rewrite <- H3.
apply compat_add_opp with p1; auto.
apply trans_equal with (opp(add (add p1 p1) (opp p1))).
  rewrite compat_add_triple; auto.
rewrite <- H3; rewrite opp_add; rewrite opp_opp.
apply add_comm.
Qed.


(***********************************************************)
(*                                                         *)
(*      Cancellation rule                                  *)
(*                                                         *)
(***********************************************************)

Theorem cancel:
  forall p1 p2 p3, add p1 p2 = add p1 p3 -> p2 = p3.
intros p1 p2; pattern p1, p2, (add p1 p2);
 apply add_casew; clear p1 p2.
intros; subst; auto.
intros p p1 H; symmetry; apply uniq_zero with p.
rewrite add_comm; auto.
intros; symmetry; apply uniq_opp; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 p4 x4 y4 H4 l
       Hp1 Hp2 Hp4 Hp4b Hd1 Hl1 Hx4 Hy4 p3.
generalize Hp1 Hp4b Hd1; clear Hp1 Hp4b Hd1.
rewrite Hp4; clear Hp4.
pattern p1, p3, (add p1 p3);
 apply add_casew; clear p1 p3.
intros; discriminate.
intros p He1 He2 _ He3.
apply uniq_zero with p.
rewrite add_comm; rewrite <- He2; auto.
intros; discriminate.
intros p1 x1b y1b H1b p3 x3 y3 H3 p5 x5 y5 H5 l'.
intros Hp1b Hp3 Hp5 Hp5b Hd1 Hl' Hx5 Hy5 He1 He2 Hd2 He3.
rewrite He3 in He2; rewrite Hp5b in He2.
rewrite He1 in Hp1b; injection Hp1b; clear Hp1b.
intros; subst x1b y1b.
generalize He3; rewrite Hp5.
intros tmp; injection tmp; intros HH HH1; clear tmp.
rewrite Hp5b in He3.
generalize Hy5; clear Hy5.
rewrite <- HH; rewrite <- HH1; rewrite Hy4; clear HH Hy4.
intros HH2; generalize (Keq_minus_eq_inv HH2); clear HH2.
intros HH2; ring_simplify in HH2.
case (@Kmult_integral (l' - l) (x4 - x1));
  try (clear HH2; intros HH2).
rewrite <- HH2; ring.
generalize HH1; subst x4 x5; clear HH1.
rewrite (Keq_minus_eq HH2).
intros HH; generalize (Keq_minus_eq_inv HH);
  clear HH; intros HH; ring_simplify in HH.
case (curve_elt_opp H2 H3).
symmetry; apply Keq_minus_eq; rewrite <- HH; ring.
subst p2 p3; auto.
rewrite <- Hp2; rewrite <- Hp3; intros HH1.
case (ceqb p1 (opp p1)); intros HH3.
case Hl1; clear Hl1.
intros (Hx1, (Hy1, _)).
case Hd1; rewrite <- HH1; rewrite He1; rewrite Hp2;
  apply curve_elt_irr; auto; clear Hd1.
intros (Hdx1, Hl2); rewrite Hl2 in HH2; clear Hl2.
case Hl'; clear Hl'.
intros (Hx1, (Hy1, _)).
case Hd2; rewrite HH1; rewrite opp_opp.
rewrite He1; rewrite Hp3;
  apply curve_elt_irr; auto; clear Hd1.
intros (Hdx3, Hl2); rewrite Hl2 in HH2; clear Hl2.
generalize HH1; rewrite Hp2; rewrite Hp3; simpl; clear HH1.
intros tmp; injection tmp.
intros; apply curve_elt_irr; auto.
subst x3 y2.
field_simplify_eq in HH2; auto.
case (Kmult_integral HH2); try intros HHx; auto.
case Kdiff_2_0; auto.
ring [HHx].
rewrite <- (opp_opp p3); rewrite <- HH1.
apply compat_add_opp with p1; auto.
pattern p2 at 2; rewrite HH1; rewrite opp_opp; auto.
case (curve_elt_opp H4 H1);
  try apply Keq_minus_eq; auto; rewrite He3; rewrite <- He1;
  intros HH3.
apply trans_equal with inf_elt; [idtac | symmetry];
  apply uniq_zero with p1; rewrite add_comm; auto.
  rewrite <- He2; auto.
apply trans_equal with (add (opp p1) (opp p1));
  [idtac | symmetry]; apply add_opp_double_opp; auto.
rewrite <- He2; auto.
Qed.

Theorem add_minus_id: forall p1 p2, (add (add p1 p2) (opp p2)) = p1.
intros p1 p2.
case (ceqb (add p1 p2) (opp p2)).
  intros Hp12; rewrite Hp12; symmetry;
  apply add_opp_double_opp; rewrite add_comm; auto.
pattern p1, p2, (add p1 p2); apply add_case; clear p1 p2.
intros; rewrite add_opp; auto.
intros; rewrite add_0_r; auto.
intros; rewrite opp_opp; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 l Hp1 Hp2 Hp3 Hd
       Hl Hx2 Hy2 Hp12.
rewrite Hp3.
apply compat_add_triple; auto.
rewrite Hp1; simpl; intros tmp; case Hd;
    injection tmp; intros; apply Keq_opp_is_zero; auto.
rewrite <- Hp3; auto.
intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1
       Hp2 Hp3 Hp3b Hx1 Hl Hx3 Hy3.
generalize Hp2 Hp3 Hp3b; clear Hp2 Hp3 Hp3b.
pattern p2 at 1 2; rewrite <- (opp_opp p2).
pattern p3, (opp p2), (add p3 (opp p2)).
apply add_case.
  intros; discriminate.
  intros; discriminate.
  intros; symmetry; apply uniq_zero with p.
  pattern p at 1; rewrite <- (opp_opp p); auto.
  intros; case n; auto.
intros p4 x4 y4 H4 p5 x5 y5 H5 p6 x6 y6 H6 l0.
intros Hp4; rewrite Hp4; clear Hp4.
intros Hp5; rewrite Hp5; clear Hp5.
intros Hp6 _; rewrite Hp6; clear Hp6.
intros Hx Hl0 Hx6 Hy6.
intros tmp; injection tmp; intros HH1 HH2; clear tmp.
assert (y5 = - y2).
  rewrite <- HH1; ring.
subst y5 x5; clear HH1.
intros tmp; injection tmp; intros HH1 HH2; subst y4 x4;
  clear tmp.
intros _ _.
subst p1; apply curve_elt_irr; clear H6 H5 H4 H3;
  subst;
  apply Keq_minus_eq; field [H1 H2]; split; auto;
  intros HH; case Hx;
  ring_simplify [H1 H2] in HH;
  symmetry; apply Keq_minus_eq; field_simplify_eq [H1 H2];
  auto.
Qed.

Theorem add_shift_minus: forall p1 p2 p3, add p1 p2 = p3 -> p1 = add p3 (opp p2).
intros p1 p2 p3 H.
apply cancel with (opp (opp p2)).
repeat rewrite (add_comm (opp (opp p2))).
rewrite add_minus_id; rewrite opp_opp; auto.
Qed.

Theorem degen_assoc:
 forall p1 p2 p3,
   (p1 = inf_elt \/ p2 = inf_elt \/ p3 = inf_elt) \/
   (p1 = opp p2 \/ p2 = opp p3) \/
   (opp p1 = add p2 p3 \/ opp p3 = add p1 p2) ->
     add p1 (add p2 p3) = add (add p1 p2) p3.
intros p1 p2 p3; intuition; subst;
  repeat (rewrite add_opp || rewrite add_0_r ||
          rewrite add_0_l); auto.
  repeat rewrite (add_comm (opp p2)).
     rewrite add_opp; rewrite (add_comm p2);
        rewrite add_minus_id; auto.
  pattern p3 at 4; rewrite <- opp_opp; rewrite add_minus_id.
  rewrite (add_comm (opp p3));
     rewrite add_opp; rewrite add_0_r; auto.
  rewrite <- H0; rewrite add_opp.
  rewrite <- (opp_opp p1); rewrite H0.
  rewrite opp_add.
  rewrite (add_comm (opp p2)); pattern p2 at 2;
    rewrite <- opp_opp; rewrite add_minus_id.
  rewrite add_comm; auto; rewrite add_opp; auto.
  pattern p3 at 1; rewrite <- opp_opp; rewrite H0.
  rewrite (add_comm p2).
  pattern p2 at 2; rewrite <- opp_opp.
  rewrite opp_add; rewrite add_minus_id; auto.
  rewrite <- H0; rewrite (add_comm (opp p3)).
  repeat rewrite add_opp; auto.
Qed.

Theorem spec4_assoc:
  forall p1 p2,
   add p1 (add p2 p2) = add (add p1 p2) p2.
intros p1 p2.
case (ceqb p1 inf_elt); intros H1.
  apply degen_assoc; auto.
case (ceqb p2 inf_elt); intros H2.
  apply degen_assoc; auto.
case (ceqb p2 (opp p2)); intros H3.
  apply degen_assoc; auto.
case (ceqb p1 (opp p2)); intros H4.
  apply degen_assoc; auto.
case (ceqb (opp p1) (add p2 p2)); intros H5.
  apply degen_assoc; auto.
case (ceqb (opp p2) (add p1 p2)); intros H6.
  apply degen_assoc; auto.
case (ceqb p1 (add p2 p2)); intros H7.
  subst p1; apply spec3_assoc.
  repeat split; auto.
  intros H7; case H2; apply uniq_zero with p2; auto.
  split; auto.
  repeat split; auto.
  intros H7; case H4; apply uniq_opp; rewrite add_comm; auto.
  intros H7; case H1; apply uniq_zero with p2; auto.
  split; auto.
case (ceqb p2 (add p1 p2)); intros H8.
  pattern p1 at 1; rewrite (uniq_zero _ (sym_equal H8)).
  rewrite <- H8; auto.
case (ceqb p1 p2); intros H9.
  subst p1; apply add_comm.
apply spec2_assoc; repeat split; auto.
  repeat split; auto.
  repeat split; auto.
  intros H10;  case H4; apply uniq_opp; rewrite add_comm; auto.
  intros H10;  case H3; apply uniq_opp; auto.
intros H10; case H5; rewrite H10; rewrite opp_opp; auto.
Qed.

(***********************************************************)
(*                                                         *)
(*       Associativity  for add                            *)
(*                                                         *)
(***********************************************************)


Theorem add_assoc: forall p1 p2 p3, add p1 (add p2 p3) = add (add p1 p2) p3.
intros p1 p2 p3.
case (ceqb p1 inf_elt); intros H1.
  apply degen_assoc; auto.
case (ceqb p2 inf_elt); intros H2.
  apply degen_assoc; auto.
case (ceqb p3 inf_elt); intros H3.
  apply degen_assoc; auto.
case (ceqb p1 p2); intros H4.
  subst p1.
  rewrite add_comm; rewrite (add_comm p2).
  rewrite <- spec4_assoc; rewrite add_comm; auto.
case (ceqb p1 (opp p2)); intros H5.
  apply degen_assoc; auto.
case (ceqb p2 p3); intros H6.
  subst p2.
  apply spec4_assoc.
case (ceqb p2 (opp p3)); intros H7.
  apply degen_assoc; auto.
case (ceqb (opp p1) (add p2 p3)); intros H8.
  apply degen_assoc; auto.
case (ceqb (opp p3) (add p1 p2)); intros H9.
  apply degen_assoc; auto.
case (ceqb p1 (add p2 p3)); intros H10.
  rewrite H10.
  apply cancel with (opp p3).
  rewrite spec4_assoc.
  repeat rewrite (add_comm (opp p3)).
  repeat rewrite add_minus_id; rewrite add_comm; auto.
case (ceqb p3 (add p1 p2)); intros H11.
  rewrite H11.
  apply cancel with (opp p1).
  rewrite spec4_assoc.
  repeat rewrite (add_comm (opp p1)).
  repeat rewrite (add_comm p1).
  repeat rewrite add_minus_id; rewrite add_comm; auto.
apply spec1_assoc.
  split; auto.
  split; auto.
  split; auto.
  intros HH; case H5; apply uniq_opp; auto.
  rewrite add_comm; auto.
  repeat split; auto.
  intros HH; case H7; apply uniq_opp; auto.
  rewrite add_comm; auto.
intros HH; case H8; rewrite HH; rewrite opp_opp; auto.
Qed.

(***********************************************************)
(*                                                         *)
(*      K is finite                                        *)
(*                                                         *)
(***********************************************************)

Variable LK: list K.
Hypothesis ULK: ulist LK.
Hypothesis CLK: forall k, In k LK.

(***********************************************************)
(*                                                         *)
(*      Exact square root function                         *)
(*                                                         *)
(***********************************************************)

Fixpoint Kfind_root (r: K) (l: list K) {struct l} : option K :=
  match l with
  | nil => None
  | r1 :: l1 => if (ksub r (kmul r1 r1)) ?0
                then Some r1 else Kfind_root r l1
  end.

Theorem Kfind_root_root: forall r l,
match Kfind_root r l with
  None => forall k, In k l -> kmul k k <> r
| Some k => kmul k k = r
end.
intros r l; elim l; simpl.
  intros k H; case H.
intros a l1 Hrec; generalize (Eth.(is_zero_correct) (ksub r (kmul a a)));
 case is_zero; intros HH; case HH; clear HH; intros H1 H2.
apply trans_equal with (ksub r kO); [rewrite <- H1; auto | idtac]; ring.
generalize Hrec; case Kfind_root; auto.
intros H3 k [H4 | H4]; subst; auto.
intros H4; absurd (false = true); try (intro HH; discriminate).
apply H2; subst; ring.
Qed.

Definition KLroot r := Kfind_root r LK.

Theorem KLroot_root: forall r,
match KLroot r with
  None => forall k, kmul k k <> r
| Some k => kmul k k = r
end.
intros r; generalize (Kfind_root_root r LK); unfold KLroot;
  case Kfind_root; auto.
Qed.

(***********************************************************)
(*                                                         *)
(*      List of elements of the curve                      *)
(*                                                         *)
(***********************************************************)

Fixpoint EKa (l: list K) : list (K * K) :=
  match l with
  | nil => nil
  | x :: l1 =>
      let y := kplus (kplus (x ^ 3) (kmul A x)) B in
      match KLroot y with
      | Some k =>
          if k ?0 then (x, kO) :: EKa l1 else (x, k) :: (x, kopp k) :: EKa l1
      | None => EKa l1
      end
  end.

Theorem EKa_in: forall l x y,
  ~ In x l -> ~ In (x, y) (EKa l).
intros l x y; elim l; simpl; auto.
intros a l1 Rec; case KLroot; auto.
intros k Hk; case (Eth.(is_zero_correct) k); case is_zero.
simpl; intros _ _ H1; case Hk; inversion_clear H1.
  injection H; intros; subst a; auto.
  case Rec; auto; case Hk; auto.
simpl; intros _ H1 H2; inversion_clear H2; case Hk; auto.
  injection H; auto.
case H; intros H2.
  injection H2; auto.
case Rec; auto.
Qed.

Theorem EKa_ulist: forall l, ulist l -> ulist (EKa l).
intros l; elim l; simpl; auto.
intros a l1 Hrec H; inversion_clear H.
generalize (KLroot_root (kplus (kplus (kmul a (kmul a a)) (kmul A a)) B));
  case KLroot; auto.
intros k Hk; case (Eth.(is_zero_correct) k); case is_zero.
intros H2 _; constructor; auto.
  apply EKa_in; auto.
intros _ H2; repeat constructor; auto.
simpl; intros H3; inversion_clear H3.
  injection H; intros H3.
  case (@Kmult_integral (kplus kI kI) k).
    apply trans_equal with (kplus k (kopp k)); [rewrite H3 |idtac];
      ring.
    intros H4; case two_not_zero; auto.
    intros H5; assert (H6 := H2 H5); discriminate.
  case (EKa_in l1 a k); auto.
apply EKa_in; auto.
Qed.

Let In_curve x y := kmul y y = kplus (kplus (x ^ 3) (kmul A x)) B.

Theorem EKa_complete: forall l x y,
  In x l -> In_curve x y ->  In (x, y) (EKa l).
unfold In_curve; intros l x y; elim l; simpl; auto.
intros a l1 Hrec [H1 | H1] H2; subst; auto.
  generalize (KLroot_root (kplus (kplus (kmul x (kmul x x)) (kmul A x)) B));
  case KLroot; auto.
  intros k Hk; rewrite <- Hk in H2.
  case (@Kmult_integral (kplus y k) (ksub y k)); try intros H3.
    apply trans_equal with (ksub (kmul y y) (kmul k k)); try ring.
    rewrite H2; ring.
  generalize (Eth.(is_zero_correct) k); case is_zero; intros HH;
    case HH; intros H4 H5; clear HH.
      rewrite <- H3; rewrite H4; auto; simpl; left.
      apply f_equal2 with (f := @pair K K); auto; ring.
    right; left; apply f_equal2 with (f := @pair K K); auto.
    apply trans_equal with (ksub (kplus y k) k); try ring;
      rewrite H3; ring.
  generalize (Eth.(is_zero_correct) k); case is_zero; intros HH;
    case HH; intros H4 H5; clear HH.
      rewrite <- H3; rewrite H4; auto; simpl; left.
      apply f_equal2 with (f := @pair K K); auto; ring.
    left; apply f_equal2 with (f := @pair K K); auto.
    apply trans_equal with (kplus (ksub y k) k); try ring;
      rewrite H3; ring.
  intros H3; case (H3 y); auto.
case KLroot; auto.
intros k; case is_zero; repeat right; auto.
Qed.

Theorem EKa_length: forall l,
  (length (EKa l) <= 2 * length l)%nat.
intros l; elim l; simpl; auto.
intros a l1 H; case KLroot.
  intros k; case is_zero; simpl.
    apply le_n_S.
    apply le_trans with (1 := H).
    rewrite <- plus_n_Sm; auto.
 rewrite <- plus_n_Sm; auto with arith.
apply le_trans with (1 := H).
rewrite <- plus_n_Sm; auto.
Qed.

Theorem EKa_elt: forall l x y,
  In (x, y) (EKa l) -> In_curve x y.
unfold In_curve; intros l x y; elim l; simpl; auto.
  intros H; case H.
intros a l1 Hrec.
generalize (KLroot_root (kplus (kplus (kmul a (kmul a a)) (kmul A a)) B));
  case KLroot; auto.
intros k Hk; generalize (Eth.(is_zero_correct) k); case is_zero;
  simpl; intros HH HH1; case HH; intros H1 H2; case HH1;
  intros H3; subst; clear HH HH1; auto.
    injection H3; intros; subst y x; rewrite <- H1; auto.
  injection H3; intros; subst; auto.
case H3; clear H3; intros H3; auto.
injection H3; intros; subst; rewrite <- Hk; ring.
Qed.

Definition ELK := EKa LK.

Theorem ELK_ulist: ulist ELK.
unfold ELK; apply EKa_ulist; apply ULK.
Qed.

Theorem ELK_complete: forall x y,
  In_curve x y -> In (x, y) ELK.
intros x y Hxy; unfold ELK; apply EKa_complete; auto.
Qed.

Theorem ELK_length: (length ELK <= 2 * length LK)%nat.
exact (EKa_length LK).
Qed.


Theorem ELK_elt: forall x y,
  In (x, y) ELK -> In_curve x y.
exact (EKa_elt LK).
Qed.


Definition mk_lelt:
  forall l, (forall x y: K, In (x, y) l -> In_curve x y) -> list elt.
fix mk_lelt 1; intros l;  case l.
  intros _; exact (@nil _).
intros a l1; case a; intros x y H.
assert (F1: y^2 = x^3 + A * x + B); auto.
  change (y^2) with (y * y).
  unfold In_curve in H; rewrite (H x y);
  try ring; simpl; auto.
assert (F2: forall x1 y1, In (x1, y1) l1 -> In_curve x1 y1).
  intros x1 y1 Hxy1; apply H; simpl; auto.
exact (cons (@curve_elt x y F1) (mk_lelt _ F2)).
Defined.

Theorem mk_lelt_inf:
  forall l H, ~In inf_elt (mk_lelt l H).
intros l; elim l; simpl; auto.
intros (x, y) l1 Hrec H H1; simpl.
inversion_clear H1; try discriminate.
case (Hrec (fun (x1 y1 : K) (Hxy1 : In (x1, y1) l1) =>
           H x1 y1 (or_intror ((x, y) = (x1, y1)) Hxy1)));
  auto.
Qed.

Theorem mk_lelt_in: forall x1 y1 H1 l H,
  In (@curve_elt x1 y1 H1) (mk_lelt l H) -> In (x1, y1) l.
intros x1 y1 H1 l; elim l; simpl; auto.
intros (x, y) l1 Hrec H; simpl; auto.
intros [H2 | H2]; auto.
  injection H2; intros; subst; auto.
right; apply (Hrec _ H2); auto.
Qed.

Theorem mk_lelt_in_rev: forall x1 y1 H1 l H,
  In (x1, y1) l -> In (@curve_elt x1 y1 H1) (mk_lelt l H).
intros x1 y1 H1 l; elim l; simpl; auto.
intros (x, y) l1 Hrec H; simpl; auto.
intros [H2 | H2]; auto.
  left; apply curve_elt_irr; injection H2; auto.
Qed.

Theorem mk_lelt_ulist:
  forall l H, ulist l -> ulist (mk_lelt l H).
intros l; elim l; simpl; auto.
intros (x, y) l1 Hrec H; simpl; auto.
intros H1; inversion_clear H1.
constructor; auto.
intros H3; case H0; apply mk_lelt_in with (1 := H3).
Qed.

Theorem mk_lelt_length:
  forall l H, length (mk_lelt l H) = length l.
intros l; elim l; simpl; auto.
intros (x, y) l1 Hrec H; simpl; auto.
Qed.

Definition FELLK := inf_elt::mk_lelt _ (ELK_elt).

Theorem FELLK_in: forall e, In e FELLK.
intros e; case e; unfold FELLK; simpl; auto.
intros x y H; right; apply mk_lelt_in_rev.
apply ELK_complete; auto.
Qed.

Theorem FELLK_ulist: ulist FELLK.
unfold FELLK; constructor.
  apply mk_lelt_inf.
apply mk_lelt_ulist.
apply ELK_ulist.
Qed.

Theorem FELLK_length:  (length FELLK <= 2 * length LK + 1)%nat.
unfold FELLK; rewrite plus_comm; simpl.
rewrite mk_lelt_length.
generalize ELK_length; simpl; auto with arith.
Qed.

(***********************************************************)
(*                                                         *)
(*      The elliptic finite group                          *)
(*                                                         *)
(***********************************************************)

Definition EFGroup: FGroup add.
refine
  (@mkGroup _ add FELLK _ _ _ inf_elt _ _ _ opp _ _ _); auto;
  try (intros; apply FELLK_in).
exact FELLK_ulist.
intros; apply add_assoc.
intros a; case a; auto.
intros a _; rewrite add_comm; apply add_opp.
intros a _; apply add_opp.
Defined.

Lemma EFGroup_order: (g_order EFGroup <= 2 * Z_of_nat (length LK) + 1)%Z.
unfold g_order; simpl s.
change (Zpos 2) with (Z_of_nat 2).
change (Zpos 1) with (Z_of_nat 1).
rewrite <- inj_mult; rewrite <- inj_plus.
apply inj_le; apply FELLK_length.
Qed.

(***********************************************************)
(*                                                         *)
(*      Projective version                                 *)
(*                                                         *)
(***********************************************************)

Record pelt: Set := mk_pelt {
  x: K;
  y: K;
  z: K;
  on_curve: y^2 * z = x^3 +  A * x * z^2 + B * z^3
}.

Theorem curve_pelt_irr: forall x1 x2 y1 y2 z1 z2 H1 H2,
 x1 = x2 -> y1 = y2 -> z1 = z2 ->
  @mk_pelt x1 y1 z1 H1 = @mk_pelt x2 y2 z2 H2.
Proof.
intros x1 x2 y1 y2 z1 z2 H1 H2 H3 H4 H5.
subst.
rewrite (fun H => eq_proofs_unicity H H1 H2); auto.
intros x1 y1; case (x1 ?= y1); auto.
Qed.

Lemma popp_lem:
forall x y z,
y ^ 2 * z = x ^ 3 + A * x * z ^ 2 + B * z ^ 3 ->
(- y) ^ 2 * z = x ^ 3 + A * x * z ^ 2 + B * z ^ 3.
Proof.
intros x1 y1 z1 H; rewrite <- H; simpl; ring.
Qed.

Definition popp: pelt -> pelt.
refine (fun p => let (x,y,z,H) := p in
                 @mk_pelt x (-y) z _).
apply popp_lem; auto.
Defined.

Let ARFth := Rth_ARth Ksth Keqe (F_R Eth.(Kfth)).


Lemma add_lem0:
  1 ^ 2 * 0 = 0 ^ 3 + A * 0 * 0 ^ 2 + B * 0 ^ 3.
Proof.
ring.
Qed.

Lemma add_lem_gen:
 forall x1 x2 y1 y2 z1 z2
  (H1 : y1 ^ 2 * z1 = x1 ^ 3 + A * x1 * z1 ^ 2 + B * z1 ^ 3)
  (H2 : y2 ^ 2 * z2 = x2 ^ 3 + A * x2 * z2 ^ 2 + B * z2 ^ 3),
let d1 := x2 * z1 in
let d2 := x1 * z2  in
let l := d1 - d2 in
let dl := d1 + d2  in
let m := y2 * z1 - y1 * z2 in
let l2 := l * l  in
let l3 := l2 * l in
let m2 := m * m  in
let x3 := z1 * z2 * m2 - l2 * dl in
(z2 * l2 * (m * x1 - y1 * l) - m * x3) ^ 2 * (z1 * z2 * l3) =
(l * x3) ^ 3 + A * (l * x3) * (z1 * z2 * l3) ^ 2 + B * (z1 * z2 * l3) ^ 3.
Proof.
intros x1 x2 y1 y2 z1 z2 H1 H2 d1 d2 l dl m l2 l3 m2 x3.
unfold x3, m2, l3, l2, m, dl, l, d1, d2.
apply Keq_minus_eq.
ring [H1 H2].
Qed.

Lemma add_lem_tan:
 forall x1 y1 z1
  (H1 : y1 ^ 2 * z1 = x1 ^ 3 + A * x1 * z1 ^ 2 + B * z1 ^ 3),
  let m := 3 * x1 * x1 + A * z1 * z1 in
  let l := 2 * y1 * z1  in
  let m2 := m * m in
  let l2 := l * l in
  let l3 := l2 * l in
  let x3 := m2 * z1 - 2 * x1 * l2 in
(l2 * (m * x1 - y1 * l) - m * x3) ^ 2 * (z1 * l3) =
(l * x3) ^ 3 + A * (l * x3) * (z1 * l3) ^ 2 + B * (z1 * l3) ^ 3.
Proof.
intros x1 y1 z1 H1 m l m2 l2 l3 x3.
unfold x3, l3, l2, m2, l, m.
apply Keq_minus_eq.
ring [H1].
Qed.

(** doubling a point *)

Definition pdouble := fun p1: pelt =>
  let (x1, y1, z1, H1) := p1 in
  if (is_zero z1) then p1 else
    let m' := 3 * x1 * x1 + A * z1 * z1 in
    let l' := 2 * y1 * z1 in
    let m'2 := m' * m' in
    let l'2 := l' * l' in
    let l'3 := l'2 * l' in
    let x3 := m'2 * z1 - 2 * x1 * l'2 in
    @mk_pelt
          (l' * x3)
          (l'2 * (m' * x1 - y1 * l') - m' * x3)
          (z1 * l'3) (add_lem_tan H1).


(* Adding two points *)
Definition padd := fun p1 p2: pelt =>
  let (x1, y1, z1, H1) := p1 in
  if (is_zero z1) then p2 else
  let (x2, y2, z2, H2) := p2 in
  if (is_zero z2) then p1 else
  let d1 := x2 * z1 in
  let d2 := x1 * z2 in
  let l := d1 - d2 in
  let dl := d1 + d2 in
  let m := y2 * z1 - y1 * z2 in
  if (l ?= 0) then
   (* we have p1 = p2 o p1 = -p2 *)
   if (m ?= 0) then
     (* we do 2p *)
    let m' := 3 * x1 * x1 + A * z1 * z1 in
    let l' := 2 * y1 * z1 in
    let m'2 := m' * m' in
    let l'2 := l' * l' in
    let l'3 := l'2 * l' in
    let x3 := m'2 * z1 - 2 * x1 * l'2 in
    @mk_pelt
          (l' * x3)
          (l'2 * (m' * x1 - y1 * l') - m' * x3)
          (z1 * l'3) (add_lem_tan H1)
   else
     (* p - p *) @mk_pelt 0 1 0 add_lem0
  else
     let l2 := l * l in
     let l3 := l2 * l in
     let m2 := m * m in
     let x3 := z1 * z2 * m2 - l2 * dl in
      @mk_pelt (l * x3)
             (z2 * l2 * (m * x1 - y1 * l) - m * x3)
             (z1 * z2 * l3)
             (add_lem_gen H1 H2).

Definition wb (a : bool) : {b : bool | a = b} :=
   match a as b return a = b ->  ({b' : bool | a = b'}) with
      true => fun (h : a = true) => exist (fun b' => a = b') true h
     | false => fun (h : a = false) => exist (fun b' => a = b') false h
   end (refl_equal a).

Lemma pe2e_lem1: forall x1 y1 z1
      (H1 : y1 ^ 2 * z1 =
           x1 ^ 3 + A * x1 * z1 ^ 2 + B * z1 ^ 3)
      (Hb: is_zero z1 = false),
      (y1 / z1) ^ 2  = (x1 / z1) ^ 3 + A * (x1 / z1) + B.
Proof.
intros x1 y1 z1 H1 Hb.
field [H1].
intros H3; case (Eth.(is_zero_correct) z1); intros _ H4.
generalize (H4 H3); rewrite Hb; intros; discriminate.
Qed.

(* Transfer function from projective to affine *)
Definition pe2e: pelt -> elt.
intros (x1,y1,z1,H1).
case (wb (is_zero z1)); intros b; case b; intros Hb.
exact (inf_elt).
refine (@curve_elt (kdiv x1 z1) (kdiv y1 z1)
         (pe2e_lem1 H1 Hb)).
Defined.

(* Doubling is correct with respect to affine *)
Theorem pe2e_double: forall p1,
  pe2e (pdouble p1) = add (pe2e p1) (pe2e p1).
intros (x1,y1,z1,H1).
unfold pdouble, pe2e.
case wb; intros b; case b; intros Hb; clear b.
  rewrite Hb; auto.
case wb; intros b; case b; intros Hz1; clear b; auto.
apply False_ind; rewrite Hb in Hz1; discriminate.
replace (z1 ?0) with false.
unfold add.
generalize (is_zero_false Hb); intros Hz1.
repeat ksplit.
generalize (Keq_minus_eq_inv KD0); clear KD0; intros KD0.
field_simplify_eq in KD0; auto.
case (Kmult_integral KD0); auto; clear KD0; intro KD0.
  case Kdiff_2_0; auto.
subst y1.
case wb; intros b; case b; intros Hb1; clear b; auto.
case (is_zero_false Hb1); field; auto.
case wb; intros b; case b; intros Hb1; clear b; auto.
case (Kmult_integral (is_zero_true Hb1)); intros V1.
case Hz1; auto.
assert (V2: 2 * y1 * z1 = 0).
  case (Kmult_integral V1); clear V1; intros V1; auto.
  case (Kmult_integral V1); clear V1; intros V1; auto.
case (Kmult_integral V2); clear V2; intros V2.
  case (Kmult_integral V2); clear V2; intros V2.
  case Kdiff_2_0; auto.
  case KD0; field[V2]; auto.
  case KD0; field[V2]; auto.
generalize (is_zero_false Hb1); intros zH.
apply curve_elt_irr; field; repeat (split; auto).
intros HH; case zH; ring [HH].
intros HH; case zH; ring [HH].
Qed.

Theorem pe2e_add: forall p1 p2,
  pe2e (padd p1 p2) = add (pe2e p1) (pe2e p2).
intros (x1,y1,z1,H1) (x2,y2,z2,H2).
unfold padd, pe2e.
case wb; intros b; case b; intros Hb; clear b.
  rewrite Hb; auto.
replace (z1 ?0) with false.
case wb; intros b; case b; intros Hb1; clear b.
  rewrite Hb1; auto.
  case wb; intros b; case b; intros Hb2; clear b; auto.
    rewrite Hb in Hb2; discriminate.
  simpl; apply curve_elt_irr; auto.
replace (z2 ?0) with false.
assert (F1 := is_zero_false Hb).
assert (F2 := is_zero_false Hb1).
unfold add.
case Kdec; intros HH1; apply sym_equal; case Kdec;
  intros HH2; apply sym_equal.
2: case HH2; apply Keq_minus_eq; field_simplify_eq;
   auto; apply trans_equal with (-0); try ring;
   rewrite <- HH1; ring.
2: case HH1;
   apply trans_equal with (x2/z2 * z2 * z1 - x1 * z2); try (field; auto);
   rewrite <- HH2; field; auto.
ksplit; symmetry; ksplit.
generalize (Keq_minus_eq_inv KD0); clear KD0; intros KD0.
field_simplify_eq in KD0; auto.
rewrite <- KD in KD0.
generalize (Keq_minus_eq_inv KD0); clear KD0; intros KD0.
field_simplify_eq in KD0; auto.
case (Kmult_integral KD0); clear KD0; intros KD0; auto.
  2: case F2; auto.
case (Kmult_integral KD0); clear KD0; intros KD0; auto.
  case Kdiff_2_0; auto.
case wb; intros b; case b; intros Hb2; auto.
case (is_zero_false Hb2).
ring [KD0].
assert (HH: y1 <> 0).
  intros HH.
  ring_simplify [HH] in KD.
  case (Kmult_integral KD); clear KD; intros KD; auto.
  case KD0; field [HH KD]; auto.
case wb; intros b; case b; intros Hb2; auto.
assert (F3 := is_zero_true Hb2).
assert (V1: 2 * y1 * z1 = 0).
  case (Kmult_integral F3); clear F3; intros V1; auto.
    case F1; auto.
  case (Kmult_integral V1); clear V1; intros V1; auto.
  case (Kmult_integral V1); clear V1; intros V1; auto.
case (Kmult_integral V1); clear V1; intros V1; auto.
case (Kmult_integral V1); clear V1; intros V1; auto.
  case Kdiff_2_0; auto.
  case HH; auto.
case F1; auto.
apply curve_elt_irr; field; repeat (split; auto).
case wb; intros b; case b; intros Hb2; auto.
case (is_zero_false Hb2); auto.
case (@curve_elt_opp (x1/z1) (x2/z2) (y1/z1) (y2/z2)
           (pe2e_lem1 H1 Hb)
           (pe2e_lem1 H2 Hb1)); auto;
  intros tmp; injection tmp; intros HH _.
generalize (Keq_minus_eq_inv HH); clear HH; intros HH.
field_simplify_eq in HH; auto.
case KD; symmetry; apply Keq_minus_eq; apply trans_equal with (2 := HH).
case KD; symmetry; apply Keq_minus_eq; apply trans_equal with (2 := HH).
  ring.
case KD0; auto.
case wb; intros b; case b; intros Hb2; auto.
assert (F3 := is_zero_true Hb2).
case HH1.
  case (Kmult_integral F3); clear F3; intros V1; auto.
  case (Kmult_integral V1); clear V1; intros V1; auto.
    case F1; auto.
    case F2; auto.
case (Kmult_integral V1); clear V1; intros V1; auto.
case (Kmult_integral V1); clear V1; intros V1; auto.
apply curve_elt_irr; field; repeat (split; auto).
Qed.

End ELLIPTIC.

Unset Implicit Arguments.
