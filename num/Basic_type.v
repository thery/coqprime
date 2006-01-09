Set Implicit Arguments.

Require Import ZArith.
Require Import ZDivModAux.
Require Import ZPowerAux.
Require Import JMeq.

Open Local Scope Z_scope.

Section Carry.

 Variable A : Set.

 Inductive carry : Set :=
  | C0 : A -> carry
  | C1 : A -> carry.

 Definition without_c c :=
  match c with
  | C0 a => a
  | C1 a => a
  end.

End Carry.

Section Zn2Z.

 Variable znz : Set.

 Inductive zn2z : Set :=
  | W0 : zn2z
  | WW : znz -> znz -> zn2z.

 Definition zn2z_to_Z (wB:Z) (w_to_Z:znz->Z) (x:zn2z) :=
  match x with
  | W0 => 0
  | WW xh xl => w_to_Z xh * wB + w_to_Z xl
  end.

 Definition base digits := Zpower 2 (Zpos digits).

 Definition interp_carry sign B (interp:znz -> Z) c :=
  match c with
  | C0 x => interp x
  | C1 x => sign*B + interp x
  end.

End Zn2Z.

Implicit Arguments W0 [znz].

Fixpoint word_tr (w:Set) (n:nat) {struct n} : Set :=
 match n with
 | O => w
 | S n => word_tr (zn2z w) n
 end.

Fixpoint word (w:Set) (n:nat) {struct n} : Set :=
 match n with
 | O => w
 | S n => zn2z (word w n)
 end.

Definition zn2z_word_comm : forall w n, zn2z (word w n) = word (zn2z w) n.
 fix zn2z_word_comm 2.
 intros w n; case n.
  reflexivity.
  intros n0;simpl.
  case (zn2z_word_comm w n0).
  reflexivity.
Defined.

Definition word_of_zn2z_word : forall w n, zn2z (word w n) -> word (zn2z w) n.
 intros w n a;rewrite <- zn2z_word_comm;exact a.
Defined.

Definition word_zn2z_comm : forall w n, word (zn2z w) n = zn2z (word w n).
 fix word_zn2z_comm 2.
 intros w n; case n.
  reflexivity.
  intros n0;simpl.
  case (word_zn2z_comm w n0).
  reflexivity.
Defined.

Definition word_tr_word : forall w n, word_tr w n = word w n.
 fix word_tr_word 2.
 intros w n; case n.
  reflexivity.
  intro n0; simpl in |- *.
  case (word_zn2z_comm w n0).
  case (word_tr_word (zn2z w) n0).
  reflexivity.
Defined.

Definition word_of_word_tr w n (a:word_tr w n) : word w n.
 intros w n a;rewrite <- word_tr_word;exact a.
Defined.

Section GENINTERP.

 Variable w             : Set.
 Variable w_digits      : positive.
 Variable w_to_Z        : w -> Z.

 Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).

 Let wB := base w_digits. 

 Variable spec_to_Z   : forall x, 0 <= [| x |] < wB.

 Fixpoint gen_digits (n:nat) : positive := 
  match n with 
  | O => w_digits
  | S n => xO (gen_digits n)
  end.

 Definition gen_wB n := base (gen_digits n).

 Fixpoint gen_to_Z (n:nat) : word w n -> Z :=
  match n return word w n -> Z with
  | O => w_to_Z 
  | S n => zn2z_to_Z (gen_wB n) (gen_to_Z n)
  end.

 Lemma gen_wB_wwB : forall n, gen_wB n * gen_wB n = gen_wB (S n).
 Proof.
  intros n;unfold gen_wB;simpl.
  unfold base;rewrite (Zpos_xO (gen_digits n)).
  replace  (2 * Zpos (gen_digits n)) with 
    (Zpos (gen_digits n) + Zpos (gen_digits n)).
  symmetry; apply Zpower_exp;intro;discriminate.
  ring.
 Qed.

 Lemma spec_gen_to_Z : 
   forall n (x:word w n), 0 <= gen_to_Z n x < gen_wB n.
 Proof.
  induction n;intros. exact (spec_to_Z x).
  unfold gen_to_Z;fold gen_to_Z.
  destruct x;unfold zn2z_to_Z.
  unfold gen_wB,base;split;auto with zarith.
  assert (U0:= IHn w0);assert (U1:= IHn w1).
  split;auto with zarith.
  apply Zlt_le_trans with ((gen_wB n - 1) * gen_wB n + gen_wB n).
  assert (gen_to_Z n w0*gen_wB n <= (gen_wB n - 1)*gen_wB n).
  apply Zmult_le_compat_r;auto with zarith.
  auto with zarith.
  rewrite <- gen_wB_wwB.
  replace ((gen_wB n - 1) * gen_wB n + gen_wB n) with (gen_wB n * gen_wB n);
   [auto with zarith | ring].
 Qed. 

End GENINTERP.

Lemma gen_digits_S : forall n wd, gen_digits wd (S n) = gen_digits (xO wd) n.
Proof.
 induction n;simpl;intros;trivial.
 rewrite <- IHn;trivial.
Qed.

Lemma gen_wB_S : forall n wd, gen_wB wd (S n) = gen_wB (xO wd) n.
Proof.
 intros;unfold gen_wB.
 rewrite gen_digits_S;trivial.
Qed.

Lemma word_of_word_tr_S : forall n (w:Set) x,
   JMeq (word_of_word_tr (zn2z w) n x) (word_of_word_tr w (S n) x).
Proof.
 intros n w x; unfold word_of_word_tr, eq_rec, eq_rect.
 case (word_tr_word w (S n));case (word_tr_word (zn2z w) n);trivial.
Qed.

Lemma zn2z_to_Z_JMeq : forall (w1 w2:Set) wd (wtz1:w1->Z) (wtz2:w2->Z), 
    w1 = w2 ->
    (forall x1 x2, JMeq x1 x2 -> wtz1 x1 = wtz2 x2) ->
    forall x1 x2, JMeq x1 x2 -> zn2z_to_Z wd wtz1 x1 = zn2z_to_Z wd wtz2 x2.
Proof.
 intros w1 w2 wd wtz1 wtz2 Heq Hjm_eq x1 x2 Hjm.
 destruct x1;destruct x2;simpl;trivial.
 rewrite Heq in Hjm;assert (H:= JMeq_eq Hjm);discriminate.
 rewrite <- Heq in Hjm;assert (H:= JMeq_eq Hjm);discriminate.
 generalize w w0 wtz1 Hjm_eq Hjm;rewrite Heq;intros.
 assert (H:= JMeq_eq Hjm0).
 inversion H.
 rewrite (Hjm_eq0 w3 w3).
 rewrite (Hjm_eq0 w4 w4).
 trivial. constructor. constructor.
Qed.

Lemma gen_to_Z_zn2z_to_Z : forall (w:Set) wd (wtz:w -> Z) n x1 x2,
   JMeq x1 x2 -> 
   gen_to_Z wd wtz (S n) x1 =
        gen_to_Z (xO wd) (zn2z_to_Z (base wd) wtz) n x2.
Proof.
 induction n;intros;simpl.
 rewrite (JMeq_eq H);trivial.
 rewrite gen_wB_S. 
 simpl in IHn;apply zn2z_to_Z_JMeq;trivial.
 apply zn2z_word_comm.
Qed.

Lemma gen_to_Z_S : forall (w:Set) wd (wtz:w -> Z) n x,
   gen_to_Z wd wtz (S n) (word_of_word_tr w (S n) x) =
        gen_to_Z (xO wd) (zn2z_to_Z (base wd) wtz) n 
                       (word_of_word_tr (zn2z w) n x).
Proof.
 intros; apply gen_to_Z_zn2z_to_Z;trivial.
 apply sym_JMeq; apply word_of_word_tr_S.
Qed.

Lemma gen_to_Z_S_case : forall (w:Set) wd (wtz:w -> Z) n x,
   gen_to_Z wd wtz (S n) x =
        gen_to_Z (xO wd) (zn2z_to_Z (base wd) wtz) n 
            match zn2z_word_comm w n in (eq _ y) return y with
            | refl_equal => x
            end.
Proof.
 intros; apply gen_to_Z_zn2z_to_Z;trivial.
 case (zn2z_word_comm w n);trivial.
Qed.
