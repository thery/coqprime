Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.

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

 Lemma spec_without_c : 
  forall B (interp:znz->Z), (forall w, 0 <= interp w < B) ->
   forall sign c,
   interp (without_c c) = (interp_carry sign B interp c) mod B.
 Proof.
  intros B interp H sign;destruct c as [w|w];simpl.
  rewrite Zmod_def_small;trivial.
  rewrite Zplus_comm;rewrite Z_mod_plus.
  rewrite Zmod_def_small;trivial.
  assert (H1 := H w);omega.
 Qed.

End Zn2Z.

Implicit Arguments W0 [znz].
