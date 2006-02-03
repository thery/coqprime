Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_lift.
Require Import W2_mod.
Require Import ZDivModAux.
Require Import W2_basic_spec.

Lemma w2_pos_mod_spec : forall x p, [|w2_pos_mod p x|] = [|x|] mod (2 ^ Zpos p).
Proof.
 intros x p; case p; simpl w2_pos_mod.
 intros p1; rewrite Zmod_def_small; auto with zarith.
 case (w2_to_Z_spec x); unfold w2_B; intros H H1; split; auto with zarith.
 apply Zlt_le_trans with (2 ^ 2); auto with zarith.
 apply ZPowerAux.Zpower_le_monotone; auto with zarith.
 assert (0 < Zpos p1); auto with zarith.
 red; simpl; auto.
 rewrite Zpos_xI; auto with zarith.
 intros p1; rewrite Zmod_def_small; auto with zarith.
 case (w2_to_Z_spec x); unfold w2_B; intros H H1; split; auto with zarith.
 apply Zlt_le_trans with (2 ^ 2); auto with zarith.
 apply ZPowerAux.Zpower_le_monotone; auto with zarith.
 assert (0 < Zpos p1); auto with zarith.
 red; simpl; auto.
 pattern (Zpos (xO p1)); rewrite Zpos_xO; auto with zarith.
 case x; auto.
Qed.

