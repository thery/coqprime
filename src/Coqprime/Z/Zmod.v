(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Import ZArith Znumtheory.

Set Implicit Arguments.

Open Scope Z_scope.

Lemma rel_prime_mod: forall a b, 1 < b ->
  rel_prime a b -> a mod b <> 0.
Proof.
intros a b H H1 H2.
case (not_rel_prime_0 _ H).
rewrite <- H2.
apply rel_prime_mod; auto with zarith.
Qed.

Lemma Zmodpl: forall a b n, 0 < n ->
  (a mod n + b) mod n = (a + b) mod n.
Proof.
intros a b n H.
rewrite Zplus_mod; auto.
rewrite Zmod_mod; auto.
apply sym_equal; apply Zplus_mod; auto.
Qed.

Lemma Zmodpr: forall a b n, 0 < n ->
  (b + a mod n) mod n = (b + a) mod n.
Proof.
intros a b n H; repeat rewrite (Zplus_comm b).
apply Zmodpl; auto.
Qed.

Lemma Zmodml: forall a b n, 0 < n ->
  (a mod n * b) mod n = (a * b) mod n.
Proof.
intros a b n H.
rewrite Zmult_mod; auto.
rewrite Zmod_mod; auto.
apply sym_equal; apply Zmult_mod; auto.
Qed.

Lemma Zmodmr: forall a b n, 0 < n ->
  (b * (a mod n)) mod n = (b * a) mod n.
Proof.
intros a b n H; repeat rewrite (Zmult_comm b).
apply Zmodml; auto.
Qed.


Ltac is_ok t :=
  match t with 
  | (?x mod _ + ?y mod _) mod _ => constr:(false)
  | (?x mod _ * (?y mod _)) mod _ => constr:(false)
  |  ?x mod _ => x
  end.
 
Ltac  rmod t :=
  match t with 
    (?x + ?y) mod _ => 
     match (is_ok x) with
     | false => rmod x
     | ?x1   =>  match (is_ok y) with 
                |false => rmod y
                | ?y1 => 
                   rewrite <- (Zplus_mod x1 y1)
                |false => rmod y
                end
     end
  | (?x * ?y) mod _ => 
     match (is_ok x) with
     | false => rmod x
     | ?x1 =>  match (is_ok y) with 
                |false => rmod y
                | ?y1 => rewrite <- (Zmult_mod x1 y1)
                end
     | false => rmod x
     end
  end.


Lemma Zmod_div_mod: forall n m a, 0 < n -> 0 < m ->
  (n | m) -> a mod n = (a mod m) mod n.
Proof.
intros n m a H1 H2 H3.
pattern a at 1; rewrite (Z_div_mod_eq a m); auto with zarith.
case H3; intros q Hq; pattern m at 1; rewrite Hq.
rewrite (Zmult_comm q).
rewrite Zplus_mod; auto.
rewrite <- Zmult_assoc; rewrite Zmult_mod; auto.
rewrite Z_mod_same; try rewrite Zmult_0_l; auto with zarith.
rewrite (Zmod_small 0); auto with zarith.
rewrite Zplus_0_l; rewrite Zmod_mod; auto with zarith.
Qed.

