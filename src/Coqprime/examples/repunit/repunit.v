From Stdlib Require Import List.
From Coqprime Require Import PocklingtonRefl.
Require Import repunit317.
Require Import repunit1031.
Local Open Scope positive_scope.
Import ListNotations.

(******************************************************************************)
(*                                                                            *)
(*                       First Repunit Primes                                 *)
(*                                                                            *)
(******************************************************************************)

Definition R (n : Z) := ((10 ^ n - 1) / 9)%Z.

Compute R 1.
Compute R 19.

Lemma primeR2 : prime (R 2).
Proof. now apply prime11. Qed.

Lemma primeR19 : prime (R 19).
Proof.
apply (Pocklington_refl
        (Pock_certif 1111111111111111111 3 ((19, 1)::(13, 1)::(11, 1)::(7, 1)::(5, 1)::(3, 2)::(2,1)::nil) 1943100)
    ((Proof_certif 19 prime19) ::
        (Proof_certif 13 prime13) ::
        (Proof_certif 11 prime11) ::
        (Proof_certif 7 prime7) ::
        (Proof_certif 5 prime5) ::
        (Proof_certif 3 prime3) ::
        (Proof_certif 2 prime2) ::
        nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma primeR23 : prime (R 23).
Proof.
 apply (Pocklington_refl
         (Pock_certif 11111111111111111111111 7 ((4093, 1)::(23, 1)::(11, 2)::(2,1)::nil) 21506235)
        ((Proof_certif 4093 prime4093) ::
         (Proof_certif 23 prime23) ::
         (Proof_certif 11 prime11) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

Lemma R317 : prime (R 317).
Proof. now apply repunit317.primo. Qed.

Lemma R1031 : prime (R 1031).
Proof. now apply repunit1031.primo. Qed.
