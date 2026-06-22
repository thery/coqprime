From Coqprime Require Import PocklingtonRefl.

(******************************************************************************)
(*                                                                            *)
(* Belphegor's Prime is the palindromic prime number 10^30 + 666 × 10^14 + 1, *)
(* written out in decimal form as 1,000,000,000,000,066,600,000,000,000,001.  *)
(* It is widely famous for its combination of mathematical properties and     *)
(* spooky, superstitious numerology                                           *)
(*                                                                            *)
(******************************************************************************)

Local Open Scope positive_scope.

Lemma myPrime : prime 1000000000000066600000000000001.
Proof.
 apply (Pocklington_refl
         (Pock_certif 1000000000000066600000000000001 3 ((5, 8)::(2,15)::nil) 12805203124)
        ((Proof_certif 5 prime5) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

