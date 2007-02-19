Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime6789012345678901234567903 : prime 6789012345678901234567903.
Proof.
 apply (Pocklington_refl
         (Pock_certif 6789012345678901234567903 3 ((38219, 1)::(71, 1)::(11, 1)::(3, 1)::(2,1)::nil) 252373641)
        ((Proof_certif 38219 prime38219) ::
         (Proof_certif 71 prime71) ::
         (Proof_certif 11 prime11) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Time Qed.

