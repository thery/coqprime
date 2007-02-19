Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime1234567890123456789012353 : prime 1234567890123456789012353.
Proof.
 apply (Pocklington_refl
         (Pock_certif 1234567890123456789012353 3 ((14246767565124824467, 1)::(2,7)::nil) 1)
        ((Pock_certif 14246767565124824467 2 ((3674753, 1)::(2,1)::nil) 4403636) ::
         (Pock_certif 3674753 3 ((2,7)::nil) 21) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Time Qed.

