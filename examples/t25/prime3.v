Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime3456789012345678901234573 : prime 3456789012345678901234573.
Proof.
 apply (Pocklington_refl
         (Pock_certif 3456789012345678901234573 2 ((52460968938504569, 1)::(2,2)::nil) 1)
        ((Pock_certif 52460968938504569 3 ((2851, 1)::(13, 1)::(2,3)::nil) 95100) ::
         (Proof_certif 2851 prime2851) ::
         (Proof_certif 13 prime13) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Time Qed.

