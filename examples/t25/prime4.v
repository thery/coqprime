Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime4567890123456789012345689 : prime 4567890123456789012345689.
Proof.
 apply (Pocklington_refl
         (Pock_certif 4567890123456789012345689 3 ((570986265432098626543211, 1)::(2,3)::nil) 1)
        ((Pock_certif 570986265432098626543211 2 ((409901, 1)::(269, 1)::(2,1)::nil) 382765896) ::
         (Pock_certif 409901 2 ((5, 2)::(2,2)::nil) 98) ::
         (Proof_certif 269 prime269) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Time Qed.

