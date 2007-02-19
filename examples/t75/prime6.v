Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime678901234567890123456789012345678901234567890123456789012345678901234568009 : prime 678901234567890123456789012345678901234567890123456789012345678901234568009.
Proof.
 apply (Pocklington_refl
         (Pock_certif 678901234567890123456789012345678901234567890123456789012345678901234568009 3 ((871998748885004791826291, 1)::(2,3)::nil) 6689576566658640505724510)
        ((Pock_certif 871998748885004791826291 2 ((6388149507743, 1)::(2,1)::nil) 1) ::
         (Pock_certif 6388149507743 5 ((739, 1)::(61, 1)::(2,1)::nil) 171176) ::
         (Proof_certif 739 prime739) ::
         (Proof_certif 61 prime61) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Time Qed.

