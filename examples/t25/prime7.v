Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime7890123456789012345678973 : prime 7890123456789012345678973.
Proof.
 apply (Pocklington_refl
         (Pock_certif 7890123456789012345678973 2 ((44301788857, 1)::(2,2)::nil) 223069282798)
        ((Pock_certif 44301788857 5 ((1607, 1)::(2,3)::nil) 592) ::
         (Proof_certif 1607 prime1607) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Time Qed.

