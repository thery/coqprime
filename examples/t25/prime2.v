Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime2345678901234567890123567 : prime 2345678901234567890123567.
Proof.
 apply (Pocklington_refl
         (Pock_certif 2345678901234567890123567 5 ((314842379, 1)::(2,1)::nil) 461915632)
        ((Pock_certif 314842379 2 ((643, 1)::(2,1)::nil) 482) ::
         (Proof_certif 643 prime643) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Time Qed.

