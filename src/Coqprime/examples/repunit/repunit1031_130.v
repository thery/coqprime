From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo130 : prime 280561.
Proof.
 apply (Pocklington_refl
         (Pock_certif 280561 11 ((3, 1)::(2,4)::nil) 82)
        ((Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

