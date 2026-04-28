From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma myPrime : prime 1234567891.
Proof.
 apply (Pocklington_refl
         (Pock_certif 1234567891 2 ((3607, 1)::(2,1)::nil) 12426)
        ((Proof_certif 3607 prime3607) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

