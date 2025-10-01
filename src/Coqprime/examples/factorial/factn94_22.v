From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo22 : prime 3194496031.
Proof.
 apply (Pocklington_refl
         (Pock_certif 3194496031 11 ((19, 1)::(11, 1)::(3, 1)::(2,1)::nil) 1822)
        ((Proof_certif 19 prime19) ::
         (Proof_certif 11 prime11) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

