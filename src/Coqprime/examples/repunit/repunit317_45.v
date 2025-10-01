From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo45 : prime 373273.
Proof.
 apply (Pocklington_refl
         (Pock_certif 373273 5 ((103, 1)::(2,3)::nil) 1)
        ((Proof_certif 103 prime103) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

