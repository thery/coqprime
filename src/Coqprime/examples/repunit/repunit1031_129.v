From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo129:
  prime  280561->
  prime  14118902671.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      14118902671
      50323
      ((280561,1)::nil)
      0
      152000
      20
      400)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
