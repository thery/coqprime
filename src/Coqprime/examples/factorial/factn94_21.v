From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo21:
  prime  3194496031->
  prime  4277434321243.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4277434321243
      1339
      ((3194496031,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
