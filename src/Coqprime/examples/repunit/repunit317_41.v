From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo41:
  prime  77078872901429921017->
  prime  17645743452205654009588213.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17645743452205654009588213
      228931
      ((77078872901429921017,1)::nil)
      0
      54
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
