From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo128:
  prime  14118902671->
  prime  354200948800717.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      354200948800717
      25087
      ((14118902671,1)::nil)
      0
      19008
      12
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
