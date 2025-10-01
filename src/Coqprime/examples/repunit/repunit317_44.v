From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo44:
  prime  373273->
  prime  27720701689.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      27720701689
      74263
      ((373273,1)::nil)
      0
      62782423
      13860351526
      25988273944)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
