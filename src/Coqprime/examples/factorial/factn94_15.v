From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo15:
  prime  95856512308311634801494166176427778326949870855325307->
  prime  256236498511767120698711130680739393368429360192360913891939829.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      256236498511767120698711130680739393368429360192360913891939829
      2673125616
      ((95856512308311634801494166176427778326949870855325307,1)::nil)
      0
      23625
      30
      225)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
