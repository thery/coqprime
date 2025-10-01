From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo124:
  prime  162173802827989698187157815100236849->
  prime  4168976488012087176910641077201840342376667.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4168976488012087176910641077201840342376667
      25706843
      ((162173802827989698187157815100236849,1)::nil)
      4168976488012087176910641077181094510900507
      36370126051009921296
      0
      6030764964)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
