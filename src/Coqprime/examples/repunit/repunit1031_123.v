From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo123:
  prime  4168976488012087176910641077201840342376667->
  prime  2247738997249499727846022191552509369986174549487203.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2247738997249499727846022191552509369986174549487203
      539158473
      ((4168976488012087176910641077201840342376667,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
