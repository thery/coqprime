From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo126:
  prime  17355846602307319->
  prime  68609290846964444311551637.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      68609290846964444311551637
      3953093872
      ((17355846602307319,1)::nil)
      0
      54
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
