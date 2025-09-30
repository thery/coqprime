From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo125:
  prime  68609290846964444311551637->
  prime  162173802827989698187157815100236849.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      162173802827989698187157815100236849
      2363729472
      ((68609290846964444311551637,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
