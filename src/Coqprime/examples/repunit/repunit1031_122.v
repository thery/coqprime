From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo122:
  prime  2247738997249499727846022191552509369986174549487203->
  prime  18752886454052576229419363135520296830244692134050144803.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      18752886454052576229419363135520296830244692134050144803
      8343
      ((2247738997249499727846022191552509369986174549487203,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
