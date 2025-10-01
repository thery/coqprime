From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo40:
  prime  17645743452205654009588213->
  prime  211687172335329042010975199189173069.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      211687172335329042010975199189173069
      11996500624
      ((17645743452205654009588213,1)::nil)
      0
      16464
      28
      196)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
