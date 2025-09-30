From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo42:
  prime  17216634550825321->
  prime  77078872901429921017.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      77078872901429921017
      4477
      ((17216634550825321,1)::nil)
      0
      99144
      18
      324)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
