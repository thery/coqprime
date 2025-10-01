From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo43:
  prime  27720701689->
  prime  17216634550825321.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17216634550825321
      621075
      ((27720701689,1)::nil)
      0
      1080
      6
      36)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
