From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo20:
  prime  4277434321243->
  prime  604724655373235676787.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      604724655373235676787
      141375556
      ((4277434321243,1)::nil)
      0
      380315115293323995069
      151181163843308919277
      491338782490753988105)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
