From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo19:
  prime  604724655373235676787->
  prime  1962185163319594728750369731.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1962185163319594728750369731
      3244758
      ((604724655373235676787,1)::nil)
      1962185163319594728750340901
      1668296
      155
      961)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
