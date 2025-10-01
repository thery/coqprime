From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo18:
  prime  1962185163319594728750369731->
  prime  6582815405310833702100048645688946027.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      6582815405310833702100048645688946027
      3354839048
      ((1962185163319594728750369731,1)::nil)
      6582815405310833702100048645688609887
      92236816
      0
      9604)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
