From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo127:
  prime  354200948800717->
  prime  17355846602307319.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17355846602307319
      49
      ((354200948800717,1)::nil)
      0
      14711791846486947
      8677923301153675
      9762663713797927)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
