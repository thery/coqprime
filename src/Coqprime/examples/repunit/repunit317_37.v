From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo37:
  prime  33568806256872149200792449996281705136473942403727957->
  prime  1087763597947685122702478549640429617601156417723601687733.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1087763597947685122702478549640429617601156417723601687733
      32404
      ((33568806256872149200792449996281705136473942403727957,1)::nil)
      100
      0
      20
      100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
