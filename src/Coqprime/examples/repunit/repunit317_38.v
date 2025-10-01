From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo38:
  prime  478167688800651670167833999697650575284472479001->
  prime  33568806256872149200792449996281705136473942403727957.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      33568806256872149200792449996281705136473942403727957
      70203
      ((478167688800651670167833999697650575284472479001,1)::nil)
      0
      4052240
      296
      5476)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
