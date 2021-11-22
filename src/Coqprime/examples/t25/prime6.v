Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime14139308836963 : prime 14139308836963.
Proof.
 apply (Pocklington_refl
         (Pock_certif 14139308836963 2 ((10607, 1)::(2,1)::nil) 6921)
        ((Proof_certif 10607 prime10607) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime6789012345678901234567903: prime  6789012345678901234567903.
apply (Pocklington_refl 

(SPock_certif 
6789012345678901234567903
2
((14139308836963, 1)::nil))
( (Proof_certif 14139308836963 prime14139308836963) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
