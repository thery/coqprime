Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma prime329719147332060395689499: prime 329719147332060395689499.
Proof.
 apply (Pocklington_refl
(Ell_certif
329719147332060395689499
8209062
((40165264598163841,1)::nil)
329719147332060395595419
9834496
0
3136)
((SPock_certif 
40165264598163841
2
((303179835433, 1)::nil))
::
         (Pock_certif 303179835433 5 ((7951, 1)::(2,3)::nil) 59386) ::
         (Proof_certif 7951 prime7951) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Time Qed.
