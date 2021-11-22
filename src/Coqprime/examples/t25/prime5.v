Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime7376765261 : prime 7376765261.
Proof.
 apply (Pocklington_refl
         (Pock_certif 7376765261 2 ((461, 1)::(2,2)::nil) 2621)
        ((Proof_certif 461 prime461) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime5678901234567890123456797: prime  5678901234567890123456797.
apply (Pocklington_refl 

(Ell_certif
5678901234567890123456797
4116859400
((1379425596745957,1)::nil)
5678901234567890123442397
0
600
14400)
(
(SPock_certif 
1379425596745957
2
((7376765261, 1)::nil))
:: (Proof_certif 7376765261 prime7376765261) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
