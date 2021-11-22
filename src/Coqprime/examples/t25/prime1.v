Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime2166990353233 : prime 2166990353233.
Proof.
 apply (Pocklington_refl
         (Pock_certif 2166990353233 5 ((2383, 1)::(2,4)::nil) 23898)
        ((Proof_certif 2383 prime2383) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime1234567890123456789012353: prime  1234567890123456789012353.
apply (Pocklington_refl 

(SPock_certif 
1234567890123456789012353
2
((14246767565124824467, 1)::nil))
(
(Ell_certif
14246767565124824467
6574449
((2166990353233,1)::nil)
0
2058
7
49)
:: (Proof_certif 2166990353233 prime2166990353233) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
