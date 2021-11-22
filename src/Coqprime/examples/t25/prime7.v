Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime439901929 : prime 439901929.
Proof.
 apply (Pocklington_refl
         (Pock_certif 439901929 7 ((3, 4)::(2,3)::nil) 1051)
        ((Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime7890123456789012345678973: prime  7890123456789012345678973.
apply (Pocklington_refl 

(Ell_certif
7890123456789012345678973
6605516421
((1194474883403587,1)::nil)
0
1272112
129
1849)
(
(Ell_certif
1194474883403587
2715321
((439901929,1)::nil)
0
9000
10
100)
:: (Proof_certif 439901929 prime439901929) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
