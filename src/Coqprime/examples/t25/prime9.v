Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime621072748687 : prime 621072748687.
Proof.
 apply (Pocklington_refl
         (Pock_certif 621072748687 3 ((7962471137, 1)::(2,1)::nil) 1)
        ((Pock_certif 7962471137 3 ((248827223, 1)::(2,5)::nil) 1) ::
         (Pock_certif 248827223 5 ((601, 1)::(2,1)::nil) 265) ::
         (Proof_certif 601 prime601) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime9012345678901234567890149: prime  9012345678901234567890149.
apply (Pocklington_refl 

(SPock_certif 
9012345678901234567890149
2
((28519720253228549537, 1)::nil))
(
(Ell_certif
28519720253228549537
5204
((5480345934414089,1)::nil)
10368
0
288
5184)
::
(SPock_certif 
5480345934414089
2
((621072748687, 1)::nil))
:: (Proof_certif 621072748687 prime621072748687) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
