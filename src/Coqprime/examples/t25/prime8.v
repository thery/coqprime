Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime142948719999101 : prime 142948719999101.
Proof.
 apply (Pocklington_refl
         (Pock_certif 142948719999101 2 ((7256280203, 1)::(2,2)::nil) 1)
        ((Pock_certif 7256280203 2 ((33285689, 1)::(2,1)::nil) 1) ::
         (Pock_certif 33285689 3 ((4160711, 1)::(2,3)::nil) 1) ::
         (Pock_certif 4160711 7 ((416071, 1)::(2,1)::nil) 1) ::
         (Pock_certif 416071 13 ((3, 3)::(2,1)::nil) 28) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime8901234567890123456789017: prime  8901234567890123456789017.
apply (Pocklington_refl 

(SPock_certif 
8901234567890123456789017
2
((11521380934487542399, 1)::nil))
(
(SPock_certif 
11521380934487542399
2
((142948719999101, 1)::nil))
:: (Proof_certif 142948719999101 prime142948719999101) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
