Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime793415879 : prime 793415879.
Proof.
 apply (Pocklington_refl
         (Pock_certif 793415879 7 ((396707939, 1)::(2,1)::nil) 1)
        ((Pock_certif 396707939 2 ((43, 1)::(11, 1)::(2,1)::nil) 1220) ::
         (Proof_certif 43 prime43) ::
         (Proof_certif 11 prime11) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime3456789012345678901234573: prime  3456789012345678901234573.
apply (Pocklington_refl 

(SPock_certif 
3456789012345678901234573
2
((52460968938504569, 1)::nil))
(
(SPock_certif 
52460968938504569
2
((793415879, 1)::nil))
:: (Proof_certif 793415879 prime793415879) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
