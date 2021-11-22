Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime174550993 : prime 174550993.
Proof.
 apply (Pocklington_refl
         (Pock_certif 174550993 5 ((11, 1)::(3, 1)::(2,4)::nil) 34)
        ((Proof_certif 11 prime11) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime4567890123456789012345689: prime  4567890123456789012345689.
apply (Pocklington_refl 

(SPock_certif 
4567890123456789012345689
2
((570986265432098626543211, 1)::nil))
(
(Ell_certif
570986265432098626543211
4566
((125051744509636077691,1)::nil)
570986265432098626449131
9834496
0
3136)
::
(Ell_certif
125051744509636077691
138775
((901111472016823,1)::nil)
0
192
4
16)
::
(SPock_certif 
901111472016823
2
((174550993, 1)::nil))
:: (Proof_certif 174550993 prime174550993) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
