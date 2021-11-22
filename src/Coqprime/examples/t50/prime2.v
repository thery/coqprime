Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime12758741597671 : prime 12758741597671.
Proof.
 apply (Pocklington_refl
         (Pock_certif 12758741597671 11 ((1277, 1)::(5, 1)::(3, 1)::(2,1)::nil) 48936)
        ((Proof_certif 1277 prime1277) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime23456789012345678901234567890123456789012345678921: prime  23456789012345678901234567890123456789012345678921.
apply (Pocklington_refl 

(Ell_certif
23456789012345678901234567890123456789012345678921
985748
((23795928586561351279672456893295268820653753,1)::nil)
10368
0
288
5184)
(
(SPock_certif 
23795928586561351279672456893295268820653753
2
((4776647834905838370780687325926589, 1)::nil))
::
(SPock_certif 
4776647834905838370780687325926589
2
((3373243986825092585447171, 1)::nil))
::
(SPock_certif 
3373243986825092585447171
2
((43583861297644259, 1)::nil))
::
(SPock_certif 
43583861297644259
2
((357244764734789, 1)::nil))
::
(SPock_certif 
357244764734789
2
((12758741597671, 1)::nil))
:: (Proof_certif 12758741597671 prime12758741597671) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
