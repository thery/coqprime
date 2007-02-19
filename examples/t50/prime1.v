Require Import PocklingtonRefl.
Set Virtual Machine.
Open Local Scope positive_scope.
Lemma prime12345678901234567890123456789012345678901234568119: prime  12345678901234567890123456789012345678901234568119.
apply (Pocklington_refl 

(Ell_certif
12345678901234567890123456789012345678901234568119
15065364
((819474318790741988718191592468617421805573,1)::nil)
0
10985
26
169)
         ((Pock_certif 819474318790741988718191592468617421805573 2 ((100441230473, 1)::(23, 1)::(3, 2)::(2,2)::nil) 165265901419037)
        ::(Pock_certif 100441230473 3 ((15331, 1)::(2,3)::nil) 83050) ::
         (Proof_certif 15331 prime15331) ::
         (Proof_certif 23 prime23) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
exact_no_check (refl_equal true).
Time Qed.
