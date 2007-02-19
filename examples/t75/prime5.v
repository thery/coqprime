Require Import PocklingtonRefl.
Set Virtual Machine.
Open Local Scope positive_scope.
Lemma prime567890123456789012345678901234567890123456789012345678901234567890123457001: prime  567890123456789012345678901234567890123456789012345678901234567890123457001.
apply (Pocklington_refl 

(Ell_certif
567890123456789012345678901234567890123456789012345678901234567890123457001
28677
((19802982301384001546384869450589946303889376491014415575248444876236177,1)::nil)
0
192
4
16)

((Pock_certif 19802982301384001546384869450589946303889376491014415575248444876236177 5 ((10301640961, 1)::(61061837, 1)::(373, 1)::(29, 1)::(3, 1)::(2,
4)::nil) 451194264388026015708990)
        ::(Pock_certif 10301640961 14 ((5, 1)::(3, 1)::(2,8)::nil) 2398) ::
         (Pock_certif 61061837 2 ((47, 1)::(11, 1)::(2,2)::nil) 574) ::
         (Proof_certif 373 prime373) ::
         (Proof_certif 47 prime47) ::
         (Proof_certif 29 prime29) ::
         (Proof_certif 11 prime11) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).

exact_no_check (refl_equal true).
Time Qed.
