Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma prime115792089237316195423570985008687907852837564279074904382605163141518161494337 : prime 115792089237316195423570985008687907852837564279074904382605163141518161494337.
Proof.
 apply (Pocklington_refl
         (Pock_certif 115792089237316195423570985008687907852837564279074904382605163141518161494337 5 ((174723607534414371449, 1)::(631, 1)::(149, 1)::(2,6)::nil) 1122621917055392771987235982)
        ((Pock_certif 174723607534414371449 3 ((4051, 1)::(59, 1)::(17, 1)::(2,3)::nil) 53130590) ::
         (Proof_certif 4051 prime4051) ::
         (Proof_certif 631 prime631) ::
         (Proof_certif 149 prime149) ::
         (Proof_certif 59 prime59) ::
         (Proof_certif 17 prime17) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

