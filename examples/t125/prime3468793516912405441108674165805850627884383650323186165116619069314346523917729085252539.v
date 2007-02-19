Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime3468793516912405441108674165805850627884383650323186165116619069314346523917729085252539 : prime 3468793516912405441108674165805850627884383650323186165116619069314346523917729085252539.
Proof.
 apply (Pocklington_refl
         (Pock_certif 3468793516912405441108674165805850627884383650323186165116619069314346523917729085252539 2 ((505175633613962251, 1)::(15603005953, 1)::(7, 1)::(2,1)::nil) 173269974505702454886091750569)
        ((Pock_certif 505175633613962251 2 ((4483, 1)::(5, 2)::(3, 1)::(2,1)::nil) 41851) ::
         (Pock_certif 15603005953 5 ((3, 2)::(2,9)::nil) 3796) ::
         (Proof_certif 4483 prime4483) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Qed.

