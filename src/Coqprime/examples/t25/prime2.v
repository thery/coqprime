Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime5846725286581 : prime 5846725286581.
Proof.
 apply (Pocklington_refl
         (Pock_certif 5846725286581 2 ((10267, 1)::(2,2)::nil) 25246)
        ((Proof_certif 10267 prime10267) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime2345678901234567890123567: prime  2345678901234567890123567.
apply (Pocklington_refl 

(Ell_certif
2345678901234567890123567
77361229
((30321117329139797,1)::nil)
2345678901215618787857727
31749105730618655022
74219
5508459961)
(
(Ell_certif
30321117329139797
5186
((5846725286581,1)::nil)
11370418998427425
0
15160558664569900
22740837996854850)
:: (Proof_certif 5846725286581 prime5846725286581) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
