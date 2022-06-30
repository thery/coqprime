Set Loose Hint Behavior "Strict".
Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime6186655106941 : prime 6186655106941.
Proof.
 apply (Pocklington_refl
         (Pock_certif 6186655106941 2 ((1339102837, 1)::(2,2)::nil) 1)
        ((Pock_certif 1339102837 2 ((599, 1)::(2,2)::nil) 3018) ::
         (Proof_certif 599 prime599) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime89012345678901234567890123456789012345678901234671: prime  89012345678901234567890123456789012345678901234671.
apply (Pocklington_refl 

(SPock_certif 
89012345678901234567890123456789012345678901234671
2
((9434440862093035546786759640267923465041649, 1)::nil))
(
(Ell_certif
9434440862093035546786759640267923465041649
19763113
((477376254545173907915829899446234441,1)::nil)
0
19008
12
144)
::
(Ell_certif
477376254545173907915829899446234441
65611
((7275857013994206904573583733469,1)::nil)
0
400921463778173399226185393785663489
2453
447540238636100538671090530731220864)
::
(SPock_certif 
7275857013994206904573583733469
2
((55120128893895506852830179799, 1)::nil))
::
(Ell_certif
55120128893895506852830179799
15841
((3479586446177328425306107,1)::nil)
0
13134093212998538742179185769
41340096670421630139622641408
3445008055868469178302417314)
::
(Ell_certif
3479586446177328425306107
562434204919
((6186655106941,1)::nil)
0
75449
38
361)
:: (Proof_certif 6186655106941 prime6186655106941) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
