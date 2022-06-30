Set Loose Hint Behavior "Strict".
Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime4819935037 : prime 4819935037.
Proof.
 apply (Pocklington_refl
         (Pock_certif 4819935037 2 ((57380179, 1)::(2,2)::nil) 1)
        ((Pock_certif 57380179 2 ((9563363, 1)::(2,1)::nil) 1) ::
         (Pock_certif 9563363 2 ((241, 1)::(2,1)::nil) 560) ::
         (Proof_certif 241 prime241) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime8901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901235157: prime  8901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901235157.
apply (Pocklington_refl 

(Ell_certif
8901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901235157
1156922
((7693893424007948208080590001468466529781515195887854519148778478161861100744009274334848368093,1)::nil)
2178
0
99
1089)
(
(Ell_certif
7693893424007948208080590001468466529781515195887854519148778478161861100744009274334848368093
174332609734004
((44133415060712164411292774692094034654673959380256317749993959868864621180235993,1)::nil)
6716617511956399606093670966280919847801782173513907580606549278856961954869757947286792229898
417422542823734559743201794605126495092036298685024850169386231229230783225870256079931728488
0
1375044944850795009802581112964584671990051818335005208014191429090934977392459228110871146792)
::
(SPock_certif 
44133415060712164411292774692094034654673959380256317749993959868864621180235993
2
((324510404858177679494799813912456137166720289560708218749955587271063391031147, 1)::nil))
::
(Ell_certif
324510404858177679494799813912456137166720289560708218749955587271063391031147
8138719
((39872417865536048055572358980873542527651362892785238594902199452149867,1)::nil)
0
711828
117
1521)
::
(Ell_certif
39872417865536048055572358980873542527651362892785238594902199452149867
15961253415843
((2498075610149703917611545457586296308821537391558714609661,1)::nil)
0
119164
93
961)
::
(Ell_certif
2498075610149703917611545457586296308821537391558714609661
606
((4122236980445055969656015606671113389530388835354169943,1)::nil)
1941535761979114296033961579264838036574568272261525721170
758577932551736704163510333117507469761998748606800467748
585616937911092920306132184545790765370916652261595391410
44885468115159188225229075154418382392705680871468124775)
::
(Ell_certif
4122236980445055969656015606671113389530388835354169943
17040853965493
((241903192691657908686211093523780482135679,1)::nil)
4122236980445055969656015606671113389418495002906369463
14406462054002124060149776
0
3795584547076)
::
(SPock_certif 
241903192691657908686211093523780482135679
2
((13661701613075547282997699307, 1)::nil))
::
(SPock_certif 
13661701613075547282997699307
2
((764676011030759391189841, 1)::nil))
::
(SPock_certif 
764676011030759391189841
2
((3186150045961497463291, 1)::nil))
::
(SPock_certif 
3186150045961497463291
2
((15100952869621771, 1)::nil))
::
(SPock_certif 
15100952869621771
2
((503365095654059, 1)::nil))
::
(SPock_certif 
503365095654059
2
((4819935037, 1)::nil))
:: (Proof_certif 4819935037 prime4819935037) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
