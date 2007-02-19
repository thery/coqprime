Require Import PocklingtonRefl.
Set Virtual Machine.
Open Local Scope positive_scope.
Lemma prime789012345678901234567890123456789012345678901234567890123456789012345678959: prime  789012345678901234567890123456789012345678901234567890123456789012345678959.
apply (Pocklington_refl 

(SPock_certif 
789012345678901234567890123456789012345678901234567890123456789012345678959
2
((394506172839450617283945061728394506172839450617283945061728394506172839479, 1)::nil))
(
(Ell_certif
394506172839450617283945061728394506172839450617283945061728394506172839479
239
((1650653442842889612066715739449349398249814414659252768600365116539773821,1)::nil)
99732839895929658721858427128528143209595282124976935293626830813033217768
202446870946127498356534994784223914312700292280139740154553523474271118842
0
133651010739828353241318700256601626348201888236269242108007321549960096204)
::
(Ell_certif
1650653442842889612066715739449349398249814414659252768600365116539773821
736
((2242735656036534799003689863382268201911807580302126684830278105025551,1)::nil)
1650653442842889612066715739449349398249814414659252768600365116539630461
25690112
64
4096)
::
(Ell_certif
2242735656036534799003689863382268201911807580302126684830278105025551
163806000
((13691413355045204687274519024835893004331196287838640974928381,1)::nil)
458780045235945239011361112474093385500753683290864974888776245978629
2148718638500306357536058174389106709980712320000391528056236970099338
691035487657762580526860539770008202621674112218820028822675362393602
1635814914901580201052657899191945983097162084387463291852340377921058)
::
(Ell_certif
13691413355045204687274519024835893004331196287838640974928381
1675
((8173978122415047574492250164085331908882575606588834294477,1)::nil)
0
13310
11
121)
::
(Ell_certif
8173978122415047574492250164085331908882575606588834294477
9529488
((857756274252619613403390629583497819082400600470199,1)::nil)
0
44851536
705
19881)
::
(Ell_certif
857756274252619613403390629583497819082400600470199
1512783
((567005495337149884288355096629900853318519383,1)::nil)
0
78608
17
289)
::
(Ell_certif
567005495337149884288355096629900853318519383
19857
((28554439005748596680683507904331946271827,1)::nil)
0
8586756
645
16641)
::
(SPock_certif 
28554439005748596680683507904331946271827
2
((4759073167624766113447251317388657711971, 1)::nil))::
(Pock_certif 4759073167624766113447251317388657711971 2 ((36492039218982424614098219335397, 1)::(2,1)::nil) 1)
        ::(Pock_certif 36492039218982424614098219335397 2 ((568733190227, 1)::(2,
2)::nil) 2363608589658) ::
         (Pock_certif 568733190227 2 ((2969, 1)::(2,1)::nil) 10509) ::
         (Proof_certif 2969 prime2969) ::
         (Proof_certif 2 prime2) ::
          nil)).

exact_no_check (refl_equal true).
Time Qed.
