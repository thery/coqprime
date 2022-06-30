Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime128075015790613 : prime 128075015790613.
Proof.
 apply (Pocklington_refl
         (Pock_certif 128075015790613 2 ((109, 1)::(11, 1)::(3, 2)::(2,2)::nil) 78721)
        ((Proof_certif 109 prime109) ::
         (Proof_certif 11 prime11) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234568879: prime  1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234568879.
apply (Pocklington_refl

(Ell_certif
1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234568879
45778
((26968585130924391389146438876779994055881066380989693668522024489536889340134667337979154985461,1)::nil)
664753466826514960509717270307781155721127367875536470545870213790282393842578427358462455592108798
1066949536887837845474343287185140129923708065140764730961872063439158873937531814092465119792708646
258533591519361098489633299073314845579165628979065330956106901328389038713216847394515309740313464
527364786192333184836771194782614780529233253858047739523622800044730617492469808169610629001738520)
(
(SPock_certif
26968585130924391389146438876779994055881066380989693668522024489536889340134667337979154985461
2
((246468517007168629036249669866386346699699016459419609472875383746453019010552616870582663, 1)::nil))
::
(SPock_certif
246468517007168629036249669866386346699699016459419609472875383746453019010552616870582663
2
((68577773235160998618878594843179284001029219938625378261790590914427662495980138250023, 1)::nil))
::
(Ell_certif
68577773235160998618878594843179284001029219938625378261790590914427662495980138250023
26002760010
((2637326699503734666006271956635240429657345180282035433909365188692640378079,1)::nil)
9574683878665620690738396565226734725608912102051371563961979234017062725086969019706
5989789951585473113280726171429669392308969092255867822149160098356694857390995803612
0
26433544158388942526079486972027982668405452614107071167901402917538854826350748466463)
::
(Ell_certif
2637326699503734666006271956635240429657345180282035433909365188692640378079
14196
((185779564631145017329266832673657398539410161537008895262054635563546679,1)::nil)
0
5832
9
81)
::
(Ell_certif
185779564631145017329266832673657398539410161537008895262054635563546679
33300992
((5578799713568443166175555150839272245207194761507009026976783873,1)::nil)
161576535781768262365025478016135538167000994582266455886427764978291880
116949320913430480919424492319827975683250152316577652210725576283843024
0
156005331631261073481675833374118458329410845179918881972015106727637130)
::
(Ell_certif
5578799713568443166175555150839272245207194761507009026976783873
699497210
((7975442408938905083231933335144283914081779243572412457,1)::nil)
1042169188617401582708901827299147890907520705280177257176160553
0
4413979268123896499256304652092280090743143644524790856101962951
459758965895128249249276577925651813675495146789068171738750092)
::
(Ell_certif
7975442408938905083231933335144283914081779243572412457
4062
((1963427476351281408968964384762463375267543044647701,1)::nil)
182261539303125828072434035369639915028261569276924030
1818896714813358048456218055302453781510211651997358610
0
2252225263348272691262486840529946391017117301334848852)
::
(Ell_certif
1963427476351281408968964384762463375267543044647701
49844
((39391450853689138290846729696561934075372333141,1)::nil)
4624
0
272
4624)
::
(Ell_certif
39391450853689138290846729696561934075372333141
7597610
((5184716095415418571214755401687864912827,1)::nil)
5185408785254035713743037011730102710849192973
16180129902632806607809003377724040331134923777
0
16152390643690358018742414050028510369692398625)
::
(Ell_certif
5184716095415418571214755401687864912827
279
((18583211811524797746770253211537874669,1)::nil)
5184716095415418571214755401687107328923
8234810772496
0
2869636)
::
(Ell_certif
18583211811524797746770253211537874669
1633802
((11374212916574222428711834302497,1)::nil)
254898
0
2499
127449)
::
(Ell_certif
11374212916574222428711834302497
6670864
((1705058432696908381922029,1)::nil)
900
0
90
900)
::
(Ell_certif
1705058432696908381922029
29743
((57326377053406663021,1)::nil)
0
19008
12
144)
::
(Ell_certif
57326377053406663021
447600
((128075015790613,1)::nil)
0
152000
20
400)
:: (Proof_certif 128075015790613 prime128075015790613) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
