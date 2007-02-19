Require Import PocklingtonRefl.
Set Virtual Machine.
Open Local Scope positive_scope.
Lemma prime567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901289: prime  567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901289.
apply (Pocklington_refl 

(Ell_certif
567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901289
1079377851
((526127271307875866674309681785908621654176215824856386553029767413787201000779201457216734898431167485613622987714903041820994571478823244923,1)::nil)
0
192
4
16)
(
(Ell_certif
526127271307875866674309681785908621654176215824856386553029767413787201000779201457216734898431167485613622987714903041820994571478823244923
79416
((6624953048603252073565902107710141805859980555868545211960181417016561431988573297370811416036509193774523711624687929377681872553416087,1)::nil)
526127271307875866674309681785908621654176215824856386553029767413787201000779201457216734898431167485613622987714903041820994571478823101563
25690112
64
4096)
::
(Ell_certif
6624953048603252073565902107710141805859980555868545211960181417016561431988573297370811416036509193774523711624687929377681872553416087
57793941
((114630581233476569344283029733344223849693526798398212919243237228218452714436603079226119697711443789721217414513389843213282067,1)::nil)
0
1272112
129
1849)
::
(Ell_certif
114630581233476569344283029733344223849693526798398212919243237228218452714436603079226119697711443789721217414513389843213282067
7310607246
((15680035512261544537675609352977710745110041273088275671162110359774130480194132133927297144276661190867294646160182061,1)::nil)
39934223032022218775631132573242643825932512698858118011738941629652355991634326494194231907950772631976745553502271723912028794
108421727562967769110326103896040068853941817391783414420681895755402124483283096126174998791506532631215988809923070910926128993
66649385823771832478883584824629796720580077143785732033601063219504428333840745367496960058165337354044945815312147281622037094
48152053626964756071587378022184190285755895710173071860494302638027130182330925262622332884443670292503623450892194223971112246)
::
(Ell_certif
15680035512261544537675609352977710745110041273088275671162110359774130480194132133927297144276661190867294646160182061
1981412
((7913566442648749749005057682590854776851074523162409267311336870307234202997331292035297584432859854432962552369,1)::nil)
4447327333273117431552150077382058203489166032239478988567762415794814375059987196812153950399151925102422372301628851
4175564375283566440000668203633522952139621982757270390365902548125123485334815093637259396462671015955401654892921284
0
4035989985684553740691132832010583145132967365288147345272954459242805829724472578299465535500671877639171554072473970)
::
(Ell_certif
7913566442648749749005057682590854776851074523162409267311336870307234202997331292035297584432859854432962552369
2488705216
((3179792605316237561582326704373674916125974207450051516060747005285376905702223040741231603964359207787,1)::nil)
7913566442648749749005057682590854776851074523162409267311336870307234202997331292035297584432859854432962530499
1102248
27
729)
::
(Ell_certif
3179792605316237561582326704373674916125974207450051516060747005285376905702223040741231603964359207787
35714
((89034905228096476496117116659396172820909845087362050929484628547776805758657309892537850996196083,1)::nil)
1107295613582100466300273420587822077537615161039101056704555910125448843801650849573569356461741622856
3166339931076345574842954129636154327764032901237562636788094855444138783626734941559033325655348871153
2611740665428576791445920876153498659634017834232716952849687449750738764480615943780698817817181936196
2095177961454761600943584828654993051359468180334881208912394743144099524137837801788073291239131345287)
::
(Ell_certif
89034905228096476496117116659396172820909845087362050929484628547776805758657309892537850996196083
468344
((190105788113216944160952455159874307818419463230831935777113534336144376253756719440320141479,1)::nil)
89034905228096476496117116659396172820909845087362050929484628547776805758657309892537850996052723
25690112
64
4096)
::         (Pock_certif 190105788113216944160952455159874307818419463230831935777113534336144376253756719440320141479 3 ((127619833241600084620478364926308187997943273331401873878200430685560400713371, 1)::(2,1)::nil) 1)
:: (Pock_certif 127619833241600084620478364926308187997943273331401873878200430685560400713371 2 ((14737665237748469, 1)::(121037317, 1)::(13, 1)::(2,1)::nil) 90178684026226160323782439) ::
         (Pock_certif 14737665237748469 2 ((24727626237833, 1)::(2,2)::nil) 1) ::
         (Pock_certif 24727626237833 3 ((239, 1)::(103, 1)::(2,3)::nil) 310440) ::
         (Pock_certif 121037317 2 ((23, 2)::(2,2)::nil) 2184) ::
         (Proof_certif 239 prime239) ::
         (Proof_certif 103 prime103) ::
         (Proof_certif 23 prime23) ::
         (Proof_certif 13 prime13) ::
         (Proof_certif 2 prime2) ::
          nil)).
exact_no_check (refl_equal true).
Time Qed.