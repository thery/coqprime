Set Loose Hint Behavior "Strict".
Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime208574597317 : prime 208574597317.
Proof.
 apply (Pocklington_refl
         (Pock_certif 208574597317 2 ((17381216443, 1)::(2,2)::nil) 1)
        ((Pock_certif 17381216443 2 ((36669233, 1)::(2,1)::nil) 1) ::
         (Pock_certif 36669233 3 ((2291827, 1)::(2,4)::nil) 1) ::
         (Pock_certif 2291827 2 ((53, 1)::(2,1)::nil) 207) ::
         (Proof_certif 53 prime53) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime3456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234979: prime  3456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234979.
apply (Pocklington_refl 

(SPock_certif 
3456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234979
2
((1728394506172839450617283945061728394506172839450617283945061728394506172839450617283945061728394506172839450617283945061728394506172839450617283945061728394506172839450617489, 1)::nil))
(
(Ell_certif
1728394506172839450617283945061728394506172839450617283945061728394506172839450617283945061728394506172839450617283945061728394506172839450617283945061728394506172839450617489
5330
((324276642809163123943205242975934032740370138733699302803951543788837931114343455400365018212364149669932033085045658820671006205678920833650003211535090729742162398181249,1)::nil)
576131502057613150205761315020576131502057613150205761315020576131502057613150205761315020576131502057613150205761315020576131502057613150205761315020576131502057613150221671
0
1308
47524)
::
(Ell_certif
324276642809163123943205242975934032740370138733699302803951543788837931114343455400365018212364149669932033085045658820671006205678920833650003211535090729742162398181249
5920
((54776459933980257422838723475664532557494955867178936284451274288655055931476935033839372999886845044558474684439457135878826558259281379044002825870222848938333666039,1)::nil)
194793747286410541613704330395541797216594126710112356427534604540974419867422895314375238671329503251722811132529747820341823194653596447515528900593597165000376473094524
25477912608175642712422540943835936598610092317725923360960877078092175016080748037870657493924853085356431761102438049794555370874161008610787655611302976252789509407134
249554573202502234470752652793705221393403958316844599770068668895279869770328778498452593944442381203924221213780722758989352001990585011363698612576531880488692104737694
200917219138597366434906486399850976138207269866178727143059500036828833903494612873835080268789872004931586706068363534868642630144118400833002823563648687053160327185219)
::
(Ell_certif
54776459933980257422838723475664532557494955867178936284451274288655055931476935033839372999886845044558474684439457135878826558259281379044002825870222848938333666039
19561188
((2800262434673203765683286898304158855663314307248564672270992655898765245315209640350330617426436722217912740947742363503472165053268878901966182223258841199523,1)::nil)
22324055542197282741865135525919614520601426717844320987934023197945262077082752249255266289515425818553107453938987837567281075144204590884031947603982336357813412891
10781594092328127422443526678243844622128004144049360873009198553450186925736715047282637160980773132958099100639854185990528833524462875686208235902151749549652520308
0
26036652031028970617691357476766137133885641614426636062136973523169631450302023280347050240325747678177501411587432521253053322624914463932986842827389388721759628045)
::
(Ell_certif
2800262434673203765683286898304158855663314307248564672270992655898765245315209640350330617426436722217912740947742363503472165053268878901966182223258841199523
46
((60875270318982690558332323876177366427463354505403579831978101215190548811200209727363828523563400032455008962530229969763415961676392830946926168474835084419,1)::nil)
98180121360204196485381931965065762684505176586247729797602170409678624213904703464075837984517350379820671409377372825645167538109513516920365987043170048310
780744546291996472639337285428078896675422713562273970274672149328802916438949087774992239883318538497504569174639073321514760659124708864696089471521893007252
0
2011731511704766787600473772363108751072204050782039248717517547630075350441039446144871215467057196555189031714970861778451332373041109995891916206878397186998)
::
(Ell_certif
60875270318982690558332323876177366427463354505403579831978101215190548811200209727363828523563400032455008962530229969763415961676392830946926168474835084419
2439612198
((24952847165171737085376027405884189806573247222878322332432484917092773452020671171073871626133007958181685316077599122089079636359706263960786472931,1)::nil)
60875270318982690558332323876177366427463354505403579831978101215190548811200209727363828523563400032455008962530229969763415961676392830946926168474835055589
1668296
155
961)
::
(Ell_certif
24952847165171737085376027405884189806573247222878322332432484917092773452020671171073871626133007958181685316077599122089079636359706263960786472931
8596
((2902844016422956850322944090959072802067618336770395804145240218368168154063176614410510596673120970257693254343283172590310386364436927324191409,1)::nil)
0
14523336826603862600472765951081032348357085297690898545048594736901653298246406267539089344897727288160434031623290114028409632099985286445923991137
12476423582585868542688013702942094903286623611439161166216242458546386726010335585536935813066503979090842658038799561044539818179853131980393237760
7797764739116167839180008564338809314554139757149475728885151536591491703756459740960584883166564986931776661274249725652837386362408207487745819339)
::
(Ell_certif
2902844016422956850322944090959072802067618336770395804145240218368168154063176614410510596673120970257693254343283172590310386364436927324191409
8748
((331829448608019758838928222560479286930454771007132579349021515588496588584165671021534044465066226288846612467077805602145943841406055527887,1)::nil)
1673188819959506846397899534620548159516879166700047504358217150231790750388303668647534503354142705227126186445258120173257630786183843679387244
2260613407613517629933218179629112983800016737481421089390368695384628661139978718970467828299403269050655475221262437910428225254892032033080132
280154498721302900703894164451001422930310857606778901728111193711432491389386820940556347332038819530369006611169508342866388310669658557171259
2204991337158580318292726797166011165749595789290351857107920015177525318984751563828632018688014313125178201830827385392241996973535746816675089)
::
(Ell_certif
331829448608019758838928222560479286930454771007132579349021515588496588584165671021534044465066226288846612467077805602145943841406055527887
332048090
((999341536968394423949037690776897066116100143828963387047404837017724208581766284926528199284735996711233844134219791681471370637379,1)::nil)
179820567841700309685722067294223206082471213838673361750679749883909472965279043814460114590254525398124070963356329096057187611444043723957
43721722561614774697614510285152164080671752243467669131544240819084785886319869394860803041733999186136583889401579138689749597227691356381
12241089697157202441383130981937420268710537242725502410246346051381648007060151768942247993561908856526302385948985343493749332215038269939
211279259235337418225013098293901494181469890416408677964041574657253821605745839017817668365342469300283887744969259137713983185582587921856)
::
(Ell_certif
999341536968394423949037690776897066116100143828963387047404837017724208581766284926528199284735996711233844134219791681471370637379
202113623
((4944454125036363451606810743167456189314364741405696275344115903643913394069489528313955006538901685913428676796786968360001,1)::nil)
999341536968394423949037690776897066116100143828963387047404837017724208581766284926528199284735996711233844134219679787638922836899
14406462054002124060149776
0
3795584547076)
::
(Ell_certif
4944454125036363451606810743167456189314364741405696275344115903643913394069489528313955006538901685913428676796786968360001
3212
((1539369279276576417063141576328597817345692634310615278749724794824333435446378039782524570840696599264800268879942113973,1)::nil)
4499835011473351277445164104830357788491288967833671977169868196740242243653778914538285681240960303956842494541682140003214
914445826993403888221514175962098438211976441308739446576738625919072759637368843097180650324537004929777159363035738798424
3210544792958381217990022132926650041036924911043337438221588473817056958874082052061963734538589523010753163699459460472276
791102667095481039165501552975227463729426242995620783999176270790556860857283020165525758998735242477272319780924511635389)
::
(Ell_certif
1539369279276576417063141576328597817345692634310615278749724794824333435446378039782524570840696599264800268879942113973
698
((2205400113576757044503068160929223234019616954599735356374960346485421125713523683113618099388737370665743560289365341,1)::nil)
2178
0
99
1089)
::
(Ell_certif
2205400113576757044503068160929223234019616954599735356374960346485421125713523683113618099388737370665743560289365341
207909
((10607525954031605387467921835655133900021725632847713934341009801243453517087755916345692272173019718843595909001,1)::nil)
148441967051525337102147044911096714290222960000773796396168205441851366282590518630015367726568855900152838294710442
53505080809324034644870762393214842527523005831164737911421755618927851705219651632497337096457015205085176390186135
0
1707918645713915877824553110616887037874477936752155698347706145990597102176903535456877328753332324632037878825605862)
::
(Ell_certif
10607525954031605387467921835655133900021725632847713934341009801243453517087755916345692272173019718843595909001
4332
((2448644033709973542813463027621222045249705824757090012525035206892133213918955024642905712133061156935251503,1)::nil)
0
5832
9
81)
::
(Ell_certif
2448644033709973542813463027621222045249705824757090012525035206892133213918955024642905712133061156935251503
240818
((10168027446910004828598622310712745912887349885627694008110108690203989349199298180028249966107564729691,1)::nil)
1041328242434004707001783073961444595134776769754679970538498503830979499709852316440036594853343541719719290
1443670614985331564239325565304200964311465793598923786895048226144513543668209270474189781053798931654086573
0
1259359203432411596323830909232651927841975623544522106028242646721009041745244529294895145524317334671405042)
::
(Ell_certif
10168027446910004828598622310712745912887349885627694008110108690203989349199298180028249966107564729691
1597266
((6365894877190151689573698000654083861352680070587929188258185013542956980044975632380799653110171,1)::nil)
10168027446910004828598622310712745912887349885627694008110108690203989349199298180028249966107564635611
9834496
0
3136)
::
(Ell_certif
6365894877190151689573698000654083861352680070587929188258185013542956980044975632380799653110171
415
((15339505728169040215840236146154418943018506194189457051704405635960591294995518450466673992901,1)::nil)
323058255936179860769198787143004320459119885840775923712592557103908299651252154594413527847526
222479777988981226347503036044130744750304647537261840975891466740304672843943587727814311766442
0
2495112319627902228826269501700353535861581700371053575527882917552713670220621169684282544802398)
::
(Ell_certif
15339505728169040215840236146154418943018506194189457051704405635960591294995518450466673992901
420
((36522632686116762418667228919415283197663109986450354867722456197963962544747801770187209381,1)::nil)
2477401738329348623978937198650306251326396555617551737757307912166917789712999487475742626435
6285225998740462305330779210639776163448899591322926151686135082164498868572480567574694125467
0
8729329438110176576410162632027018729822315394802970328997916883034888864262742282911383488252)
::
(SPock_certif 
36522632686116762418667228919415283197663109986450354867722456197963962544747801770187209381
2
((608710544768612706977787148656921386627718499774172581128707603299399375745796696169786823, 1)::nil))
::
(Ell_certif
608710544768612706977787148656921386627718499774172581128707603299399375745796696169786823
93
((6545274674931319429868679017816358995996973124691036907677081345592090047074708889313761,1)::nil)
608710544768612706977787148656921386627718499774172581128707603299399375745796695412202919
8234810772496
0
2869636)
::
(SPock_certif 
6545274674931319429868679017816358995996973124691036907677081345592090047074708889313761
2
((2153050879911618233509433887439591774999004317332577930156934653155292778642996345169, 1)::nil))
::
(Ell_certif
2153050879911618233509433887439591774999004317332577930156934653155292778642996345169
91365215337050
((23565323761006044366691925736135773397287354485498180482214382830855369,1)::nil)
1443364429311423176052225592203477623754896586561610617579043162670561197488399063076
0
2093542823437778193593775858122671241783330982204308724215553822861632955966623881436
1330698936131234471235966309033156889214341878251695563244827791627594423467369488113)
::
(Ell_certif
23565323761006044366691925736135773397287354485498180482214382830855369
272601
((86446211719715057416120724928139564088543125874592062207854633669,1)::nil)
0
221184
48
576)
::
(SPock_certif 
86446211719715057416120724928139564088543125874592062207854633669
2
((437778855278962123819669712572371621360918737684089063, 1)::nil))
::
(Ell_certif
437778855278962123819669712572371621360918737684089063
2488356
((175930958142228091084904938704982437683772579397,1)::nil)
67709214180110495090221112302565674033547721904615244
277545821707103076610895619172231227555051565315251558
251597498597696075022107818383978813794668579585303837
406236876543903037683356569813009784501895530347937959)
::
(Ell_certif
175930958142228091084904938704982437683772579397
1974763
((89089656906792405511397841603124530069583,1)::nil)
0
10985
26
169)
::
(Ell_certif
89089656906792405511397841603124530069583
381
((233831120490268780870489544712538903639,1)::nil)
0
1257728
272
4624)
::
(Ell_certif
233831120490268780870489544712538903639
132177
((1769075712796241259077281880028439,1)::nil)
0
75449
38
361)
::
(Ell_certif
1769075712796241259077281880028439
7607729385676
((232536624676358204437,1)::nil)
0
192
4
16)
::
(Ell_certif
232536624676358204437
1114884687
((208574597317,1)::nil)
0
275128
102
1156)
:: (Proof_certif 208574597317 prime208574597317) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
