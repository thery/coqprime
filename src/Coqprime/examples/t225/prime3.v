Set Loose Hint Behavior "Strict".
Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime17635995829 : prime 17635995829.
Proof.
 apply (Pocklington_refl
         (Pock_certif 17635995829 2 ((44535343, 1)::(2,2)::nil) 1)
        ((Pock_certif 44535343 3 ((436621, 1)::(2,1)::nil) 1) ::
         (Pock_certif 436621 2 ((5, 1)::(3, 1)::(2,2)::nil) 73) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901235183: prime  345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901235183.
apply (Pocklington_refl 

(Ell_certif
345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901235183
769491819050
((449230118731264099621172949768926693959807041421103275846467682701351566198811718811591974059829871344709379627898125644776565084149816777607767004775588369487041261498479543842378411521905114854881257303056907123,1)::nil)
124445881663102992980141441993329828700792757755916489208972584684292694348231503332980696475063802670700132391809730763418228849307092893686051170798262020108386760862425820796098568749112960545080790762088761896659523951
131026675338615181436173443900925845023207361354440191835230056836934720949448339671111246934816511447755548628516382255015582144458761328052350204691850163534164437816372329660748654485505374133034640087279245732934158156915
0
302187293806124070012643261585911019718365803504328515941198123221522205791743513588444918574504433249949432003969933036584506101026612491918234852772437959902654539579210190257846502548023275021628096017067985539769480672418)
(
(Ell_certif
449230118731264099621172949768926693959807041421103275846467682701351566198811718811591974059829871344709379627898125644776565084149816777607767004775588369487041261498479543842378411521905114854881257303056907123
42907
((10469856171050506901465330826413561748894283949497827297328353944609307716661890106779592468823965118621889680958014564588784414462590283105180747927628640324939249513720119226824808592328980007352378096979167,1)::nil)
383267087166575790028778592434105405792513705314661720567716922792799599356466458893308742189643174226272362819934913854150405162994668313046687258428280644156737399962592515299495725804871755899486507387527581145
53372674622861711757032286419974895815219591744977297024497643838484399715363188822922875497250438206572026622897004377602788119811577676641037144155685897959262361441723383294451579955134489305281776227565730481
0
441749539732546044054194446488203084744193784796499728709878948571652709156070700640552462430682621672460655266787585794396153675039028273767003239294299784334404795931357576771791386017605896392668612253927134052)
::
(Ell_certif
10469856171050506901465330826413561748894283949497827297328353944609307716661890106779592468823965118621889680958014564588784414462590283105180747927628640324939249513720119226824808592328980007352378096979167
4140175048
((2528843841061308406171847163505141183802014921350211300855208174427244100588543546717107906405595321732333668269530040131077430179935360426292414212419543890675101071096407849913369770215109010717521,1)::nil)
80466900773225537429743089008610457336051370047735088329713065606358686762676186025114353418660834932573528202827698483060300135753800393270154402946512104291631576933186403199463972758592175290150729224324
8726850887121024085879889316956067399109975327605857395784316392421016913255198315638739679268554244565450015566679903140629864979444489297544288390677618150925355502517397948593337622645496618846721581117752
3922162952967870323458992535790145558085788103834404894897964752504898837986294412852819136723213907527097231889874237520251550827855998706632092730924329041531560138557868146146634588671057982053472480747170
5621982012118676031712137907935413748403627723474042844551437854718346301419681502380648593335166667282259118336980690475545880265414288800351230301421283437380336574045184318854992626746938485229359506635716)
::
(Ell_certif
2528843841061308406171847163505141183802014921350211300855208174427244100588543546717107906405595321732333668269530040131077430179935360426292414212419543890675101071096407849913369770215109010717521
1282376258282820
((1971998331010576022529135168075960414082129550030630262585183734400440246473598574849351864300268123522943778726280721024523022416890104495793969993668385765482613804754715274628617177,1)::nil)
1643844500198762331838959387205386522834229148223734866553821085822380086658973693208946482582063294799039248721476062273890335103629520102837338401438628787229097965374577875365352379915304706188191
2151006956536226111866023169972710311676957186432861905241044536811248525724981615949947664638469356998189707158380634350449995651391232827062841564911466745195336203311556524688592953143566071799694
1214336070996724237616579679273612714085949274473119132748379329383327276525253954642199137240864186539755219605724316166350207436146763399168213352267855136641889376291929008025688953665953258241482
1936378938707695704012786731646372802443459919571945009863686696999919100219560724738349619611615923804189214971654125744599372559040905589309257086330966483060838524058062633946162686798469677746135)
::
(Ell_certif
1971998331010576022529135168075960414082129550030630262585183734400440246473598574849351864300268123522943778726280721024523022416890104495793969993668385765482613804754715274628617177
130
((15169217930850584788685655139045849339093304231004848173732182572311078819027681344995014340732331851328231572749685315404278152084112514162700437274507695753018690208815595512553753,1)::nil)
279112764381425310037602882797430341704686017458244112688558424137134968482089563067218621468372052849119862183323747078445586960123577803804976938794956335421661957651806180671859507
0
947080339555753253848759195555336030563285134584697231331419927187169381361379558063704801585016305156367205306849961558709735720476535621346868793765177928702375464332339900505373447
285460298413662377780016591350385030441031247264192931991496946965306769479244158927195581978014442869587576349913179348329552425011752969994893341591923710040541017567038374753475317)
::
(Ell_certif
15169217930850584788685655139045849339093304231004848173732182572311078819027681344995014340732331851328231572749685315404278152084112514162700437274507695753018690208815595512553753
1265391344
((11987768055137403238539661718316487345193428343069848100472056471022516192451274856353857236716653506030806104669528593592818700419651974800639878510968577578061798188982799,1)::nil)
4246986556907132668801270405233312987396105059534596106897289145637182298631296365157823594223382781779737185282214189720660959349502995613175918237035788882432527464748665175127378
9063510675812246076067819995192997647544230640176684012720630270999750870571021888954673857871828172970820168349308145050391399514237793966440486378321496717470828136475178187904191
0
12970374098180014491772575810180874152253782116107513086539748651084513923611625374635168616519921720112527492946662976033579770458501526378775220904455926725708751198996614732245438)
::
(Ell_certif
11987768055137403238539661718316487345193428343069848100472056471022516192451274856353857236716653506030806104669528593592818700419651974800639878510968577578061798188982799
379
((31629994868436420154458210338565929670695061591213319526311494646497404201718403314917399530584197727145480144205934468255473163683258109556075988660608278078552372921523,1)::nil)
6575443628797878804595807807727244672346302596908267578509264584788121169848231446072432859476437784503696454431074285487237030619684737147145257809738992778218516218798074
1504877936793656416907349723629076610575709556764394690411989170274424078976551601564992000946557726899749867266568584720312169380991945997770472913909834500846085337894028
6764261568801727784664791795017156955518773771201862634071428169557955833306022824734871444983519734284808331027698515236235936862694177761097075627426755200724761373229789
8822118492239469085006208840403935991127959969725162315156962888878908813995987372151521845272326032424325939306676715653121536485547993654547243731656534809504510655867911)
::
(SPock_certif 
31629994868436420154458210338565929670695061591213319526311494646497404201718403314917399530584197727145480144205934468255473163683258109556075988660608278078552372921523
2
((405512754723543848134079619725204226547372584502734865721942239057659028227159016857915378597233304194172822361614544464813758508759719353283025495648824077930158627199, 1)::nil))
::
(Ell_certif
405512754723543848134079619725204226547372584502734865721942239057659028227159016857915378597233304194172822361614544464813758508759719353283025495648824077930158627199
662750
((611863832098896790847347596718527689999807747269309491847517524040224863413291613514492918782706357888441333789299764246779654493593104232976557364920945220158013,1)::nil)
404727180602277411437641911707902572422006807823395915397943342474987673557927103099251386670575187570413152581262617130822369590427108776605461745245976222115154746544
202392708672416856108076851538340863271792428423057986884442320581670803528534111123756735824918170515248187793520542687068392553329901276629417309429692929750016801841
9483106952429223520863480326285369522611346825026215180642268814767942095298534377168015930619172144126026037041882610350349401695283082464925170661402924038306102144
9528000630193138904837593279029978658911890681452880840180418210288983148884804912136040169939359183220611614781481890693113803635402054786731532955221216795986464907)
::
(Ell_certif
611863832098896790847347596718527689999807747269309491847517524040224863413291613514492918782706357888441333789299764246779654493593104232976557364920945220158013
5480
((111653983959652699059734962904840819343030610815567425519619986138727164856440075174263047780257620491421479838330815741758955859585292232603801300620996727977,1)::nil)
611863832098896790847347596718527689999807747269309491847517524040224863413291613514492918782706357888441333789299764246779654493593104232976557364920945220157977
0
12
36)
::
(Ell_certif
111653983959652699059734962904840819343030610815567425519619986138727164856440075174263047780257620491421479838330815741758955859585292232603801300620996727977
668
((167146682574330387813974495366528172669207501220909319640149679848393959365928230030298484471789165746336131460391303820769301157381916842613294835817083893,1)::nil)
45888141940099206252906489264842993912950930964559650087201304044338995517694802696601084481297933763474207781994317069724717176693608175090692515274183602304
51531882839843249402638021905161988694142820076191654845210654707319088657835199247850595323452216795495608391332112402955628491538296534194620860169512762669
102998828914448544603769224331479480084938025419779004897653784105430956012641654034828232777765238609000712226359539548630786218389085780979836262932445630681
104392591252030365115004548444986629221317339108487953196128646915181040899322704762602367725702847126042238723491523568794906461141976913902380914372311285817)
::
(Ell_certif
167146682574330387813974495366528172669207501220909319640149679848393959365928230030298484471789165746336131460391303820769301157381916842613294835817083893
108175642
((1545141581635636493971299891767946916083081820035875725518224147432320848772305342544526608622508707634314764247947084049957011024978118368518294997,1)::nil)
27703586279407379826310193786492823150073816306007051196414163235319584162902108051493218515538216616809963748498082317083776411869020051524251216154259641
14915165343020793875897710919361594803586927065595134100002213365575102324773985239650562795352441900995890998221750967151639515161699663743812681866833752
80371859407540301784689565862549661424792195286126016731637473086988635791542811426392524697245628988741522743418660596189722641731810088385063616052504008
83707879986804877257187816424707390021349647080197241023342461904742335292217388525414050373170051376980871693283107781858929551568014931090288045311406997)
::
(Ell_certif
1545141581635636493971299891767946916083081820035875725518224147432320848772305342544526608622508707634314764247947084049957011024978118368518294997
468
((3301584576144522423015598059333219906160431239392896849397914844940856514432200080849831620741218816263724247745301198980124940140258532354250203,1)::nil)
0
78608
17
289)
::
(Ell_certif
3301584576144522423015598059333219906160431239392896849397914844940856514432200080849831620741218816263724247745301198980124940140258532354250203
63
((52406104383246387666914254910051109621594146657030108720601822935569150973100951226138593879158926754443301086952882081059215297036892994743879,1)::nil)
0
78608
17
289)
::
(Ell_certif
52406104383246387666914254910051109621594146657030108720601822935569150973100951226138593879158926754443301086952882081059215297036892994743879
93336
((561477933308116778808972474822695526073478043381225986978248724346116723631183356652472559096466785707141053213975652254240757039051385269,1)::nil)
19815182144583986386229440813140995733007963363391089103185144442517649067155715756709652163006824664855287859603990478330944833998471338754113
36115130047030536014740385111922189899640636436520706619654885013180680565113169005397847113296610698741260918693072760592510207724820990593943
0
43263764928469982709432810305104625607779496411239126628067691372234454456135089458878473727181961901328747988572938861155904608940387951402386)
::
(Ell_certif
561477933308116778808972474822695526073478043381225986978248724346116723631183356652472559096466785707141053213975652254240757039051385269
10269428
((54674703723334617936750953882017141176069206910182922259959242554319017186642657163226860538648296290973589814897887977901819702757,1)::nil)
16900
0
650
16900)
::
(Ell_certif
54674703723334617936750953882017141176069206910182922259959242554319017186642657163226860538648296290973589814897887977901819702757
17452
((3132861776491784204489511453244163487054160377617632492548661617838372925898607602552471810086875373725594522373269833946900189,1)::nil)
0
2058
7
49)
::
(SPock_certif 
3132861776491784204489511453244163487054160377617632492548661617838372925898607602552471810086875373725594522373269833946900189
2
((9002476369229264955429630612770584732914253958671357737208797752409117603156918398139286810594469464728719891877212166514081, 1)::nil))
::
(Ell_certif
9002476369229264955429630612770584732914253958671357737208797752409117603156918398139286810594469464728719891877212166514081
130000
((69249818224840499657151004713619882560878876605164290286221519872300666320719737173496606734338308459787247859233805729,1)::nil)
100
0
20
100)
::
(Ell_certif
69249818224840499657151004713619882560878876605164290286221519872300666320719737173496606734338308459787247859233805729
92
((752715415487396735403815268626303071313900832664829242241533450508678278650272795247652758240257497952229036097027093,1)::nil)
51348241047762311716992418656534726416224924915424702704984217678960981392493763901139155866080542758844246364459746935
43499492681395654153446540479559529888909456170118151178558219112603012537097329053523738206381853438328685211579341817
31272396086192433102547034120724425891829143895070368089567032258090799993308489242444248961642990652701159650226346039
28775241267287205817641596427654049127982340483429664211956562790315014803540708390710320342337164637397577474180201120)
::
(Ell_certif
752715415487396735403815268626303071313900832664829242241533450508678278650272795247652758240257497952229036097027093
63
((11947863737895186276251036009941318592284140201029035591134586468629092899982820795747136599822714875178404563431043,1)::nil)
0
44851536
705
19881)
::
(Ell_certif
11947863737895186276251036009941318592284140201029035591134586468629092899982820795747136599822714875178404563431043
6672018646
((1790741958591220980867000414246342109560726218784166687883707832333651202751408380258183056000783792829781,1)::nil)
7206623654802118701452606067573241362968504354070564786859943917929411463104043014908804995538689358983122116245398
1461397753074821423538112658713926962594311269749693707272352366601783723178932320758984604114158627407902626972317
0
7394965319342455083597424898594620769821301185041672334329312639583670280714214884934510033333964069157399283627597)
::
(Ell_certif
1790741958591220980867000414246342109560726218784166687883707832333651202751408380258183056000783792829781
187972
((9526642045577112446891028526835603757797577398677285719536837511494924142627984429398474990937688337,1)::nil)
16900
0
650
16900)
::
(Ell_certif
9526642045577112446891028526835603757797577398677285719536837511494924142627984429398474990937688337
17865397
((533245471431567540698425482894984296055529994585477257834253270308230444281572038477920052349,1)::nil)
9526642045577112446891028526835603757797577398677285719536837511494924142627984429398457754274870097
27544082901737469648
141572
5010657796)
::
(Ell_certif
533245471431567540698425482894984296055529994585477257834253270308230444281572038477920052349
3402650
((156714758036109367903964698953752015651192451337178727682679643413926989938709126660553,1)::nil)
18
0
3
9)
::
(Ell_certif
156714758036109367903964698953752015651192451337178727682679643413926989938709126660553
956566
((163830575241132726757970384640215119135733908429509309148023140677606278022896727,1)::nil)
36174062834845159614555764645019780681194640792986943019820008528921823880629744721396
41612532293862791104224131835787714236639281519113040181987353910918348506060478724527
0
89806173503847097370147551349939235028268053553333635507546213975245734927639634626182)
::
(Ell_certif
163830575241132726757970384640215119135733908429509309148023140677606278022896727
16041
((10213239526284690901936935642429718791579850817865893771518194227645392175803,1)::nil)
0
8586756
645
16641)
::
(Ell_certif
10213239526284690901936935642429718791579850817865893771518194227645392175803
3770523001
((2708706331608634815469445704736524107321718666005186905095404963961,1)::nil)
0
265625
50
625)
::
(Ell_certif
2708706331608634815469445704736524107321718666005186905095404963961
644241
((4204492312051910411584245188891309745792345482063732794864051,1)::nil)
0
99144
18
324)
::
(SPock_certif 
4204492312051910411584245188891309745792345482063732794864051
2
((227885762170835252660392693164840636628311408241936736849, 1)::nil))
::
(SPock_certif 
227885762170835252660392693164840636628311408241936736849
2
((795789784037148505245070143264382634396205013459, 1)::nil))
::
(Ell_certif
795789784037148505245070143264382634396205013459
2144988
((370999643838169959573232661161584240526957,1)::nil)
0
78608
17
289)
::
(Ell_certif
370999643838169959573232661161584240526957
2821
((131513521388929443308907555300744597853,1)::nil)
0
16464
28
196)
::
(Ell_certif
131513521388929443308907555300744597853
6578726640393
((19990725953172160992863227,1)::nil)
0
6912
24
144)
::
(Ell_certif
19990725953172160992863227
11116
((1798374051203765434969,1)::nil)
0
1080
6
36)
::
(Ell_certif
1798374051203765434969
14668
((122605266643249711,1)::nil)
0
611166181463850315363
899187025601882717672
786788647401647386588)
::
(SPock_certif 
122605266643249711
2
((17635995829, 1)::nil))
:: (Proof_certif 17635995829 prime17635995829) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
