Set Loose Hint Behavior "Strict".
Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime330707491243 : prime 330707491243.
Proof.
 apply (Pocklington_refl
         (Pock_certif 330707491243 2 ((55117915207, 1)::(2,1)::nil) 1)
        ((Pock_certif 55117915207 3 ((151, 1)::(149, 1)::(2,1)::nil) 54948) ::
         (Proof_certif 151 prime151) ::
         (Proof_certif 149 prime149) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime5678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678902111: prime  5678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678902111.
apply (Pocklington_refl 

(Ell_certif
5678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678902111
3708
((1531526762289075006325994879273376186956463832287879392937525803371422483249763607548277331628614140929851705355121092865609235636976545042087102468671837655040372512005812941961838587457332460593492843253211899563032101727222603679540277901924403,1)::nil)
5678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345650845247
58690283344
1956
106276)
(
(Ell_certif
1531526762289075006325994879273376186956463832287879392937525803371422483249763607548277331628614140929851705355121092865609235636976545042087102468671837655040372512005812941961838587457332460593492843253211899563032101727222603679540277901924403
4056052
((377590514689918917786555714589797218318814411720530060496642006407073302622787776771174859599584556837499052121403052245289401038425854965423881454031457259141983173536779364558446201073757113933318880703659048181614576742952722059657850971,1)::nil)
714297136044156365467443519897348070887735596479096572532015726361431567904726795737888774714486687463454213690669998360505100060935156524276194881360803386379341418421399025242231461110731021092293520349759801443770705759317768544163904230706001
1194759262273247766683635189592537622667171821822450386317613722841982659792322762760789440970394872951356840288476255767376030893385105934004558813178851603848534689936524123528942617834987800568000890559591493748971322561449565910155353054355471
899753742305838700038227103664062914372649183961188752113399728648216453796359396853878694483477338902384275597558881808004770222100567590741977781676803937728067615074905416018651898272880140659366299607182242082746710591495807609446634378068077
1361672641752096326608928521473740729162136169073717211372252571386026402946115131642525514579578996661022331244207882109754535698645163923875301810118228662710951041124279545875001233898040072023601765693913674980677924307920316857002571451804016)
::
(Ell_certif
377590514689918917786555714589797218318814411720530060496642006407073302622787776771174859599584556837499052121403052245289401038425854965423881454031457259141983173536779364558446201073757113933318880703659048181614576742952722059657850971
3956416
((95437515845128246824033598739312857474748462173980203420631704655696797966338164836856098954100012950483228285752320344094705861978146693859671936137569707401446428419820146431356518101152324830869463966730147651668094652262955634409,1)::nil)
377590514689918917786555714589797218318814411720530060496642006407073302622787776771174859599584556837499052121403052245289401038425854965423881454031457259141983173536779364558446201073757113933318880703659048181614576742952722059657707611
25690112
64
4096)
::
(Ell_certif
95437515845128246824033598739312857474748462173980203420631704655696797966338164836856098954100012950483228285752320344094705861978146693859671936137569707401446428419820146431356518101152324830869463966730147651668094652262955634409
33408995287
((2856641303495426687359082171351047054752708288889052918517109450352708476118806692352121883613710390071546490255647532312834045236195585150904776450295222512141483227864806475437083431235109653865186470670374320847700183493,1)::nil)
0
56293222236774864337613568006391568276121163235433635611388232043008658175457276915489339617457429513761591684174220202962111660776172463956290868581144632100071916763253289496620446223726566599458160386625985528913602705140770772682
47718757922564123412016799369656428737374231086990101710315852327848398983169082418428049477050006475241614142876160172047352930989073346929835968068784853700723214209910073215678259050576162415434731983365073825834047326131477818319
89472671104807731397531498818105803882576683288106440706842223114715748093442029534552592769468762141078026517892800322588786745604512525493442440128971600688856026643581387279396735719830304528940122468809513423438838736496521217786)
::
(Ell_certif
2856641303495426687359082171351047054752708288889052918517109450352708476118806692352121883613710390071546490255647532312834045236195585150904776450295222512141483227864806475437083431235109653865186470670374320847700183493
42769
((66792333313741885182236717513877973643356362993968830660457561559837931121111241608457571690095872947030477454596321269938689064664069780583875898486197601717074472310890922023362632322737385777634134039862885993688239,1)::nil)
0
16464
28
196)
::
(Ell_certif
66792333313741885182236717513877973643356362993968830660457561559837931121111241608457571690095872947030477454596321269938689064664069780583875898486197601717074472310890922023362632322737385777634134039862885993688239
52
((1284467948341190099658398413728422570064545442191708281931876183843037136944446954008799455578766787442893797499180988890950808441583721315657574605359563399319728783322001210489409968817884519306374159585076203817687,1)::nil)
11001630940329779750551907888617507573648717515092099893286916138804580850063408795011509648775148300661508756030402199899153614317914816716037696142139681918197258747379170318359807101869392619700498691132646642820998
20198825648408672998826028342197208437430071695076114576083442135185105146328065088483710634640318445529797389598350539533084360881400560443698846486282949158903499253139424255093531435293078492464579077517207586964027
37618600937699251147292732956675920943530765899289151070228003554765433253155832440839042618409169661794181216272890744337336168799762066296739165862540068727320934392433221134355785588925160481875049309481433854936204
22079925227703191807838667712537248975898865007855422975394068825179898788204729456312517766461720924424064535347056769878971527262606860473570691645651155600344693503922440479504672485405158438616754956295159409566376)
::
(Ell_certif
1284467948341190099658398413728422570064545442191708281931876183843037136944446954008799455578766787442893797499180988890950808441583721315657574605359563399319728783322001210489409968817884519306374159585076203817687
1276
((1006636323151402899418807534269923644251211161592247869852567542196737568138281311919121830390883062259321159008244768182735007373582257884349200844408156345196144952773472256577663855257593022837899701898712762147,1)::nil)
48405216664595109999490167801892168655165978367747021362952771525888537143720943440604517056024263955924841886380727348060410469310222465040696371737033139836310533755012671378919641972358081231236305466272485088123
36592008672601861824122645406011840875975047179617291266151973149786702499506343995443789164706213075408683890126074409745896978759498677419816012741170094091310101296920992133632268467378633459595076499074836262077
71410404621633546582309957236704570525727617967150394783844935065817930890659055774393375560251020702789490576469097267278893521579194741972107866080111730486647186061947311369485084764677385167932219577197038708839
475994116120195476459651745735985084897188596858037783416172880164117709053693710525824292603582643199527566339381507882634480421111240001278886689759662376842195069156456516301155312437828341856253936161331249102428)
::
(Ell_certif
1006636323151402899418807534269923644251211161592247869852567542196737568138281311919121830390883062259321159008244768182735007373582257884349200844408156345196144952773472256577663855257593022837899701898712762147
1461
((689005012423958178931421994709051091205483341267794572109902492947801210224696312059631642978017154181602394207783877952619375814473802859537888516741106727080663622801004845257167453808337247929175494376976629,1)::nil)
0
119164
93
961)
::
(Ell_certif
689005012423958178931421994709051091205483341267794572109902492947801210224696312059631642978017154181602394207783877952619375814473802859537888516741106727080663622801004845257167453808337247929175494376976629
26832
((25678481381334159918434033792078529040156654042478927106063748246414773785953201850761465525418051363357213700798888846735745291652649456989523413823164501687432846736171334781559233040773505208771176167287,1)::nil)
0
267674
23
529)
::
(Ell_certif
25678481381334159918434033792078529040156654042478927106063748246414773785953201850761465525418051363357213700798888846735745291652649456989523413823164501687432846736171334781559233040773505208771176167287
76436
((335947477384140456308990970119819575071388534754290218039454553435747210554623500062293494235936618391239397686123536858935293047723017296073429923882430454631055154951252350613021271292628103756129953,1)::nil)
20558561941120369088441167056715615906404855907256925820899841852179936140053711309055099001233774650366194916803781201654644007887946220550599694384282645295301625105583941579803437176705666459999861211954
13218100801166189949893740648990331355332893376942385008189642680060165956330939470414647946115466261721142194119733802933127052899727291137170430591510607949682874868681453353950280767628085242580815847968
0
3822195866617631961988231859911630773527766430255573385279120195027287856409693117015756668371185333933508033694438526073654623085317416159859595336770374690329863003370614327356968108781212432979917658139)
::
(Ell_certif
335947477384140456308990970119819575071388534754290218039454553435747210554623500062293494235936618391239397686123536858935293047723017296073429923882430454631055154951252350613021271292628103756129953
61272192689226180
((5482870167354267257607637759390613336353903857104278797797973605619616980776342314286416366301216061477057700645438332359796418342416129348029537550994516104206465180044756152573396239,1)::nil)
67659953930451311472990864223085735210079086295301928454075386470891537533582780581417616270315433277042711596982141108932079854678454563953901902750355311301525926783273654670910411701941988050111129
236215445039934235077159642057899705975302965515217919089250374927793327266983829420881174002799930846361953186108919699164625868861829548830700056907998742012700052704187494879558273615557748035783926
97544128060357381624668416715833574700959006474408050851385990510914959378801261649207390059647389320374380912190573807465600265401807234270419386579685850910180387549334030816556072824860146631411132
315184825620623172576840575212214728251201089291259177446652694940783026271100760879415502963393099976742725854669077585777075502164196162722609892143679673177574488701679743432306168460298045841583800)
::
(Ell_certif
5482870167354267257607637759390613336353903857104278797797973605619616980776342314286416366301216061477057700645438332359796418342416129348029537550994516104206465180044756152573396239
194732
((28155979332386393903455198731541879795585234358524940933169554082634682439333762885845245601284398028077024827928428172220063365176245497050310689161273141061795002939279058593267,1)::nil)
762899260905468864489601983943557076501699663345025861700379649834355211003995852332151530920934449661479936580674356542119847740241527963492035752737141317720041570840210603645689087
1564189009573116864938960761925120993586657234999707619894691798857261264138273392702743277053790565724655025093954516336621592814356157980837374179490821301128126406780676836773417659
0
1327131524628896662145672309848656397437126529980855703952307243318501538707559214282255953870289759283339166419526721840471774284465025344065473482613372596979583073728162966634605579)
::
(Ell_certif
28155979332386393903455198731541879795585234358524940933169554082634682439333762885845245601284398028077024827928428172220063365176245497050310689161273141061795002939279058593267
324
((86901170778970351553874070159079875912300106044830064608548006427884822343622724956312485825059682876406740368415335735560994800106085065022404473372296229374133448022542193109,1)::nil)
16297102580403566367161964673125110700317760118369207348005010103496170928485853628516659100885795580416826227855534697094261830491971166199604480411964155700961097679710305132854
6536636445010385900061730650500363025114403821087527373109046721757192020214317664514771854975574478060784040175902073064752312598585856613192410604527752179866979355098166191036
18723958261677473113221969032359998509799591022477343605424412729325203642926816818727516202943773910402699510782172369207168611714543835021497392992740387633318822038726299252410
12392785215091289308093992545568392528410735229211222486655570420290528542907148716347884089489203303174407508098491687189750993730067710907481151135018661636173825681546629808074)
::
(Ell_certif
86901170778970351553874070159079875912300106044830064608548006427884822343622724956312485825059682876406740368415335735560994800106085065022404473372296229374133448022542193109
5681705648094
((15294908987078985354203735676485140709758659221923977896590807779489052195326038834941036407011105349895577195624850121454150806394691500878317725933700221468262349,1)::nil)
15649192227089152126604771745513099261128958400016390154942046736435147395678488876588930911382710596898425904413406964028489296060830461785937761885061571583923643880159907855
72021006382704849367014271927016948086864117220247759812230819730204915185347809597296399654854317598479856772061072101302973974328990589224755862886158086708612199392930998707
21605267511875000768037874338835233475417013849847279062274051189878089270202070492821577453431468222421866913976996425629703793029421258810120077799062807200200018816214116365
79750093274589995979684677177085564231756958454345990597399863981170744492452539253482002317384008707481776769795644694229622997871356558068121152661571743664629196552844099459)
::
(Ell_certif
15294908987078985354203735676485140709758659221923977896590807779489052195326038834941036407011105349895577195624850121454150806394691500878317725933700221468262349
392
((39017624967038227944397284888992705892241477606948923205588795355839418865627650072372795655007873836503332483784614153481610258887172677098575594115652290413713,1)::nil)
8110519805877672452408941351668309151665116435581876477459802197646643366650283957772631493061835411105086386898954863802419766131699586146693455340825354003856979
5051952626727052597573051429356284845755500457427446317591548244172334823215297462340067002243093862330626927893347495957778049624359658132178084949080579481552045
3501182966284904330352645429997992189097009849133506243085794520118023478479755462501825474095325351684697846896372872594197013986874250287310583553609412621850036
8180918503687328554475709095786626533881337424955604855327324267529995745531679448569164323664595782363243626686186985681547984788715628190441643584673254417551021)
::
(Ell_certif
39017624967038227944397284888992705892241477606948923205588795355839418865627650072372795655007873836503332483784614153481610258887172677098575594115652290413713
7070268708
((5518549093175176666057383584379705005724016904924248206605614536685784314271022799462679487365861619501662014572153133417978306240365261212816969584699,1)::nil)
39017624967038227944397284888992705892241477606948923205588795355839418865627650072372795655007873836503332483784614153481610258887172677098575594115652290319633
9834496
0
3136)
::
(Ell_certif
5518549093175176666057383584379705005724016904924248206605614536685784314271022799462679487365861619501662014572153133417978306240365261212816969584699
334263
((16509601999548788427248554534542276607713138770741147559274028345003139187613275305451313764616788752931011038092192249876626277023089986833781297,1)::nil)
0
500
5
25)
::
(Ell_certif
16509601999548788427248554534542276607713138770741147559274028345003139187613275305451313764616788752931011038092192249876626277023089986833781297
1213690
((13602816204754746621664967606672442392796462664058489036964981457376380443666769252122027096738169080265052049605013793420575426095548154573,1)::nil)
448
0
8
64)
::
(Ell_certif
13602816204754746621664967606672442392796462664058489036964981457376380443666769252122027096738169080265052049605013793420575426095548154573
55755347
((243973303668162026175982145832083914620717232090018003779350193217816180361146579494385725025508722466098810493939484168513002672357,1)::nil)
13602816204754746621664967606672442392796462664058489036964981457376380443666769252122027096738169080265052049605013793420463532263100354093
14406462054002124060149776
0
3795584547076)
::
(Ell_certif
243973303668162026175982145832083914620717232090018003779350193217816180361146579494385725025508722466098810493939484168513002672357
260
((938358860262161639138392868584938133156604738807761552997500743143205118073620192660435960539178911597691135126575280479053913361,1)::nil)
100
0
20
100)
::
(Ell_certif
938358860262161639138392868584938133156604738807761552997500743143205118073620192660435960539178911597691135126575280479053913361
144
((6516380974042789160683283809617625924698644019498344118038199605554866528881861084368276474613330180478085635203691765991371547,1)::nil)
0
78608
17
289)
::
(Ell_certif
6516380974042789160683283809617625924698644019498344118038199605554866528881861084368276474613330180478085635203691765991371547
46
((141660455957451938275723561078644041841274869989094437348656513150285639608662452706568118337596520136063783505875449325254677,1)::nil)
2174199106881120459816490674971635584521992164021939444662492154997427362212394105153390335578541228429460578998741812232774103
3365507249737308274864123182445826111892182721278256295310074573542643764676353332898894708904641833713147729354063455287990922
470851323200288803558706463548727975155661405543024749340630378299556029611505390542947393950524523266068502175782782362524979
3127521875946249672704339738286748819392024753481397756381025784981019359461229198495424014585180531383110066010970833484918005)
::
(Ell_certif
141660455957451938275723561078644041841274869989094437348656513150285639608662452706568118337596520136063783505875449325254677
15652
((9050629693167131246851748088336573079560111806101101287289580411858586342498361164969292056709072990725049773873655536479,1)::nil)
0
5832
9
81)
::
(Ell_certif
9050629693167131246851748088336573079560111806101101287289580411858586342498361164969292056709072990725049773873655536479
6498
((1392833132220241804686326267826496318799647861819190718265555361831229796569850625839178454417869251784841619104850289,1)::nil)
1039728455086613973433401323145200384698429834855898538075751269110026486218757301997212879452159032273818230263605379939
6989379613557521878304192711204706436494445474726618567707992677735818730365157283835400251436340859203195136299691924481
0
4242197251294288631623210645132405719736238227117727550095363290465439393554010512717998876810899601270575127201792622999)
::
(Ell_certif
1392833132220241804686326267826496318799647861819190718265555361831229796569850625839178454417869251784841619104850289
97226
((14325726988873776610025366340551872120622548102556833750905153357973331770916665978129081043537295548265452155253,1)::nil)
907648681988376276189852766435838309796896729603805418612201976370405629577284240098755619975549643219784196110386896
1248004401049069626656901437888776644838270123786462225171083949686603119545445939469611784372316534007504053825228395
15226812069270501913403396794233463213568302702045588855139234406743169521150629479421985577107458798708822126997528
172564451601818635016691709805777896906715790743782551190338386532751327440322828520281435205456210314739788450541862)
::
(Ell_certif
14325726988873776610025366340551872120622548102556833750905153357973331770916665978129081043537295548265452155253
884
((16205573516825539151612405362615239955455371156738499718318446941468393765787591459676576556363174208030165437,1)::nil)
100
0
20
100)
::
(Ell_certif
16205573516825539151612405362615239955455371156738499718318446941468393765787591459676576556363174208030165437
11671885290
((1388428100018239568529241891017182876670935065087372849256700841778774518171518421296644837192773387,1)::nil)
15697030794987221911989561532769504074466796428164003961270189181863198649965484259348139380327607673293902865
15553155482955817893944654840229875192427438356575345249573725535809827341521786882287585064112390018112632009
2535083458026674943542251354063331100554470984268029810276514199981655898535928014099240218224551814368916069
6048117110910210574753197773139501056400030399099387972108055725849462827249846886107859989817630098728432535)
::
(Ell_certif
1388428100018239568529241891017182876670935065087372849256700841778774518171518421296644837192773387
29268
((47438434468301201603431798927743025716514113198281688186192467944166995612897835401058411114443,1)::nil)
0
78608
17
289)
::
(Ell_certif
47438434468301201603431798927743025716514113198281688186192467944166995612897835401058411114443
1593
((29779306006466542123937099138570637612375463401267519671917532606855882859740097087731341711,1)::nil)
47438434468301201603431798927743025716514113198281688186192467944166995612897835401057870505539
4964006108754
1431
2047761)
::
(Ell_certif
29779306006466542123937099138570637612375463401267519671917532606855882859740097087731341711
3494
((8522983974375083607308843485566868234795496106349531875898626161343878134012752012048391,1)::nil)
28739290841078821007204482043129563700312783545027511872634824633825013796055195195511992224
12464868575776434745716972769003119621230050191635076021083279988667471378939177784784124852
23194925452662805499617422990227607865838139760072830534441155665012999552044310824949621353
24815782999099208202670498396842423583427818939926348036003782235351067699054664829677011299)
::
(Ell_certif
8522983974375083607308843485566868234795496106349531875898626161343878134012752012048391
1397835
((6097274695779604608060925277709363576384549104490062015458621043408646602626756861,1)::nil)
6089048696140007323824495695785015729858786800487096821992769459891332468568304669977694
5632288699038566233851870429619660770150906866484989116851712444354854955063290567497528
0
2958086091617326100224982165842348991338594659364025280392900036527013493360650530642936)
::
(Ell_certif
6097274695779604608060925277709363576384549104490062015458621043408646602626756861
1573336561230
((3875378508342098808661856648812177795160013387922165832279969875723789,1)::nil)
217826212521276822817671259733094735060529110888341866775779824805477537943966178
3197011743159270839815571144862884993862707314731879747028545701411994645609657274
1934200340812311815995791009775068134780855536014587659786716612096639633108612302
5047515779578290928095717620042258795299136643454719248463489951219833688653341673)
::
(Ell_certif
3875378508342098808661856648812177795160013387922165832279969875723789
465948
((8317190992003611580394929581867886211992808697835282334908634341,1)::nil)
0
8192000
320
6400)
::
(Ell_certif
8317190992003611580394929581867886211992808697835282334908634341
4809
((1729505300894907793802231146156764192366987457888690089864151,1)::nil)
0
500
5
25)
::
(SPock_certif 
1729505300894907793802231146156764192366987457888690089864151
2
((405430406811047691269554988139940268027939908315737799, 1)::nil))
::
(Ell_certif
405430406811047691269554988139940268027939908315737799
324605
((1248996185551817412761833574662425555862510374593,1)::nil)
405430406811047691269554988139940268027939908266179567
134414314742
571
326041)
::
(SPock_certif 
1248996185551817412761833574662425555862510374593
2
((732565612428816637981867525933489409, 1)::nil))
::
(Ell_certif
732565612428816637981867525933489409
56862934930688
((12883007416373489101957,1)::nil)
100
0
20
100)
::
(SPock_certif 
12883007416373489101957
2
((6191836477731649, 1)::nil))
::
(Ell_certif
6191836477731649
18723
((330707491243,1)::nil)
0
1080
6
36)
:: (Proof_certif 330707491243 prime330707491243) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
