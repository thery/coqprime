Set Loose Hint Behavior "Strict".
Require Import PocklingtonRefl.


Local Open Scope positive_scope.

Lemma prime4053914317 : prime 4053914317.
Proof.
 apply (Pocklington_refl
         (Pock_certif 4053914317 2 ((6624043, 1)::(2,2)::nil) 1)
        ((Pock_certif 6624043 2 ((41, 1)::(3, 1)::(2,1)::nil) 358) ::
         (Proof_certif 41 prime41) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime7890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123653: prime  7890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123653.
apply (Pocklington_refl 

(Ell_certif
7890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123653
10460852
((754252469759538931023868919526620788006253124730718278972167741912248250564121911893610490193,1)::nil)
5711837973884804833670609687066636323072093184056713586174969642483249665305037356422406858435580528
5864824973376157764488234165361249338351528043620293388268984927406061454180414937119652693677642276
6330055507965069569110886336455501388716790303535113454240606863275824594393993716166055243703790267
6686656249294054193074581818726107163928467089018171242593247722001994028806603030371947672610942668)
(
(Ell_certif
754252469759538931023868919526620788006253124730718278972167741912248250564121911893610490193
1983
((380359288834865825024643933195471905197303643307314002479191872085676159414452866681923821,1)::nil)
754252469759538931023868919526620788006253124730718278972167741912248250564121911893069881289
4964006108754
1431
2047761)
::
(Ell_certif
380359288834865825024643933195471905197303643307314002479191872085676159414452866681923821
1165630108
((326312169035758833560126205315444636058854824155743279122140963325641791062731331,1)::nil)
313637151499851231302907976953652984456117832257646135697901903194811100931785300586057284
204090620937716585001362988602333029856974493650256664721167580993380387430660048720842363
0
194712919632394234290697224295782338978599730127751948077782169350596064601904666335472020)
::
(Ell_certif
326312169035758833560126205315444636058854824155743279122140963325641791062731331
2146105
((152048557286693257580652486861288071207529370334225203040662350004030368053,1)::nil)
209371817550697340488562184513210423052833713959921661157127008818740143056520531
167196752884304751237414052224311661970816342555911748178378246164145707756701729
0
222946114746880490872023983915294840107028453668415582397199933852944089317005350)
::
(Ell_certif
152048557286693257580652486861288071207529370334225203040662350004030368053
26374
((5765092791639237794064324215564118875390189647884942420499819425314341,1)::nil)
65644437298317324663011539370895386324918378748848230413614998772546204683
63122665259827460561961810690349622539657587030756853462869600163373992613
45298751333647943095923964431483186109868739791138029842429020730358495382
133683191535348014801026900164696011420702936759678420587917020250341459715)
::
(Ell_certif
5765092791639237794064324215564118875390189647884942420499819425314341
2132
((2704077294389886394964504791540393400367253472630376742383519887941,1)::nil)
4624
0
272
4624)
::
(SPock_certif 
2704077294389886394964504791540393400367253472630376742383519887941
2
((42080256682071061235052984617808798636278454289299357958037969, 1)::nil))
::
(Ell_certif
42080256682071061235052984617808798636278454289299357958037969
4160
((10115446317805543566118505917745577526158073480750719441653,1)::nil)
100
0
20
100)
::
(Ell_certif
10115446317805543566118505917745577526158073480750719441653
393181348
((25727177469785630741869540356890467466075961914623,1)::nil)
847815818871771120058488512568895361520663562004659206091
6030293246650983540490844248925323756749909868529593766436
0
9408003974440041714900154329254494269385904132775019829265)
::
(Ell_certif
25727177469785630741869540356890467466075961914623
26419970
((973777694289040855908221409820577458251227,1)::nil)
2964282123981597553619657781999093815919373170970
22794388619023187393464450857704686494180696161639
6042228320462774617836714127831652988066436168221
20598495339780754588293602035731056903135923582919)
::
(Ell_certif
973777694289040855908221409820577458251227
701
((1389126525376663132539066790092142602863,1)::nil)
973777694289040008075979026316993564721307
9501955807025115933281263315351902213136
0
97477976010097357444)
::
(Ell_certif
1389126525376663132539066790092142602863
38885
((35723968763704851037725820469085157,1)::nil)
1389126525376663132539066790092063367695
271737008656
0
521284)
::
(SPock_certif 
35723968763704851037725820469085157
2
((992332465658468084381272790807921, 1)::nil))
::
(Ell_certif
992332465658468084381272790807921
2155396
((460394500898427980137788937,1)::nil)
900
0
10
100)
::
(Ell_certif
460394500898427980137788937
283674432
((1622967913084201459,1)::nil)
0
192
4
16)
::
(Ell_certif
1622967913084201459
400345884
((4053914317,1)::nil)
0
221184
48
576)
:: (Proof_certif 4053914317 prime4053914317) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
