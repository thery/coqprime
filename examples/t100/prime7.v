Require Import PocklingtonRefl.
Set Virtual Machine.
Open Local Scope positive_scope.
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
::         (Pock_certif 5765092791639237794064324215564118875390189647884942420499819425314341 2 ((11044922210593, 1)::(173, 1)::(89, 2)::(71, 1)::(17, 1)::(3, 1)::(2,2)::nil) 52328674211088681597156)
        ::(Pock_certif 11044922210593 5 ((22259, 1)::(2,5)::nil) 1260498) ::
         (Proof_certif 22259 prime22259) ::
         (Proof_certif 173 prime173) ::
         (Proof_certif 89 prime89) ::
         (Proof_certif 71 prime71) ::
         (Proof_certif 17 prime17) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
exact_no_check (refl_equal true).
Time Qed.
