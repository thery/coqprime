Require Import PocklingtonRefl.
Set Virtual Machine.
Open Local Scope positive_scope.
Lemma prime9012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012346103: prime  9012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012346103.
apply (Pocklington_refl 

(Ell_certif
9012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012346103
13986778
((644347517269612384488416378438909400412225119649982232019901316388005468995251584871148108053,1)::nil)
6876185946935048040751473751022855964435207604826800480584663082562294790804494778730289090926002123
1287604209866173807929447190325501394628999764593900337993219613475043207272374348910703520783514130
6516846521636749360666474081337202009939996170296211414189696691120500897237814287101042700085704070
2998572055249888636204342756351637531949479794472452565652191467026302998735989403985748205493541627)
(
(Ell_certif
644347517269612384488416378438909400412225119649982232019901316388005468995251584871148108053
1497
((430425863239554031054386358342624849974766278957837438467999123730922152371746873570509403,1)::nil)
0
16099776
660
17424)
::
(Ell_certif
430425863239554031054386358342624849974766278957837438467999123730922152371746873570509403
1293660
((332719465114136659597101524622099199151837638944376508147884923943200404443549457431,1)::nil)
289975626511744866140091265861677492458656809520477876988840499632959965536640266414272794
297185428712726663958979141683738649218638291445691368309364200908337676579577162068480917
89556275673284803859411324942479193383687199311131908539246861667374500136391048012989360
395257953085467719995030050059258928938403275170021505221014856868895404968479220279853944)

::         (Pock_certif 332719465114136659597101524622099199151837638944376508147884923943200404443549457431 3 ((16807851081551, 1)::(2430947, 1)::(1588451, 1)::(5, 1)::(3, 2)::(2,1)::nil) 6932163119051278812634872398)
        ::(Pock_certif 16807851081551 17 ((20407, 1)::(2,1)::nil) 2557) ::
         (Pock_certif 2430947 2 ((89, 1)::(2,1)::nil) 127) ::
         (Pock_certif 1588451 2 ((31769, 1)::(2,1)::nil) 1) ::
         (Proof_certif 31769 prime31769) ::
         (Proof_certif 20407 prime20407) ::
         (Proof_certif 89 prime89) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Qed.


exact_no_check (refl_equal true).
Time Qed.