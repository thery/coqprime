From Stdlib Require Import List.
From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.
Import ListNotations.
Require Import factn94.

(******************************************************************************)
(*                                                                            *)
(*                       Factorial Primes                                     *)
(*                                                                            *)
(******************************************************************************)

Definition Zfact z := 
  match z with 
  | Zpos n => 
    Z.of_N (N.peano_rec
            (fun _ : N => N) 1%N (fun n f : N => ((n + 1) * f)%N) (N.pos n))
  | _ => 1%Z
  end.

Definition Pfact := 
 Pos.peano_rec 
 (fun _ : positive => positive) 1%positive (fun n f => ((n + 1) * f)%positive).

Definition Zfactp z := (Zfact z + 1)%Z.
Definition Pfactp z := (Pfact z + 1)%positive.

Definition Zfactn z := (Zfact z - 1)%Z.
Definition Pfactn z := (Pfact z - 1)%positive.

(* The positive ones : !n + 1 is prime
    1, 2, 3, 11, 27, 37, 41, 73, 77, 116, 154, 320, 340, 
    399, 427, 872, 1477, 6380
*)

Lemma Zfactp1 : prime (Zfactp 1).
Proof. exact prime2. Qed.

Lemma Zfactp2 : prime (Zfactp 2).
Proof. exact prime3. Qed.

Lemma Zfactp3 : prime (Zfactp 3).
Proof. exact prime7. Qed.

Lemma Zfactp11 : prime (Zfactp 11).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 11) 13 ((2,8)::nil) 272)
        ((Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp27 : prime (Zfactp 27).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 27) 31 ((3, 5)::(2,23)::nil) 834880196)
        ((Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp37 : prime (Zfactp 37).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 37) 43 ((3, 9)::(2,34)::nil) 649828339463582)
        ((Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp41 : prime (Zfactp 41).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 41) 43 ((3, 11)::(2,38)::nil) 9435315418112004)
        ((Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp73 : prime (Zfactp 73).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 73) 79 ((3, 30)::(2,70)::nil) 321994900686544973640015819443189360)
        ((Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp77 : prime (Zfactp 77).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 77) 89 ((3, 33)::(2,73)::nil) 43027210892808563300877888879696436848)
        ((Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp116 : prime (Zfactp 116).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 116) 131 ((5, 5)::(3, 55)::(2,112)::nil) 4734510491385311194344115983013161451519826419821023843148934373)
        ((Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp154 : prime (Zfactp 154).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 154) 163 ((5, 15)::(3, 73)::(2,150)::nil) 5244725022200306586071817561612387840194817732901177821263031898529020044932826507568359373)
        ((Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp320 : prime (Zfactp 320).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 320) 353 ((5, 74)::(3, 155)::(2,318)::nil) 73124736908546630847393483259571787584538305950632078244347210708266610697985160828973415804791792296807877776366708968860803960261167592147156421615834961577836077137295719717164436610277285213671428153841552968511104366)
        ((Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp340 : prime (Zfactp 340).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 340) 347 ((5, 82)::(3, 167)::(2,336)::nil) 3318419133257294624588212105471131489572844556338393052288198346874250577356158308558838654016845307013158383316037328326657518024437411580067604174953221038430136991114353191145328644642425401519283302398321487189263397459078168463320878)
        ((Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp399 : prime (Zfactp 399).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 399) 409 ((7, 11)::(5, 97)::(3, 196)::(2,393)::nil) 6952298334705500709873285838715305045562840349932509190563476580258043884496738755761844967345261646703794419215502838162415377912996949357737864253218998205230262928196008225290850576444050643701225541217148439428241495675277408000450041428686669229114123380277630242529713144204663660718)
        ((Proof_certif 7 prime7) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp427 : prime (Zfactp 427).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 427) 449 ((7, 16)::(5, 104)::(3, 210)::(2,421)::nil) 25461136184959533546167477131568471289821636552662586987037498209879087588003070041157087088612129003977234754787204167032687892523886593584371677755574052392948922456172467840412222414579487920254262835159757215960557638101330988699550997263657788247638971416367949122612506889758064838005899648474657945555065783)
        ((Proof_certif 7 prime7) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactp872 : prime (Zfactp 872).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 872) 877 ((7, 132)::(5, 215)::(3, 432)::(2,867)::nil) 1047926738867069403328243594038978278643816167152135663512822386968878005004633841241022213842746270494318432945275402970394168913481247542999298632892651522108723354386461535174534117531281567752751488191780189822730695146114811689042854056532744479581731886832030431405691859903942583277481639461637219822411837244270791002130930636707733733194777239551472932546219146119719508369116940308774686965128884204732398697952243048921215075459455239519606149543125361072485777404232909077272508847927598960790992868186712222132993338749955649302250909581151131139330209891947929068071848445790188433654848443317593565426298176146741580600317434587083739603496232077265427819605001750496751846775654374570426497054732862395358026385506)
        ((Proof_certif 7 prime7) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.
(*
Lemma Zfactp1477 : prime (Zfactp 1477).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactp 1477) 1481 ((11, 87)::(7, 244)::(5, 367)::(3, 736)::(2,1471)::nil) 1892547634346877801814628199998195232086014530120526716124023096878553223593724358869959005726575549970710125230340923349741003839188613425030748043836280081703349880489397637889435956763611284306706907076663634502887410831207024197181722433752994266264902986863200459871631297023659514451029538562511221841597208514482123488022701396661849304723687060258143604366577855795005922918418166124324888008520212812110304559012372242175280817409460639910833569810636257864963793383995059571761552040177481368586514418016727581604875075413236514841937090900179305143152088736510623695584990254486575714811026761212640885320207910260958488391515542408296012302136255744758171668587640419281890301174411132708411355501167104946017756303357443121364229037121368379424270700588942920636498673862539781262257216789869098971625993253213093308040060313910510796137860017697306424125951005763122957527531276070845292499606664496937999296397367721263977739872206210585093874801223436839344409044053664168093996957819226390861606901282075717849039333237524276853495924016522722913224226355539631620885754921402773576749027018952778339117844380153220351830180749005164250585070186890310545292485192920518599121357196711160172935309550047912557532013561455834051414128643858132667038117973710753322144283527551832417110254314886578427673048239882678988855475572779231)
        ((Proof_certif 11 prime11) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.
*)

(* The negative ones : !n - 1 is prime
    3, 4, 6, 7, 12, 14, 30, 32, 33, 38, 94, 166, 324, 
    379, 469, 546, 974, 1963, 3507, 3610, 6917, 21480, and 34790 
*)
Lemma Zfactn3 : prime (Zfactn 3).
Proof. exact prime5. Qed.

Lemma Zfactn4 : prime (Zfactn 4).
Proof. exact prime23. Qed.

Lemma Zfactn6 : prime (Zfactn 6).
Proof.
apply (Pocklington_refl
         (Pock_certif 719 11 ((359, 1)::(2,1)::nil) 1)
        ((Proof_certif 359 prime359) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactn7 : prime (Zfactn 7).
Proof.
apply (Pocklington_refl
         (Pock_certif 5039 11 ((11, 1)::(2,1)::nil) 6)
        ((Proof_certif 11 prime11) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactn12 : prime (Zfactn 12).
Proof.
apply (Pocklington_refl
         (Pock_certif 479001599 13 ((4518883, 1)::(2,1)::nil) 1)
        ((Pock_certif 4518883 2 ((67, 1)::(2,1)::nil) 220) ::
         (Proof_certif 67 prime67) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactn14 : prime (Zfactn 14).
Proof.
apply (Pocklington_refl
         (Pock_certif 87178291199 17 ((431575699, 1)::(2,1)::nil) 1)
        ((Pock_certif 431575699 2 ((347, 1)::(2,1)::nil) 1) ::
         (Proof_certif 347 prime347) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactn30 : prime (Zfactn 30).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactn 30) 43 ((20594988459756689859259, 1)::(2,1)::nil) 1)
        ((Pock_certif 20594988459756689859259 2 ((22571261, 1)::(2,1)::nil) 53411076) ::
         (Pock_certif 22571261 2 ((761, 1)::(2,2)::nil) 1326) ::
         (Proof_certif 761 prime761) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactn32 : prime (Zfactn 32).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactn 32) 37 ((949811, 1)::(127951, 1)::(67, 1)::(2,1)::nil) 5556805370996)
        ((Pock_certif 949811 2 ((19, 1)::(5, 1)::(2,1)::nil) 58) ::
         (Pock_certif 127951 3 ((5, 2)::(2,1)::nil) 57) ::
         (Proof_certif 67 prime67) ::
         (Proof_certif 19 prime19) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactn33 : prime (Zfactn 33).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactn 33) 41 ((1570143494597312303, 1)::(2,1)::nil) 1)
        ((Pock_certif 1570143494597312303 5 ((102449660354777, 1)::(2,1)::nil) 1) ::
         (Pock_certif 102449660354777 3 ((1829458220621, 1)::(2,3)::nil) 1) ::
         (Pock_certif 1829458220621 2 ((149239, 1)::(2,2)::nil) 676820) ::
         (Pock_certif 149239 3 ((8291, 1)::(2,1)::nil) 1) ::
         (Proof_certif 8291 prime8291) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactn38 : prime (Zfactn 38).
Proof.
apply (Pocklington_refl
         (Pock_certif (Pfactn 38) 41 ((1895980294180200166695525250433028941, 1)::(2,1)::nil) 1)
        ((Pock_certif 1895980294180200166695525250433028941 2 ((108048250930768147053657257, 1)::(2,2)::nil) 1) ::
         (Pock_certif 108048250930768147053657257 3 ((2957309254728709958771, 1)::(2,3)::nil) 1) ::
         (Pock_certif 2957309254728709958771 2 ((8747, 1)::(11, 2)::(7, 1)::(2,1)::nil) 4258250) ::
         (Proof_certif 8747 prime8747) ::
         (Proof_certif 11 prime11) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 2 prime2) ::
          nil)).
native_cast_no_check (refl_equal true).
Qed.

Lemma Zfactn94 : prime (Zfactn 94).
Proof. now apply factn94.primo. Qed.


