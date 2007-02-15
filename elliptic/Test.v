
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)


Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import ZnZ.
Require Import W.
Require Import Mod_op.
Require Import NEll.


Definition exx := mkEx
  329719147332060395689499
  8209062
  (List.cons (40165264598163841%positive,1%positive) List.nil)
  (-94080)
  9834496
  0
  3136.

Lemma xHdiv: forall p, ~(2 | xI p).
intros p HH; inversion HH.
generalize H; rewrite Zmult_comm; case q; simpl;
  intros; discriminate.
Qed.

Definition exx2: ex_spec exx.
constructor; simpl; auto.
apply xHdiv.
2: unfold ZEll.Zmullp, Zpower_pos; red; simpl; auto.
Admitted.

(*
Eval vm_compute in 
(@npowl1_prime exx exx2 _ (cmk_op 5) (cmk_spec 5)
  (@make_mod_spec _ _ (zN exx (cmk_op 5)) ((refl_equal Lt): 1 < znz_to_Z (cmk_op 5) (zN exx (cmk_op 5))) (cmk_spec 5))
 (refl_equal 0%N)).
*)

Set Virtual Machine.

Theorem foo: prime 329719147332060395689499.
assert (Hu:= ((refl_equal Lt): 1 < znz_to_Z (cmk_op 5) (zN exx (cmk_op 5)))).
assert (U := (@npowl1_prime exx exx2 _ (cmk_op 5) (cmk_spec 5))).
assert (U1 := (@make_mod_spec _ _ (zN exx (cmk_op 5)) Hu (cmk_spec 5))).
assert (U2 := U1 ((refl_equal 0%N):mod_spec (cmk_op 5) (zN exx (cmk_op 5))
    (make_mod_op (cmk_op 5) (zN exx (cmk_op 5))))).

 (refl_equal 0%N))).

intros HH.
assert (H1:= refl_equal (1 + 2)).
exact_no_check HH.
eval vm_compute in H1.

intros HH; generalize (HH (refl_equal 0%N)); clear HH.
intros H
Qed.
simpl.

intros HH.
generalize (HH ((refl_equal Lt): 1 < znz_to_Z (cmk_op 5) (zN exx (cmk_op 5)))).
simpl.
unfold Zlt; simpl.
Check (zN exx (cmk_op 5)).
generalize (@npowl1_prime exx exx2 _ (cmk_op 5) (cmk_spec 5)).
unfold mop.
Definition zZ := word W8_basic.w8 l.
znz_spec (cmk_op 5) ->
 mod_spec (cmk_op 5) (zN exx (cmk_op 5)) (mop exx (cmk_op 5)) ->
 
(*
Definition exx := mkEx
  1384435372850622112932804334308326689651568940268408537
  13077052794
  105867537178241517538435987563198410444088809
  (-677530058123796416781392907869501000001421915645008494)
  0
  (-169382514530949104195348226967375250000355478911252124)
  1045670343788723904542107880373576189650857982445904291.
*)  

Time Eval vm_compute in SR.


Time Eval vm_compute in  (test exx (cmk_op 6)).
(*
Eval vm_compute in exx.(vN) * exx.(vN).
Eval vm_compute in op.(znz_to_Z) (op.(znz_mul) zN zN).
*)


Time Eval vm_compute in zpow (c1 6) (pp  6) SR.
Time Eval vm_compute in (zpow c1 pp pR).
