(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)

(* Montgomery arithmetic on the words of BigN (any ZnZ.Specs).
   With R = wB, the base of the words, and N' = - N^-1 mod R,
   mont_mul x y = x y R^-1 mod N, with three multiplications and no
   division.  make_mod_op here is Mod_op's make_mod_op whose power_mod works in
   Montgomery form, with the same name and the same specification
   (make_mod_spec): importing this file after Mod_op is enough to switch. *)

From Stdlib Require Import ZArith Lia Znumtheory Zpow_facts.
From Stdlib Require Import CyclicAxioms DoubleType Cyclic63.
From Bignums Require Import DoubleCyclic BigN.
From Coqprime Require Import Mod_op.
Import CyclicAxioms DoubleType DoubleBase.

Set Implicit Arguments.

Open Scope Z_scope.

Notation "[| x |]" := (ZnZ.to_Z x) (at level 0, x at level 99).

Section MontMul.

Variable w : univ_of_cycles.
Variable op : ZnZ.Ops w.
Variable op_spec : ZnZ.Specs op.

Notation wB := (base (@ZnZ.digits _ op)).

Variables wN wN' : w.
Hypothesis HN : 0 < [|wN|].
Hypothesis Hinv : [|ZnZ.mul wN wN'|] = wB - 1.

(* the high and low words of a double word *)
Definition split2 (c : zn2z w) : w * w :=
  match c with W0 => (ZnZ.zero, ZnZ.zero) | WW h l => (h, l) end.

Lemma split2_spec c :
  [|fst (split2 c)|] * wB + [|snd (split2 c)|] = zn2z_to_Z wB ZnZ.to_Z c.
Proof. destruct c as [ | h l]; simpl; [rewrite ZnZ.spec_0; ring | reflexivity]. Qed.

Definition mont_mul x y :=
  let '(h, l) := split2 (ZnZ.mul_c x y) in
  let m := ZnZ.mul l wN' in
  let '(mh, ml) := split2 (ZnZ.mul_c m wN) in
  let t := match ZnZ.add_c l ml with
           | C0 _ => ZnZ.add_c h mh
           | C1 _ => ZnZ.add_carry_c h mh end in
  match t with
  | C0 r => match ZnZ.compare r wN with Lt => r | _ => ZnZ.sub r wN end
  | C1 r => ZnZ.sub r wN
  end.

Lemma wB_pos : 0 < wB.
Proof. unfold base; apply Z.pow_pos_nonneg; auto with zarith. Qed.

(* the core of the proof: t = (x y + m N) / R, with m N = - x y mod R *)
Lemma mont_mul_spec x y : [|x|] < [|wN|] -> [|y|] < [|wN|] ->
  [|mont_mul x y|] < [|wN|] /\
  ([|mont_mul x y|] * wB) mod [|wN|] = ([|x|] * [|y|]) mod [|wN|].
Proof.
intros Hx Hy.
assert (HR := wB_pos).
assert (Bx := ZnZ.spec_to_Z x); assert (By := ZnZ.spec_to_Z y).
assert (BN := ZnZ.spec_to_Z wN); assert (BN' := ZnZ.spec_to_Z wN').
unfold mont_mul.
generalize (split2_spec (ZnZ.mul_c x y)); rewrite ZnZ.spec_mul_c.
destruct (split2 (ZnZ.mul_c x y)) as [h l]; simpl fst; simpl snd; intros HT.
set (m := ZnZ.mul l wN').
assert (Hm : [|m|] = ([|l|] * [|wN'|]) mod wB) by apply ZnZ.spec_mul.
generalize (split2_spec (ZnZ.mul_c m wN)); rewrite ZnZ.spec_mul_c.
destruct (split2 (ZnZ.mul_c m wN)) as [mh ml]; simpl fst; simpl snd; intros HmN.
assert (Bh := ZnZ.spec_to_Z h); assert (Bl := ZnZ.spec_to_Z l).
assert (Bmh := ZnZ.spec_to_Z mh); assert (Bml := ZnZ.spec_to_Z ml).
assert (Bm := ZnZ.spec_to_Z m).
(* l + ml is a multiple of R *)
assert (Hlml : ([|l|] + [|ml|]) mod wB = 0).
{ assert (E1 : [|ml|] = ([|m|] * [|wN|]) mod wB).
  { rewrite <- HmN, Z.add_comm, Z_mod_plus_full.
    rewrite Z.mod_small; lia. }
  assert (HNN' : ([|wN|] * [|wN'|]) mod wB = wB - 1).
  { rewrite <- Hinv; symmetry; apply ZnZ.spec_mul. }
  assert (E2 : [|ml|] mod wB = ([|l|] * (wB - 1)) mod wB).
  { rewrite E1, Zmod_mod, Hm, Zmult_mod_idemp_l.
    replace ([|l|] * [|wN'|] * [|wN|]) with ([|l|] * ([|wN|] * [|wN'|])) by ring.
    rewrite Zmult_mod, HNN', Zmult_mod_idemp_l; reflexivity. }
  rewrite Zplus_mod, E2, <- Zplus_mod.
  replace ([|l|] + [|l|] * (wB - 1)) with ([|l|] * wB) by ring.
  apply Z_mod_mult. }
(* so l + ml = c R with c = 0 or 1, and t = h + mh + c *)
assert (Ht : exists tv, tv * wB = [|x|] * [|y|] + [|m|] * [|wN|] /\
  match (match ZnZ.add_c l ml with
         | C0 _ => ZnZ.add_c h mh
         | C1 _ => ZnZ.add_carry_c h mh end) with
  | C0 r => [|r|] = tv
  | C1 r => wB + [|r|] = tv
  end).
{ generalize (ZnZ.spec_add_c l ml).
  destruct (ZnZ.add_c l ml) as [r | r]; unfold interp_carry; lazy beta iota; intros Hr;
    assert (Br := ZnZ.spec_to_Z r).
  - assert (H0 : [|l|] + [|ml|] = 0).
    { rewrite <- Hr in Hlml |- *; rewrite Z.mod_small in Hlml; lia. }
    exists ([|h|] + [|mh|]); split.
    + rewrite <- HT, <- HmN; nia.
    + generalize (ZnZ.spec_add_c h mh); destruct (ZnZ.add_c h mh); unfold interp_carry; lazy beta iota; lia.
  - assert (H1 : [|l|] + [|ml|] = wB).
    { rewrite <- Hr in Hlml.
      assert (E : (1 * wB + [|r|]) mod wB = [|r|] mod wB).
      { rewrite <- (Z.mod_add [|r|] 1 wB) by lia; f_equal; ring. }
      rewrite E, Z.mod_small in Hlml by lia.
      lia. }
    exists ([|h|] + [|mh|] + 1); split.
    + rewrite <- HT, <- HmN; nia.
    + generalize (ZnZ.spec_add_carry_c h mh);
        destruct (ZnZ.add_carry_c h mh); unfold interp_carry; lazy beta iota; lia. }
destruct Ht as [tv [Htv Hr]].
(* bounds and congruence of t *)
assert (Btv : 0 <= tv < 2 * [|wN|]).
{ split; [nia | idtac].
  assert (H1 : [|x|] * [|y|] < [|wN|] * [|wN|]) by nia.
  assert (H2 : [|m|] * [|wN|] < wB * [|wN|]) by nia.
  nia. }
assert (Ctv : (tv * wB) mod [|wN|] = ([|x|] * [|y|]) mod [|wN|]).
{ rewrite Htv, Z_mod_plus_full; reflexivity. }
destruct (match ZnZ.add_c l ml with
          | C0 _ => ZnZ.add_c h mh
          | C1 _ => ZnZ.add_carry_c h mh end) as [r | r];
  assert (Br := ZnZ.spec_to_Z r).
- rewrite ZnZ.spec_compare.
  case Z.compare_spec; intros Hc.
  + rewrite ZnZ.spec_sub, Z.mod_small by lia.
    split; [lia | idtac].
    rewrite <- Ctv, <- Hr, Z.mul_sub_distr_r, Zminus_mod,
      (Z.mul_comm [|wN|]), Z_mod_mult, Z.sub_0_r, Zmod_mod; reflexivity.
  + split; [lia | rewrite Hr; exact Ctv].
  + rewrite ZnZ.spec_sub, Z.mod_small by lia.
    split; [lia | idtac].
    rewrite <- Ctv, <- Hr, Z.mul_sub_distr_r, Zminus_mod,
      (Z.mul_comm [|wN|]), Z_mod_mult, Z.sub_0_r, Zmod_mod; reflexivity.
- rewrite ZnZ.spec_sub.
  replace (([|r|] - [|wN|]) mod wB) with (tv - [|wN|]).
  + split; [lia | idtac].
    rewrite <- Ctv, Z.mul_sub_distr_r, Zminus_mod,
      (Z.mul_comm [|wN|]), Z_mod_mult, Z.sub_0_r, Zmod_mod; reflexivity.
  + rewrite <- Hr.
    rewrite <- (Z_mod_plus_full ([|r|] - [|wN|]) 1 wB).
    rewrite Z.mod_small; lia.
Qed.

(* R is invertible modulo N: (N N' + 1) / R is its inverse *)
Lemma mont_R_cancel a b : (a * wB) mod [|wN|] = (b * wB) mod [|wN|] ->
  a mod [|wN|] = b mod [|wN|].
Proof.
intros H.
assert (HR := wB_pos).
set (q := ([|wN|] * [|wN'|]) / wB + 1).
assert (Hq : (q * wB) mod [|wN|] = 1 mod [|wN|]).
{ assert (H1 : ([|wN|] * [|wN'|]) mod wB = wB - 1).
  { rewrite <- Hinv; symmetry; apply ZnZ.spec_mul. }
  assert (H2 := Z_div_mod_eq_full ([|wN|] * [|wN'|]) wB).
  replace (q * wB) with (1 + [|wN'|] * [|wN|]).
  - rewrite Z_mod_plus_full; reflexivity.
  - unfold q; rewrite H1 in H2; lia. }
assert (E : forall c, c mod [|wN|] = ((c * wB) * q) mod [|wN|]).
{ intros c.
  replace (c * wB * q) with (c * (q * wB)) by ring.
  rewrite Zmult_mod, Hq, <- Zmult_mod, Z.mul_1_r; reflexivity. }
rewrite (E a), (E b), Zmult_mod, H, <- Zmult_mod; reflexivity.
Qed.

(* one product in Montgomery form: a R * b R * R^-1 = a b R *)
Lemma mont_mul_form u v a b : [|u|] < [|wN|] -> [|v|] < [|wN|] ->
  [|u|] mod [|wN|] = (a * wB) mod [|wN|] ->
  [|v|] mod [|wN|] = (b * wB) mod [|wN|] ->
  [|mont_mul u v|] < [|wN|] /\
  [|mont_mul u v|] mod [|wN|] = (a * b * wB) mod [|wN|].
Proof.
intros Hu Hv Hua Hvb.
destruct (@mont_mul_spec u v Hu Hv) as [H1 H2]; split; auto.
apply mont_R_cancel; rewrite H2.
replace (a * b * wB * wB) with ((a * wB) * (b * wB)) by ring.
rewrite Zmult_mod, Hua, Hvb, <- Zmult_mod; reflexivity.
Qed.

(* exponentiation in Montgomery form, as _power_mod in Mod_op *)
Fixpoint mpow (x : w) (p : positive) {struct p} : w :=
  match p with
  | xH => x
  | xO p' => let r := mpow x p' in mont_mul r r
  | xI p' => let r := mpow x p' in mont_mul (mont_mul r r) x
  end.

Lemma mpow_spec x a p : [|x|] < [|wN|] -> [|x|] mod [|wN|] = (a * wB) mod [|wN|] ->
  [|mpow x p|] < [|wN|] /\
  [|mpow x p|] mod [|wN|] = (Zpower_pos a p * wB) mod [|wN|].
Proof.
intros Hx Hxa.
assert (Hxo : forall p, Zpower_pos a (xO p) = Zpower_pos a p * Zpower_pos a p).
{ intros q; rewrite <- Pos.add_diag, Zpower_pos_is_exp; reflexivity. }
assert (Hxi : forall p, Zpower_pos a (xI p) = Zpower_pos a p * Zpower_pos a p * a).
{ intros q; rewrite Pos.xI_succ_xO, <- Pos.add_1_r, Zpower_pos_is_exp, Hxo.
  unfold Zpower_pos; simpl; ring. }
induction p as [p IH | p IH | ]; simpl mpow.
- destruct IH as [H1 H2].
  destruct (@mont_mul_form _ _ _ _ H1 H1 H2 H2) as [H3 H4].
  rewrite Hxi; apply (@mont_mul_form _ _ _ _ H3 Hx H4 Hxa).
- destruct IH as [H1 H2].
  rewrite Hxo; apply (@mont_mul_form _ _ _ _ H1 H1 H2 H2).
- unfold Zpower_pos; simpl; rewrite Z.mul_1_r; auto.
Qed.

End MontMul.

Section RmodN.

Variable w : univ_of_cycles.
Variable op : ZnZ.Ops w.
Variable op_spec : ZnZ.Specs op.
Variable wN : w.
Variable mop : mod_op w.
Hypothesis mop_spec : mod_spec op wN mop.
Hypothesis HN1 : 1 < ZnZ.to_Z wN.

(* 2^p mod N, by doubling 1 p times *)
Definition rmodn p := Pos.iter (fun u => mop.(add_mod) u u) ZnZ.one p.

Lemma rmodn_spec p : ZnZ.to_Z (rmodn p) = 2 ^ Zpos p mod ZnZ.to_Z wN.
Proof.
assert (H1 : ZnZ.to_Z (@ZnZ.one _ op) = 1 mod ZnZ.to_Z wN).
{ rewrite ZnZ.spec_1, Zmod_small; auto with zarith. }
induction p as [ | p IH] using Pos.peano_ind.
- unfold rmodn; simpl Pos.iter.
  rewrite (mop_spec.(add_mod_spec) _ _ _ _ H1 H1), ZnZ.spec_1; reflexivity.
- unfold rmodn; rewrite Pos.iter_succ; fold (rmodn p).
  rewrite (mop_spec.(add_mod_spec) _ _ _ _ IH IH), IH.
  rewrite <- Z.add_mod by auto with zarith.
  rewrite Pos2Z.inj_succ, Z.pow_succ_r by auto with zarith.
  f_equal; ring.
Qed.

End RmodN.

Section MontModOp.

Variable w : univ_of_cycles.
Variable op : ZnZ.Ops w.
Variable wN : w.

(* N' = - N^-1 mod R by Newton iteration: u (2 - N u) doubles the number of
   correct bits; it is checked before use (see make_mod_op) *)
Definition mont_inv :=
  ZnZ.sub ZnZ.zero
    (List.fold_left (fun u _ => ZnZ.mul u (ZnZ.sub (ZnZ.of_Z 2) (ZnZ.mul wN u)))
       (List.repeat tt (Pos.size_nat (ZnZ.digits op) + 1)) ZnZ.one).

(* make_mod_op with power_mod computed in Montgomery form; if N' fails the
   check, power_mod is the one of make_mod_op *)
Definition make_mod_op :=
  let m := Mod_op.make_mod_op op wN in
  let wN' := mont_inv in
  let ok := match ZnZ.compare (ZnZ.mul wN wN') (ZnZ.sub ZnZ.zero ZnZ.one) with
            | Eq => true | _ => false end in
  let wR := rmodn op m (ZnZ.digits op) in
  let wR2 := m.(mul_mod) wR wR in
  mk_mod_op m.(succ_mod) m.(add_mod) m.(pred_mod) m.(sub_mod) m.(mul_mod)
    m.(square_mod)
    (fun x p => if ok then
                  mont_mul op wN wN' (mpow op wN wN' (mont_mul op wN wN' x wR2) p)
                    ZnZ.one
                else m.(power_mod) x p).

Hypothesis b_pos : 1 < [|wN|].
Variable op_spec : ZnZ.Specs op.

Lemma make_mod_spec : mod_spec op wN make_mod_op.
Proof.
assert (ms := Mod_op.make_mod_spec wN b_pos op_spec).
assert (HN : 0 < [|wN|]) by auto with zarith.
apply mk_mod_spec.
- exact ms.(succ_mod_spec).
- exact ms.(add_mod_spec).
- exact ms.(pred_mod_spec).
- exact ms.(sub_mod_spec).
- exact ms.(mul_mod_spec).
- exact ms.(square_mod_spec).
- intros x t p Hx; unfold make_mod_op; lazy zeta; simpl power_mod.
  generalize (ZnZ.spec_compare (ZnZ.mul wN mont_inv) (ZnZ.sub ZnZ.zero ZnZ.one)).
  case ZnZ.compare; intros Hc; try exact (ms.(power_mod_spec) _ _ _ Hx).
  lazy beta iota.
  assert (HR : 0 < base (ZnZ.digits op)).
  { unfold base; apply Z.pow_pos_nonneg; auto with zarith. }
  assert (Hinv : [|ZnZ.mul wN mont_inv|] = base (ZnZ.digits op) - 1).
  { rewrite (Z.compare_eq _ _ (eq_sym Hc)), ZnZ.spec_sub, ZnZ.spec_0, ZnZ.spec_1.
    rewrite <- (Z_mod_plus_full (0 - 1) 1), Zmod_small; auto with zarith. }
  set (m := Mod_op.make_mod_op op wN).
  set (wR := rmodn op m (ZnZ.digits op)).
  assert (HwR := @rmodn_spec _ op op_spec wN m ms b_pos (ZnZ.digits op)); fold m wR in HwR.
  assert (HwR2 : [|m.(mul_mod) wR wR|] = (base (ZnZ.digits op) * base (ZnZ.digits op))
                                          mod [|wN|]).
  { unfold m; rewrite (ms.(mul_mod_spec) _ _ _ _ HwR HwR), HwR, <- Zmult_mod.
    unfold base; reflexivity. }
  assert (Bx : [|x|] < [|wN|]).
  { rewrite Hx; apply Z.mod_pos_bound; auto. }
  assert (B2 : [|m.(mul_mod) wR wR|] < [|wN|]).
  { rewrite HwR2; apply Z.mod_pos_bound; auto. }
  (* encode: x R *)
  destruct (@mont_mul_spec _ op op_spec wN mont_inv HN Hinv _ _ Bx B2) as [E1 E2].
  assert (E3 : [|mont_mul op wN mont_inv x (m.(mul_mod) wR wR)|] mod [|wN|]
               = ([|x|] * base (ZnZ.digits op)) mod [|wN|]).
  { apply (@mont_R_cancel _ op op_spec wN mont_inv Hinv); rewrite E2, HwR2.
    rewrite Zmult_mod_idemp_r, Z.mul_assoc; reflexivity. }
  (* power *)
  destruct (@mpow_spec _ op op_spec wN mont_inv HN Hinv _ _ p E1 E3) as [P1 P2].
  (* decode *)
  assert (B1 : [|ZnZ.one (Ops := op)|] < [|wN|]) by (rewrite ZnZ.spec_1; auto).
  destruct (@mont_mul_spec _ op op_spec wN mont_inv HN Hinv _ _ P1 B1) as [D1 D2].
  rewrite ZnZ.spec_1, Z.mul_1_r in D2.
  assert (D3 := @mont_R_cancel _ op op_spec wN mont_inv Hinv _ _ (eq_trans D2 P2)).
  rewrite <- D3, Zmod_small; auto.
  split; [apply (proj1 (ZnZ.spec_to_Z _)) | exact D1].
Qed.

End MontModOp.
