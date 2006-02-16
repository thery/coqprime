Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import ZDivModAux.
Require Import Basic_type.
Require Import GenBase.

Open Local Scope Z_scope.

Section GenMul.
 Variable w : Set.
 Variable w_0 : w.
 Variable w_1 : w.
 Variable w_WW : w -> w -> zn2z w.
 Variable w_W0 : w -> zn2z w.
 Variable w_0W : w -> zn2z w.
 Variable w_succ : w -> w.
 Variable w_add_c : w -> w -> carry w.
 Variable w_add : w -> w -> w.
 Variable w_mul_c : w -> w -> zn2z w.
 Variable w_mul : w -> w -> w.
 Variable w_square_c : w -> zn2z w.
 Variable ww_add_c : zn2z w -> zn2z w -> carry (zn2z w).
 Variable ww_add   : zn2z w -> zn2z w -> zn2z w.
 Variable ww_add_carry : zn2z w -> zn2z w -> zn2z w.
 Variable ww_sub_c : zn2z w -> zn2z w -> carry (zn2z w).
 Variable ww_sub   : zn2z w -> zn2z w -> zn2z w.

 (* ** Multiplication ** *)

 (*   (xh*B+xl) (yh*B + yl)
   xh*yh         = hh  = |hhh|hhl|B2
   xh*yl +xl*yh  = cc  =     |cch|ccl|B
   xl*yl         = ll  =         |llh|lll 
  *)

 Definition gen_mul_c (cross:w->w->w->w->zn2z w -> zn2z w -> w*zn2z w) x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0
  | WW xh xl, WW yh yl =>
    let hh := w_mul_c xh yh in
    let ll := w_mul_c xl yl in
    let (wc,cc) := cross xh xl yh yl hh ll in
    match cc with 
    | W0 => WW (ww_add hh (w_W0 wc)) ll
    | WW cch ccl =>
      match ww_add_c (w_W0 ccl) ll with
      | C0 l => WW (ww_add hh (w_WW wc cch)) l
      | C1 l => WW (ww_add_carry hh (w_WW wc cch)) l
      end
    end
  end.

 Definition ww_mul_c :=
  gen_mul_c 
    (fun xh xl yh yl hh ll=> 
      match ww_add_c (w_mul_c xh yl) (w_mul_c xl yh) with
      | C0 cc => (w_0, cc)
      | C1 cc => (w_1, cc)
      end).

 Definition kara_prod_carry1 mhh ll :=
  match ww_sub_c mhh ll with
  | C0 mhhll => (w_1, mhhll)
  | C1 mhhll => (w_0, mhhll)
  end.

 Definition kara_prod_carry2 m hh ll := 
  match ww_sub_c m hh with
  | C0 mhh => (w_1,ww_sub mhh ll) (* carry = 2 => -ll a une carry de 1 *)
  | C1 mhh => kara_prod_carry1 mhh ll
  end.

 Definition kara_prod_C0_C1 xhl yhl hh ll := 
  match ww_add_c (w_mul_c xhl yhl) (w_W0 xhl) with
  | C0 m => (w_0, ww_sub (ww_sub m hh) ll)
  | C1 m => (* carry = 1 *)
    match ww_sub_c m hh with
    | C0 mhh => kara_prod_carry1 mhh ll
    | C1 mhh =>  (w_0, ww_sub mhh ll)
    end
  end.
  
 Definition kara_prod cxhl cyhl hh ll :=
  match cxhl, cyhl with
  | C0 xhl, C0 yhl => (w_0, ww_sub (ww_sub (w_mul_c xhl yhl) hh) ll)
  | C0 xhl, C1 yhl => kara_prod_C0_C1 xhl yhl hh ll
  | C1 xhl, C0 yhl => kara_prod_C0_C1 yhl xhl hh ll
  | C1 xhl, C1 yhl => (* carry = 1 *)
    match w_add_c xhl yhl with
    | C0 suml => (* carry = 1 *)
      match ww_add_c (w_mul_c xhl yhl) (w_W0 suml) with
      | C0 m =>  (* carry = 1 *)
	match ww_sub_c m hh with
	| C0 mhh => kara_prod_carry1 mhh ll
        | C1 mhh => (w_0, ww_sub mhh ll)
        end
      | C1 m => kara_prod_carry2 m hh ll 
      end
    | C1 suml => (* carry = 2 *)
      match ww_add_c (w_mul_c xhl yhl) (w_W0 suml) with
      | C0 m => kara_prod_carry2 m hh ll
      | C1 m => (w_1, ww_sub (ww_sub m hh) ll)
                (* carry = 3 => les deux soutraction on une carry *)
      end
    end
  end.

 Definition ww_karatsuba_c :=
  gen_mul_c 
   (fun xh xl yh yl hh ll => kara_prod (w_add_c xh xl) (w_add_c yh yl) hh ll).

 Definition ww_mul x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0  
  | WW xh xl, WW yh yl => 
    let ccl := w_add (w_mul xh yl) (w_mul xl yh) in
    ww_add (w_W0 ccl) (w_mul_c xl yl)
  end.

 Definition ww_square_c x  :=
  match x with
  | W0 => W0
  | WW xh xl =>
    let hh := w_square_c xh in
    let ll := w_square_c xl in
    let xhxl := w_mul_c xh xl in
    let (wc,cc) :=
      match ww_add_c xhxl xhxl with
      | C0 cc => (w_0, cc)
      | C1 cc => (w_1, cc)
      end in
    match cc with
    | W0 => WW (ww_add hh (w_W0 wc)) ll
    | WW cch ccl =>
      match ww_add_c (w_W0 ccl) ll with
      | C0 l => WW (ww_add hh (w_WW wc cch)) l
      | C1 l => WW (ww_add_carry hh (w_WW wc cch)) l
      end
    end
  end.

 Section GenMulAddn1.
  Variable w_mul_add : w -> w -> w -> w * w.

  Fixpoint gen_mul_add_n1 (n:nat) : word w n -> w -> w -> w * word w n :=
   match n return word w n -> w -> w -> w * word w n with 
   | O => w_mul_add 
   | S n1 => 
     let mul_add := gen_mul_add_n1 n1 in
     fun x y r =>
     match x with
     | W0 => (w_0,extend w_0W n1 r)
     | WW xh xl =>
       let (rl,l) := mul_add xl y r in
       let (rh,h) := mul_add xh y rl in
       (rh, gen_WW w_WW n1 h l)
     end
   end.

 End GenMulAddn1.

 Definition w_mul_add x y r :=
  match w_mul_c x y with
  | W0 => (w_0, r)
  | WW h l =>
    match w_add_c l r with
    | C0 lr => (h,lr)
    | C1 lr => (w_succ h, lr) 
    end
  end.

  
 (*Section GenProof. *)
  Variable w_digits : positive.
  Variable w_to_Z : w -> Z.

  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[+| c |]" :=
   (interp_carry 1 wB w_to_Z c) (at level 0, x at level 99).
  Notation "[-| c |]" :=
   (interp_carry (-1) wB w_to_Z c) (at level 0, x at level 99).

  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).
  Notation "[+[ c ]]" := 
   (interp_carry 1 wwB (ww_to_Z w_digits w_to_Z) c) 
   (at level 0, x at level 99).
  Notation "[-[ c ]]" := 
   (interp_carry (-1) wwB (ww_to_Z w_digits w_to_Z) c) 
   (at level 0, x at level 99).

  Notation "[|| x ||]" :=
    (zn2z_to_Z wwB (ww_to_Z w_digits w_to_Z) x)  (at level 0, x at level 99).

  Notation "[! n | x !]" := (gen_to_Z w_digits w_to_Z n x)
    (at level 0, x at level 99).

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_w_1   : [|w_1|] = 1.

  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.

  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_w_W0 : forall h, [[w_W0 h]] = [|h|] * wB.
  Variable spec_w_0W : forall l, [[w_0W l]] = [|l|].

  Variable spec_w_succ : forall x, [|w_succ x|] = ([|x|] + 1) mod wB.
  Variable spec_w_add_c  : forall x y, [+|w_add_c x y|] = [|x|] + [|y|].
  Variable spec_w_add : forall x y, [|w_add x y|] = ([|x|] + [|y|]) mod wB.

  Variable spec_mul_c : forall x y, [[ w_mul_c x y ]] = [|x|] * [|y|].
  Variable spec_mul : forall x y, [|w_mul x y|] = ([|x|] * [|y|]) mod wB.
  Variable spec_square_c : forall x, [[ w_square_c x]] = [|x|] * [|x|].

  Variable spec_ww_add_c  : forall x y, [+[ww_add_c x y]] = [[x]] + [[y]].
  Variable spec_ww_add : forall x y, [[ww_add x y]] = ([[x]] + [[y]]) mod wwB.
  Variable spec_ww_add_carry :
	 forall x y, [[ww_add_carry x y]] = ([[x]] + [[y]] + 1) mod wwB.
  Variable spec_ww_sub : forall x y, [[ww_sub x y]] = ([[x]] - [[y]]) mod wwB.
  Variable spec_ww_sub_c : forall x y, [-[ww_sub_c x y]] = [[x]] - [[y]].
 
 
  Lemma spec_ww_to_Z : forall x, 0 <= [[x]] < wwB.
  Proof. intros x;apply spec_ww_to_Z;auto. Qed.

  Lemma spec_ww_to_Z_wBwB : forall x, 0 <= [[x]] < wB*wB.
  Proof. rewrite <- wwB_wBwB;apply spec_ww_to_Z. Qed.

  Hint Resolve spec_ww_to_Z spec_ww_to_Z_wBwB : mult.
  Ltac zarith := auto with zarith mult.

  Lemma wBwB_lex: forall a b c d,
      a * (wB * wB) + [[b]] <= c * (wB * wB) + [[d]] -> 
      a <= c.
  Proof.   
   intros a b c d H; apply beta_lex with [[b]] [[d]] (wB * wB);zarith.
  Qed.

  Lemma wBwB_lex_inv: forall a b c d, 
      a < c -> 
      a * (wB * wB) + [[b]] < c * (wB * wB) + [[d]]. 
  Proof.
   intros a b c d H; apply beta_lex_inv; zarith.
  Qed.

  Lemma sum_mul_carry : forall xh xl yh yl wc cc,
   [|wc|]*wB*wB + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] -> 
   0 <= [|wc|] <= 1.
  Proof.
   intros.
   apply (sum_mul_carry [|xh|] [|xl|] [|yh|] [|yl|] [|wc|][[cc]] wB);zarith.
   apply wB_pos.
  Qed.

  Theorem mult_add_ineq: forall xH yH crossH, 
               0 <= [|xH|] * [|yH|] + [|crossH|] < wwB.
  Proof.
   intros;rewrite wwB_wBwB;apply mult_add_ineq;zarith.
  Qed.
 
  Hint Resolve mult_add_ineq : mult.
 
  Lemma spec_mul_aux : forall xh xl yh yl wc (cc:zn2z w) hh ll,
   [[hh]] = [|xh|] * [|yh|] ->
   [[ll]] = [|xl|] * [|yl|] ->
   [|wc|]*wB*wB + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] ->
    [||match cc with
      | W0 => WW (ww_add hh (w_W0 wc)) ll
      | WW cch ccl =>
          match ww_add_c (w_W0 ccl) ll with
          | C0 l => WW (ww_add hh (w_WW wc cch)) l
          | C1 l => WW (ww_add_carry hh (w_WW wc cch)) l
          end
      end||] = ([|xh|] * wB + [|xl|]) * ([|yh|] * wB + [|yl|]).
  Proof.
   intros;assert (U1 := wB_pos w_digits).
   replace (([|xh|] * wB + [|xl|]) * ([|yh|] * wB + [|yl|])) with 
   ([|xh|]*[|yh|]*wB*wB + ([|xh|]*[|yl|] + [|xl|]*[|yh|])*wB + [|xl|]*[|yl|]).
   2:ring. rewrite <- H1;rewrite <- H;rewrite <- H0.  
   assert (H2 := sum_mul_carry _ _ _ _ _ _ H1).
   destruct cc as [ | cch ccl];simpl.
   rewrite spec_ww_add;rewrite spec_w_W0;rewrite Zmod_def_small;
    rewrite wwB_wBwB. ring.
   rewrite <- (Zplus_0_r ([|wc|]*wB));rewrite H;apply mult_add_ineq3;zarith.
   simpl in H1. assert (U:=spec_to_Z cch).
   assert ([|wc|]*wB + [|cch|] <= 2*wB - 3).
    destruct (Z_le_gt_dec ([|wc|]*wB + [|cch|]) (2*wB - 3));trivial.
    assert ([|xh|] * [|yl|] + [|xl|] * [|yh|] <= (2*wB - 4)*wB + 2).
     ring ((2*wB - 4)*wB + 2).
     assert (H4 := Zmult_lt_b _ _ _ (spec_to_Z xh) (spec_to_Z yl)).
     assert (H5 := Zmult_lt_b _ _ _ (spec_to_Z xl) (spec_to_Z yh));omega.
    generalize H3;clear H3;rewrite <- H1.
    rewrite Zplus_assoc;rewrite <- Zmult_plus_distr_l.
    assert (((2 * wB - 4) + 2)*wB <= ([|wc|] * wB + [|cch|])*wB).
     apply Zmult_le_compat;zarith.
    rewrite Zmult_plus_distr_l in H3. 
    intros. assert (U2 := spec_to_Z ccl);omega.
   generalize (spec_ww_add_c (w_W0 ccl) ll);destruct (ww_add_c (w_W0 ccl) ll)
   as [l|l];unfold interp_carry;rewrite spec_w_W0;try rewrite Zmult_1_l;simpl;
   try rewrite spec_ww_add;try rewrite spec_ww_add_carry;rewrite spec_w_WW;
   rewrite Zmod_def_small;rewrite wwB_wBwB;intros.
   rewrite H4;ring. rewrite H;apply mult_add_ineq2;zarith.
   rewrite Zplus_assoc;rewrite Zmult_plus_distr_l.
   rewrite Zmult_1_l;rewrite <- Zplus_assoc;rewrite H4;ring.
   repeat rewrite <- Zplus_assoc;rewrite H;apply mult_add_ineq2;zarith.
  Qed.

  Lemma spec_gen_mul_c : forall cross:w->w->w->w->zn2z w -> zn2z w -> w*zn2z w,
     (forall xh xl yh yl hh ll,
        [[hh]] = [|xh|]*[|yh|] ->
        [[ll]] = [|xl|]*[|yl|] ->
        let (wc,cc) :=  cross xh xl yh yl hh ll in 
        [|wc|]*wwB + [[cc]] = [|xh|]*[|yl|] + [|xl|]*[|yh|]) -> 
     forall x y, [||gen_mul_c cross x y||] = [[x]] * [[y]].
  Proof.
   intros cross Hcross x y;destruct x as [ |xh xl];simpl;trivial.
   destruct y as [ |yh yl];simpl. rewrite Zmult_0_r;trivial.
   assert (H1:= spec_mul_c xh yh);assert (H2:= spec_mul_c xl yl).
   generalize (Hcross _ _ _ _ _ _ H1 H2).
   destruct (cross xh xl yh yl (w_mul_c xh yh) (w_mul_c xl yl)) as (wc,cc).
   intros;apply spec_mul_aux;trivial.
   rewrite <- Zmult_assoc;rewrite <- wwB_wBwB;trivial.
  Qed.

  Lemma spec_ww_mul_c : forall x y, [||ww_mul_c x y||] = [[x]] * [[y]]. 
  Proof.
   intros x y;unfold ww_mul_c;apply spec_gen_mul_c.
   intros xh xl yh yl hh ll H1 H2.
   generalize (spec_ww_add_c (w_mul_c xh yl) (w_mul_c xl yh));
   destruct (ww_add_c (w_mul_c xh yl) (w_mul_c xl yh)) as [c|c];
   unfold interp_carry;repeat rewrite spec_mul_c;intros H;
   (rewrite spec_w_0 || rewrite spec_w_1);rewrite H;ring.
  Qed.

  Lemma kara_prod_aux : forall xh xl yh yl,
   (xh+xl)*(yh+yl) - xh*yh - xl*yl = xh*yl + xl*yh.
  Proof. intros;ring. Qed.
   
  Lemma spec_kara_prod_carry1 : forall xh xl yh yl mhh ll,
    wwB+[[mhh]] =(xh+xl)*(yh+yl) - xh*yh ->
    [[ll]] = xl*yl ->
    let (wc,cc) := kara_prod_carry1 mhh ll in
    [|wc|]*wwB + [[cc]] = xh*yl + xl*yh.
  Proof.
   intros xh xl yh yl mhh ll H1 H2.
   rewrite <- kara_prod_aux;rewrite <- H2;rewrite <- H1.
   replace (wwB + [[mhh]] - [[ll]]) with (wwB + ([[mhh]] - [[ll]])). 2:ring.
   unfold kara_prod_carry1. 
   generalize (spec_ww_sub_c mhh ll);destruct (ww_sub_c mhh ll);
   unfold interp_carry;intros H;rewrite <- H;
   (rewrite spec_w_0||rewrite spec_w_1);ring.
  Qed.

  Lemma sub_carry : forall xh xl yh yl z, 
    0 <= z -> 
    [|xh|]*[|yl|] + [|xl|]*[|yh|] = wwB + z ->
    z < wwB.
  Proof.
   intros xh xl yh yl z Hle Heq.
   destruct (Z_le_gt_dec wwB z);auto with zarith.
   generalize (Zmult_lt_b _ _ _ (spec_to_Z xh) (spec_to_Z yl)).
   generalize (Zmult_lt_b _ _ _ (spec_to_Z xl) (spec_to_Z yh)).
   rewrite <- wwB_wBwB;intros H1 H2.
   assert (H3 := wB_pos w_digits).
   assert (2*wB <= wwB). 
    rewrite wwB_wBwB;apply Zmult_le_compat;zarith.
   omega.
  Qed.

  Ltac Spec_ww_to_Z x :=
   let H:= fresh "H" in
   assert (H:= spec_ww_to_Z x).

  Ltac Zmult_lt_b x y := 
   let H := fresh "H" in
   assert (H := Zmult_lt_b _ _ _ (spec_to_Z x) (spec_to_Z y)).

  Lemma spec_kara_prod_carry2 : forall xh xl yh yl m hh ll,
    2*wwB+[[m]] =([|xh|]+[|xl|])*([|yh|]+[|yl|]) ->
    [[hh]] = [|xh|]*[|yh|] ->
    [[ll]] = [|xl|]*[|yl|] ->
    let (wc,cc) := kara_prod_carry2 m hh ll in
    [|wc|]*wwB + [[cc]] = [|xh|]*[|yl|] + [|xl|]*[|yh|].
  Proof.
   intros xh xl yh yl m hh ll H1 H2 H3; unfold kara_prod_carry2.
   generalize (spec_ww_sub_c m hh);destruct (ww_sub_c m hh) as [mhh|mhh];
   unfold interp_carry;intros.
   generalize (kara_prod_aux [|xh|] [|xl|] [|yh|] [|yl|]).
   rewrite <- H2;rewrite <- H1;rewrite <- H3.
   replace (2*wwB+[[m]]-[[hh]]-[[ll]])with(wwB+(wwB+([[m]]-[[hh]]-[[ll]]))). 
   2:ring. rewrite <- H;rewrite spec_ww_sub;rewrite spec_w_1.
   intros H0;rewrite <- H0;rewrite Zmult_1_l.
   replace (([[mhh]] - [[ll]]) mod wwB) with (wwB + ([[mhh]]-[[ll]]));trivial.
   assert (H4:=lt_0_wwB);apply Zmod_unique with (q:= -1);zarith.
   assert (0 <= wwB + ([[mhh]] - [[ll]])).
    Spec_ww_to_Z mhh;Spec_ww_to_Z ll;zarith.
   split;trivial.
   apply (sub_carry _ _ _ _ H5 (sym_eq H0)).
   apply spec_kara_prod_carry1;trivial.
   rewrite <- H1;rewrite <- H2.
   unfold Zminus in *;rewrite <- Zplus_assoc;rewrite <- H;ring.
  Qed.

  Lemma spec_kara_prod_C0_C1 : forall xh xl yh yl xhl yhl hh ll,
    [[hh]] = [|xh|]*[|yh|] ->
    [[ll]] = [|xl|]*[|yl|] ->
    [|xhl|] = [|xh|]+[|xl|] ->
    wB+[|yhl|] = [|yh|]+[|yl|] ->
    let (wc,cc) := kara_prod_C0_C1 xhl yhl hh ll in
    [|wc|]*wwB + [[cc]] = [|xh|]*[|yl|] + [|xl|]*[|yh|].
  Proof.
   intros;unfold kara_prod_C0_C1.
   generalize (kara_prod_aux [|xh|] [|xl|] [|yh|] [|yl|]).
   rewrite <- H1;rewrite <- H;rewrite <- H0;rewrite <- H2.
   replace ([|xhl|] * (wB + [|yhl|]) - [[hh]] - [[ll]]) with
   ([|xhl|]*[|yhl|] + [|xhl|]*wB - [[hh]] - [[ll]]). 2:ring.
   intros H3;generalize (spec_ww_add_c (w_mul_c xhl yhl) (w_W0 xhl));
   rewrite spec_mul_c;rewrite spec_w_W0;destruct 
   (ww_add_c (w_mul_c xhl yhl) (w_W0 xhl)) as [m|m];
   unfold interp_carry;try rewrite Zmult_1_l;intros.
   rewrite spec_w_0;simpl;rewrite <- H4 in H3;rewrite <- H3. 
   repeat rewrite spec_ww_sub. 
   Zmult_lt_b xh yl;Zmult_lt_b xl yh. 
   rewrite <- wwB_wBwB in H5;rewrite <- wwB_wBwB in H6.
   Spec_ww_to_Z m;Spec_ww_to_Z hh;Spec_ww_to_Z ll.
   rewrite (Zmod_def_small ([[m]]-[[hh]]));zarith.
   rewrite Zmod_def_small;zarith.
   generalize (spec_ww_sub_c m hh);destruct (ww_sub_c m hh);
   unfold interp_carry;intros.
   apply spec_kara_prod_carry1;trivial.
   rewrite H5;replace (wwB+([[m]]-[[hh]])) with (wwB+[[m]]-[[hh]]). 2:ring.
   rewrite H4;rewrite <- H1;rewrite <- H2;rewrite <- H;ring.
   rewrite spec_w_0;simpl; rewrite <- H4 in H3;rewrite <- H3.
   generalize H3;clear H3.
   replace (wwB+[[m]]-[[hh]]-[[ll]]) with (wwB+([[m]]-[[hh]])-[[ll]]). 2:ring.
   rewrite <- H5. 
   replace (wwB + (-1 * wwB + [[z]]) - [[ll]]) with ([[z]]-[[ll]]). 2:ring.
   intros;rewrite spec_ww_sub;rewrite Zmod_def_small;trivial.
   Zmult_lt_b xh yl;Zmult_lt_b xl yh. 
   rewrite <- wwB_wBwB in H6;rewrite <- wwB_wBwB in H7.
   Spec_ww_to_Z z;Spec_ww_to_Z ll;zarith.
  Qed.

  Lemma spec_kara_prod : forall xh xl yh yl cxhl cyhl hh ll,
   [[hh]] = [|xh|]*[|yh|] ->
   [[ll]] = [|xl|]*[|yl|] ->
   [+|cxhl|] = [|xh|]+[|xl|] ->
   [+|cyhl|] = [|yh|]+[|yl|] ->
   let (wc,cc) := kara_prod cxhl cyhl hh ll in
   [|wc|]*wwB + [[cc]] = [|xh|]*[|yl|] + [|xl|]*[|yh|].
  Proof.
   intros xh xl yh yl cxhl cyhl hh ll H H0.
   destruct cxhl as [xhl|xhl];destruct cyhl as [yhl|yhl];unfold
   interp_carry;try rewrite Zmult_1_l;intros;simpl.
   rewrite spec_w_0;generalize (kara_prod_aux [|xh|] [|xl|] [|yh|] [|yl|]).
   rewrite <- H;rewrite <- H0;rewrite <- H1;rewrite <- H2;simpl.
   intros H3;rewrite <- H3; Zmult_lt_b xh yl;Zmult_lt_b xl yh. 
   rewrite <- wwB_wBwB in H4;rewrite <- wwB_wBwB in H5.
   Spec_ww_to_Z (w_mul_c xhl yhl);Spec_ww_to_Z hh;Spec_ww_to_Z ll.
   repeat rewrite spec_ww_sub. assert (H9 := spec_mul_c xhl yhl).
   rewrite (Zmod_def_small ([[w_mul_c xhl yhl]]-[[hh]]));zarith.
   rewrite Zmod_def_small;zarith.
   apply spec_kara_prod_C0_C1;trivial.
   rewrite (Zmult_comm [|xh|]);rewrite (Zmult_comm [|xl|]);rewrite 
   (Zplus_comm ([|yl|]*[|xh|])); apply spec_kara_prod_C0_C1;trivial.
   rewrite Zmult_comm;trivial.  rewrite Zmult_comm;trivial.
   generalize (kara_prod_aux [|xh|] [|xl|] [|yh|] [|yl|]). 
   rewrite <- H;rewrite <- H0;rewrite <- H1;rewrite <- H2.
   replace ((wB + [|xhl|]) * (wB + [|yhl|]) - [[hh]] - [[ll]]) with
   (wB*wB + ([|xhl|]+[|yhl|])*wB+ [|xhl|]*[|yhl|] -[[hh]] - [[ll]]).  2:ring.
   generalize (spec_w_add_c xhl yhl);destruct (w_add_c xhl yhl) as [suml|suml];
    unfold interp_carry;try rewrite Zmult_1_l;intros H3;rewrite <- H3.
   replace (wB * wB + [|suml|] * wB + [|xhl|] * [|yhl|]) with
    (wB * wB + ([|xhl|] * [|yhl|] + [|suml|] * wB)). 2:ring.
   generalize (spec_ww_add_c (w_mul_c xhl yhl) (w_W0 suml));rewrite spec_w_W0;
   rewrite spec_mul_c;intros H4;rewrite <- H4;clear H4.
   destruct (ww_add_c (w_mul_c xhl yhl) (w_W0 suml)) as [m|m];
    unfold interp_carry;try rewrite Zmult_1_l.
   replace (wB * wB + [[m]] - [[hh]]) with (wB*wB+([[m]] - [[hh]])). 2:ring.
   rewrite <- (spec_ww_sub_c m hh);destruct (ww_sub_c m hh) as [mhh|mhh];
   unfold interp_carry;try rewrite Zmult_1_l.
   intros;apply spec_kara_prod_carry1;trivial.
   rewrite <- kara_prod_aux in H4;rewrite wwB_wBwB;zarith.
   rewrite spec_w_0;rewrite Zmult_0_l;replace (wB * wB + (-1 * wwB + [[mhh]]))
   with [[mhh]]. 2:rewrite wwB_wBwB;ring. intros H4;rewrite <- H4.
   rewrite Zplus_0_l;rewrite spec_ww_sub;rewrite Zmod_def_small;zarith.
   Zmult_lt_b xh yl;Zmult_lt_b xl yh. 
   rewrite <- wwB_wBwB in H5;rewrite <- wwB_wBwB in H6.
   Spec_ww_to_Z mhh;Spec_ww_to_Z ll;zarith.
   intros;apply spec_kara_prod_carry2;trivial. 
   rewrite <- kara_prod_aux in H4;rewrite <- wwB_wBwB in H4;zarith.
   replace (wB * wB + (wB + [|suml|]) * wB + [|xhl|] * [|yhl|]) with
   (2*wB*wB + ([|xhl|] * [|yhl|] +  [|suml|] * wB)). 2:ring.
   generalize (spec_ww_add_c (w_mul_c xhl yhl) (w_W0 suml));rewrite spec_w_W0;
   rewrite spec_mul_c;intros H4;rewrite <- H4;clear H4.
   destruct (ww_add_c (w_mul_c xhl yhl) (w_W0 suml)) as [m|m];
   unfold interp_carry;try rewrite Zmult_1_l;intros.
   apply spec_kara_prod_carry2;trivial.
   generalize H4;clear H4;rewrite <- kara_prod_aux;rewrite wwB_wBwB.
   rewrite <- H;rewrite <- H0. rewrite <- Zmult_assoc;zarith.
   rewrite spec_w_1;rewrite Zmult_1_l;rewrite <- Zmult_assoc in H4.
   rewrite <- wwB_wBwB in H4.
   Spec_ww_to_Z m;Spec_ww_to_Z hh;Spec_ww_to_Z ll.
   assert ((2*wwB + [[m]]) - [[hh]] - [[ll]] < wwB).
    apply (sub_carry xh xl yh yl);zarith.
   repeat rewrite spec_ww_sub. 
   assert (wwB + [[m]] - [[hh]] = ([[m]] - [[hh]]) mod wwB).
    apply Zmod_unique with (-1);zarith.
   rewrite <- H9;clear H9.
   assert (2*wwB+[[m]]-[[hh]]-[[ll]]=(wwB+[[m]]-[[hh]]-[[ll]]) mod wwB).
    apply Zmod_unique with (-1);zarith.
   rewrite <- H9;rewrite <- H4;ring.
  Qed.

  Lemma spec_ww_karatsuba_c : forall x y, [||ww_karatsuba_c x y||]=[[x]]*[[y]].
  Proof.
   intros x y; unfold ww_karatsuba_c;apply spec_gen_mul_c.
   intros xh xl yh yl hh ll H H0;apply spec_kara_prod;trivial.
  Qed.

  Lemma spec_ww_mul : forall x y, [[ww_mul x y]] = [[x]]*[[y]] mod wwB.
  Proof.
   assert (U:= lt_0_wB w_digits).
   assert (U1:= lt_0_wwB w_digits).
   intros x y; case x; auto; intros xh xl.
   case y; auto.
   simpl; rewrite Zmult_0_r; rewrite Zmod_def_small; auto with zarith.
   intros yh yl;simpl.
   repeat (rewrite spec_ww_add || rewrite spec_w_W0 || rewrite spec_mul_c
    || rewrite spec_w_add || rewrite spec_mul).
   rewrite <- Zmod_plus; auto with zarith.
   repeat (rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r).
   rewrite <- Zmult_mod_distr_r; auto with zarith.
   rewrite <- wwB_wBwB; auto with zarith.
   rewrite Zmod_plus; auto with zarith.
   rewrite Zmod_mod; auto with zarith.
   rewrite <- Zmod_plus; auto with zarith.
   match goal with |- ?X mod _ = _ =>
     rewrite <- Z_mod_plus with (a := X) (b := [|xh|] * [|yh|])
   end; auto with zarith.
   eq_tac; auto; rewrite wwB_wBwB; ring.
  Qed.

  Lemma spec_ww_square_c : forall x, [||ww_square_c x||] = [[x]]*[[x]].
  Proof.
   destruct x as [ |xh xl];simpl;trivial.
   case_eq match ww_add_c (w_mul_c xh xl) (w_mul_c xh xl) with
          | C0 cc => (w_0, cc)
          | C1 cc => (w_1, cc)
          end;intros wc cc Heq.
   apply (spec_mul_aux xh xl xh xl wc cc);trivial.
   generalize Heq (spec_ww_add_c (w_mul_c xh xl) (w_mul_c xh xl));clear Heq.
   rewrite spec_mul_c;destruct (ww_add_c (w_mul_c xh xl) (w_mul_c xh xl));
   unfold interp_carry;try rewrite Zmult_1_l;intros Heq Heq';inversion Heq;
   rewrite (Zmult_comm [|xl|]);subst.
   rewrite spec_w_0;rewrite Zmult_0_l;rewrite Zplus_0_l;trivial.
   rewrite spec_w_1;rewrite Zmult_1_l;rewrite <- wwB_wBwB;trivial.
  Qed.

  Section GenMulAddn1Proof.

   Variable w_mul_add : w -> w -> w -> w * w.
   Variable spec_w_mul_add : forall x y r,
    let (h,l):= w_mul_add x y r in
    [|h|]*wB+[|l|] = [|x|]*[|y|] + [|r|]. 

   Lemma spec_gen_mul_add_n1 : forall n x y r,
     let (h,l) := gen_mul_add_n1 w_mul_add n x y r in
     [|h|]*gen_wB w_digits n + [!n|l!] = [!n|x!]*[|y|]+[|r|].
   Proof.
    induction n;intros x y r;trivial.
    exact (spec_w_mul_add x y r).
    unfold gen_mul_add_n1;destruct x as[ |xh xl]; 
     fold(gen_mul_add_n1 w_mul_add).
    rewrite spec_w_0;rewrite spec_extend;simpl;trivial.
    assert(H:=IHn xl y r);destruct (gen_mul_add_n1 w_mul_add n xl y r)as(rl,l).
   assert(U:=IHn xh y rl);destruct(gen_mul_add_n1 w_mul_add n xh y rl)as(rh,h).
    rewrite <- gen_wB_wwB. rewrite spec_gen_WW;simpl;trivial.
    rewrite Zmult_plus_distr_l;rewrite <- Zplus_assoc;rewrite <- H.
    rewrite Zmult_assoc;rewrite Zplus_assoc;rewrite <- Zmult_plus_distr_l.
    rewrite U;ring.
   Qed. 
 
  End GenMulAddn1Proof.

  Lemma spec_w_mul_add : forall x y r, 
    let (h,l):= w_mul_add x y r in
    [|h|]*wB+[|l|] = [|x|]*[|y|] + [|r|]. 
  Proof.
   intros x y r;unfold w_mul_add;assert (H:=spec_mul_c x y);
   destruct (w_mul_c x y) as [ |h l];simpl;rewrite <- H.
   rewrite spec_w_0;trivial.
   assert (U:=spec_w_add_c l r);destruct (w_add_c l r) as [lr|lr];unfold
   interp_carry in U;try rewrite Zmult_1_l in H;simpl.
   rewrite U;ring. rewrite spec_w_succ. rewrite Zmod_def_small.
   rewrite <- Zplus_assoc;rewrite <- U;ring.
   simpl in H;assert (H1:= Zmult_lt_b _ _ _ (spec_to_Z x) (spec_to_Z y)).
   rewrite <- H in H1.
   assert (H2:=spec_to_Z h);split;zarith.
   case H1;clear H1;intro H1;clear H1.
   replace (wB * wB - 2 * wB) with ((wB - 2)*wB). 2:ring.
   intros H0;assert (U1:= wB_pos w_digits).
   assert (H1 := beta_lex _ _ _ _ _ H0 (spec_to_Z l));zarith.
  Qed.

(* End GenProof. *)

End GenMul.
