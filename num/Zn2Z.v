(*
Unset Boxed Definitions.
*)

Set Implicit Arguments.

Require Import ZArith.
Require Import ZnZ.
Require Import ZAux.
Require Import ZDivModAux.

Open Local Scope Z_scope.



Section Zn2Z.
 
 Variable w : Set.
 Variable w_op : znz_op w.

 Let w_digits      := w_op.(znz_digits).
 Let w_to_Z        := w_op.(znz_to_Z).
 Let w_of_pos      := w_op.(znz_of_pos).
 Let w_head0       := w_op.(znz_head0).

 Let w0            := w_op.(znz_0).
 Let w1            := w_op.(znz_1).
 Let wBm1          := w_op.(znz_Bm1).

 Let wWW           := w_op.(znz_WW).
 Let wCW           := w_op.(znz_CW).

 Let w_compare     := w_op.(znz_compare).
 Let w_opp_c       := w_op.(znz_opp_c).
 Let w_opp_carry   := w_op.(znz_opp_carry).

 Let w_succ_c      := w_op.(znz_succ_c).
 Let w_add_c       := w_op.(znz_add_c).
 Let w_add_carry_c := w_op.(znz_add_carry_c).
 Let w_add         := w_op.(znz_add).

 Let w_pred_c      := w_op.(znz_pred_c).
 Let w_sub_c       := w_op.(znz_sub_c).
 Let w_sub_carry_c := w_op.(znz_sub_carry_c).
 Let w_sub         := w_op.(znz_sub).

 Let w_mul_c       := w_op.(znz_mul_c).
 Let w_mul         := w_op.(znz_mul).

 Let w_square_c    := w_op.(znz_square_c).

 Let w_div21       := w_op.(znz_div21).
 Let w_add_mul_div := w_op.(znz_add_mul_div).

 Let _zn2z := zn2z w.

 Let wB := base w_digits.

 Let ww_digits := xO w_digits.

 Definition ww_to_Z := zn2z_to_Z wB w_to_Z.

 Definition ww_of_pos p :=
  match w_of_pos p with
  | (N0, l) => (N0, WW w0 l)
  | (Npos ph,l) => 
    let (n,h) := w_of_pos ph in (n, wWW h l)
  end.

 Definition ww_head0 x :=
  match x with
  | W0 => Npos ww_digits
  | WW xh xl =>
    match w_compare xh w0 with
    | Eq => Nplus (Npos w_digits) (w_head0 xl)
    | _ => w_head0 xh
    end
  end.

 Let ww_1 :=  WW w0 w1.

 Let ww_Bm1 := WW wBm1 wBm1.

 Definition ww_WW xh xl : zn2z _zn2z :=
  match xh, xl with
  | W0, W0 => W0
  | _, _ => WW xh xl
  end.
 
 Definition ww_CW ch l : carry (zn2z _zn2z) :=
  match ch with
  | C0 h => C0 (ww_WW h l)
  | C1 h => C1 (ww_WW h l)
  end.

 (* ** Comparison ** *)
 Definition ww_compare x y :=
  match x, y with
  | W0, W0 => Eq
  | W0, WW yh yl =>
    match w_compare w0 yh with
    | Eq => w_compare w0 yl 
    | cmp => cmp
    end
  | WW xh xl, W0 =>
    match w_compare xh w0 with
    | Eq => w_compare xl w0
    | cmp => cmp
    end
  | WW xh xl, WW yh yl =>
    match w_compare xh yh with
    | Eq => w_compare xl yl
    | cmp => cmp
    end
  end.
 
 (* ** Opposites ** *)
 Definition ww_opp_c x :=
  match x with
  | W0 => C0 W0
  | WW xh xl => 
    match w_opp_c xl with
    | C0 _ => wCW (w_opp_c xh) w0
    | C1 l => C1 (wWW (w_opp_carry xh) l)
    end
  end.

 Definition ww_opp_carry x :=
  match x with
  | W0 => ww_Bm1
  | WW xh xl => wWW (w_opp_carry xh) (w_opp_carry xl)
  end.
  
 (* ** Additions ** *)

 Definition ww_succ_c x :=
   match x with
   | W0 => C0 ww_1
   | WW xh xl => 
     match w_succ_c xl with
     | C0 l => C0 (wWW xh l)
     | C1 l => wCW (w_succ_c xh) l
     end
   end.

 Definition ww_succ := 
   let succ_c := ww_succ_c in 
   fun x => without_c (succ_c x).

 Definition ww_add_c x y :=
  match x, y with
  | W0, _ => C0 y
  | _, W0 => C0 x
  | WW xh xl, WW yh yl =>
    match w_add_c xl yl with
    | C0 l => wCW (w_add_c xh yh) l
    | C1 l => wCW (w_add_carry_c xh yh) l
    end
  end.
 Let add_c := ww_add_c.

 Definition ww_add := 
   fun x y => without_c (add_c x y).
 Let add := ww_add.

 Definition ww_add_carry_c x y :=
  match x, y with
  | W0, W0 => C0 ww_1
  | W0, WW yh yl =>
    match w_succ_c yl with
    | C0 l => C0 (wWW yh l)
    | C1 l => wCW (w_succ_c yh) l
    end
  | WW xh xl, W0 =>
    match w_succ_c xl with
    | C0 l => C0 (wWW xh l)
    | C1 l => wCW (w_succ_c xh) l
    end
  | WW xh xl, WW yh yl =>
    match w_add_carry_c xl yl with
    | C0 l => wCW (w_add_c xh yh) l
    | C1 l => wCW (w_add_carry_c xh yh) l
    end
  end.
  Let add_carry_c := ww_add_carry_c.

  Definition ww_add_carry x y := without_c (add_carry_c x y).
  Let add_carry := ww_add_carry.

 (* ** Subtractions ** *)

 Definition ww_pred_c x :=
  match x with
  | W0 => C1 ww_Bm1
  | WW xh xl =>
    match w_pred_c xl with
    | C0 l => C0 (wWW xh l)
    | C1 l => wCW (w_pred_c xh) l
    end
  end.
     
 Definition ww_sub_c x y :=
  match y, x with
  | W0, _ => C0 x
  | WW yh yl, W0 => 
    match w_opp_c yl with
    | C0 _ => wCW (w_opp_c yh) w0
    | C1 l => C1 (wWW (w_opp_carry yh) l)
    end
  | WW yh yl, WW xh xl =>
    match w_sub_c xl yl with
    | C0 l => wCW (w_sub_c xh yh) l
    | C1 l => wCW (w_sub_carry_c xh yh) l
    end
  end.
 Let sub_c := ww_sub_c.

 Definition ww_sub x y := without_c (sub_c x y).
 Let sub := ww_sub.

 Definition ww_sub_carry_c x y :=
  match y, x with
  | W0, W0 => C1 ww_Bm1
  | W0, WW xh xl => 
    match w_pred_c xl with
    | C0 l => C0 (wWW xh l)
    | C1 l => wCW (w_pred_c xh) l
    end  
  | WW yh yl, W0 => C1 (wWW (w_opp_carry yh) (w_opp_carry yl))
  | WW yh yl, WW xh xl =>
    match w_sub_carry_c xl yl with
    | C0 l => wCW (w_sub_c xh yh) l
    | C1 l => wCW (w_sub_carry_c xh yh) l
    end
  end.

 (* ** Multiplication ** *)

 (*   (xh*B+xl) (yh*B + yl)
   xh*yh         = hh  = |hhh|hhl|B2
   xh*yl +xl*yh  = cc  =     |cch|ccl|B
   xl*yl         = ll  =         |llh|lll 
 *)

 Definition ww_mul_c x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0
  | WW xh xl, WW yh yl =>
    let hh := w_mul_c xh yh in
    let ll := w_mul_c xl yl in
    let cc_c := add_c (w_mul_c xh yl) (w_mul_c xl yh) in 
    let (wc,cc) :=
      match cc_c with
      | C0 cc => (w0, cc)
      | C1 cc => (w1, cc)
      end
    in match cc with
    | W0 => WW (add hh (WW wc w0)) ll
    | WW cch ccl =>
      match add_c (WW ccl w0) ll with
      | C0 l => WW (add hh (WW wc cch)) l
      | C1 l => WW (add_carry hh (WW wc cch)) l
      end
    end
  end.

 Let kara_prod cxhl cyhl hh ll :=
  match cxhl, cyhl with
  | C0 xhl, C0 yhl => (w0, sub (sub (w_mul_c xhl yhl) hh) ll)
  | C0 xhl, C1 yhl => 
    match add_c (w_mul_c xhl yhl) (WW xhl w0) with
    | C0 m => (w0, sub (sub m hh) ll)
    | C1 m => (* carry = 1 *)
      match sub_c m hh with
      | C0 mhh =>
	match sub_c mhh ll with
        | C0 mhhll => (w1, mhhll)
        | C1 mhhll => (w0, mhhll)
        end
      | C1 mhh =>  (w0, sub mhh ll)
      end
    end
  | C1 xhl, C0 yhl => 
    match add_c (w_mul_c xhl yhl) (WW yhl w0) with
    | C0 m => (w0, sub (sub m hh) ll)
    | C1 m => (* carry = 1 *)
      match sub_c m hh with
      | C0 mhh =>
	match sub_c mhh ll with
        | C0 mhhll => (w1, mhhll)
        | C1 mhhll => (w0, mhhll)
        end
      | C1 mhh =>  (w0, sub mhh ll)
      end
    end
  | C1 xhl, C1 yhl => (* carry = 1 *)
    match w_add_c xhl yhl with
    | C0 suml =>      (* carry = 1 *)
      match add_c (w_mul_c xhl yhl) (WW suml w0) with
      | C0 m =>       (* carry = 1 *)
	match sub_c m hh with
	| C0 mhh =>
	  match sub_c mhh ll with
          | C0 mhhll => (w1, mhhll)
          | C1 mhhll => (w0, mhhll)
          end
        | C1 mhh =>  (w0, sub mhh ll)
        end
      | C1 m =>       (* carry = 2 *)  
	match sub_c m hh with
	| C0 mhh =>   (* carry = 2 => -ll a yn carry de 1 *)
          (w1,sub mhh ll)
        | C1 mhh =>  (* carry = 1 *)
          match sub_c mhh ll with
          | C0 mhhll => (w1, mhhll)
          | C1 mhhll => (w0, mhhll)
          end
        end
      end
    | C1 suml =>      (* carry = 2 *)
      match add_c (w_mul_c xhl yhl) (WW suml w0) with
      | C0 m =>       (* carry = 2 *) 
	match sub_c m hh with
	| C0 mhh =>  (* carry = 2 => -ll a yn carry de 1 *)
	  (w1,  sub mhh ll)
        | C1 mhh => (* carry = 1 *)
          match sub_c mhh ll with
          | C0 mhhll => (w1, mhhll)
          | C1 mhhll => (w0, mhhll)
          end  
        end
      | C1 m =>       (* carry = 3 => les deux soutraction on une carry *)
        (w1, sub (sub m hh) ll)
      end
    end
  end.

 Definition ww_karastuba_c x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0
  | WW xh xl, WW yh yl =>
    let hh := w_mul_c xh yh in
    let ll := w_mul_c xl yl in
    let (wc,cc) := kara_prod (w_add_c xh xl) (w_add_c yh yl) hh ll in
    match cc with
    | W0 => WW (add hh (WW wc w0)) ll
    | WW cch ccl =>
      match add_c (WW ccl w0) ll with
      | C0 l => WW (add hh (WW wc cch)) l
      | C1 l => WW (add_carry hh (WW wc cch)) l
      end
    end
  end.
 
 Definition ww_mul x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0  
  | WW xh xl, WW yh yl => 
    let ccl := w_add (w_mul xh yl) (w_mul xl yh) in
    add (WW ccl w0) (w_mul_c xl yl)
  end.

 (*   (xh*B+xl) (yh*B + yl)
   xh*yh         = hh  = |hhh|hhl|B2
   xh*yl +xl*yh  = cc  =     |cch|ccl|B
   xl*yl         = ll  =         |llh|lll 
 *)

 Definition ww_square_c x  :=
  match x with
  | W0 => W0
  | WW xh xl =>
    let hh := w_square_c xh in
    let ll := w_square_c xl in
    let xhxl := w_mul_c xh xl in
    let (wc,cc) :=
      match add_c xhxl xhxl with
      | C0 cc => (w0, cc)
      | C1 cc => (w1, cc)
      end in
    match cc with
    | W0 => WW (add hh (WW wc w0)) ll
    | WW cch ccl =>
      match add_c (WW ccl w0) ll with
      | C0 l => WW (add hh (WW wc cch)) l
      | C1 l => WW (add_carry hh (WW wc cch)) l
      end
    end
  end.


 (* Division operation *)

 Let w_carry_mul cx y :=
  match cx with
  | C0 x => w_mul_c x y
  | C1 x => add (w_mul_c x y) (wWW y w0)
  end.

 Let w_carry_pred_c cx :=
  match cx with
  | C0 x => C0 (without_c (w_pred_c x))
  | C1 x =>
    match w_pred_c x with
    | C0 p => C1 p
    | C1 p => C0 p
    end
  end.

 Definition w_div32 a1 a2 a3 b1 b2 :=
  let (q,s) := w_div21 a1 a2 b1 in
  let d := w_carry_mul q b2 in
  match sub_c (wWW s a3) d with
  | C0 r => (q, r)
  | C1 r => (* cas negatif *)
    let b := (wWW b1 b2) in
    let q1 := w_carry_pred_c q in
    match add_c r b with
    | C0 r1 => (* 2eme cas negatif *)
       (w_carry_pred_c q1, add r1 b)
    | C1 r1 => (q1,r1)
    end
  end.
 Let div32 := w_div32.

 Let wCC wh wl := 
  match wl with
  | C0 l => wCW wh l
  | C1 l => wCW (w_succ_c (without_c wh)) l
  end.

 Definition ww_split x :=
  match x with
  | W0 => (w0,w0)
  | WW h l => (h, l)
  end.
 Let split := ww_split.

 Definition ww_div21 :=
  let compare := ww_compare in
  fun a1 a2 b =>
  match a1, a2 with
  | W0, W0 => (C0 W0, W0)
  | WW h1 h2, W0 =>
    let (b1, b2) := split b in
    let (q1, r) := div32 h1 h2 w0 b1 b2 in
    let (r1, r2) := split r in 
    let (q2,s) := div32 r1 r2 w0 b1 b2 in
    (wCC q1 q2, s)
  | W0, WW l1 l2 =>
    match compare a2 b with
    | Gt => (C0 ww_1, sub a2 b)
    | _ => (C0 W0, a2)
    end
  | WW h1 h2, WW l1 l2 =>
    let (b1, b2) := split b in
    let (q1, r) := div32 h1 h2 l1 b1 b2 in
    let (r1, r2) := split r in 
    let (q2,s) := div32 r1 r2 l2 b1 b2 in
    (wCC q1 q2, s)
  end.

 (* 0 < p < ww_digits *)
 Definition ww_add_mul_div x y p := 
  match x, y with
  | W0, W0 => W0
  | W0, WW yh yl =>
    match Pcompare p w_digits Eq with
    | Eq => wWW w0 yh 
    | Lt =>
      let n := Pminus w_digits p in
      wWW w0 (w_add_mul_div w0 yh p)
    | Gt =>
      let n := Pminus p w_digits in
      wWW (w_add_mul_div w0 yh n) (w_add_mul_div yh yl n)
    end
  | WW xh xl, W0 =>
   match Pcompare p w_digits Eq with
    | Eq => wWW xl w0 
    | Lt =>
      let n := Pminus w_digits p in
      wWW (w_add_mul_div xh xl p) (w_add_mul_div xl w0 p)
    | Gt =>
      let n := Pminus p w_digits in
      wWW (w_add_mul_div xl w0 n) w0
    end
  | WW xh xl, WW yh yl =>
    match Pcompare p w_digits Eq with
    | Eq => wWW xl yh 
    | Lt =>
      let n := Pminus w_digits p in
      wWW (w_add_mul_div xh xl p) (w_add_mul_div xl yh p)
    | Gt =>
      let n := Pminus p w_digits in
      wWW (w_add_mul_div xl yh n) (w_add_mul_div yh yl n)
    end
  end.


 (* ** Record of operators on 2 words *)
   
 Definition mk_zn2z_op := 
  mk_znz_op ww_digits
    ww_to_Z ww_of_pos ww_head0
    W0 ww_1 ww_Bm1
    ww_WW ww_CW 
    ww_compare
    ww_opp_c ww_opp_carry
    ww_succ_c
    ww_add_c ww_add_carry_c ww_add
    ww_pred_c
    ww_sub_c ww_sub_carry_c ww_sub
    ww_mul_c ww_mul
    ww_square_c   
    ww_div21 ww_add_mul_div.

 Definition mk_zn2z_op_karastuba := 
  mk_znz_op ww_digits
    ww_to_Z ww_of_pos ww_head0
    W0 ww_1 ww_Bm1
    ww_WW ww_CW 
    ww_compare
    ww_opp_c ww_opp_carry
    ww_succ_c
    ww_add_c ww_add_carry_c ww_add
    ww_pred_c
    ww_sub_c ww_sub_carry_c ww_sub
    ww_karastuba_c ww_mul ww_square_c
    ww_div21 ww_add_mul_div.

End Zn2Z. 
 (* ********************************************************** *)
 (* **                    The Proofs ...                    ** *)
 (* ********************************************************** *)

Section Proof.
 Variable w:Set.
 Variable w_op : znz_op w.
 Variable op_spec : znz_spec w_op.

 Notation "[| x |]" := (znz_to_Z w_op x)  (at level 0, x at level 99).
 
 Notation wB := (base (znz_digits w_op)).

 Notation "[+| c |]" := 
   (interp_carry 1 wB (znz_to_Z w_op) c)  (at level 0, x at level 99).

 Notation "[-| c |]" := 
   (interp_carry (-1) wB (znz_to_Z w_op) c)  (at level 0, x at level 99).

 Notation "[[ x ]]" := 
   (ww_to_Z w_op x)  (at level 0, x at level 99).

 Notation wwB := (base (xO (znz_digits w_op))).

 Notation "[+[ c ]]" := 
   (interp_carry 1 wwB (ww_to_Z w_op) c)  (at level 0, x at level 99).

 Notation "[-[ c ]]" := 
   (interp_carry (-1) wwB (ww_to_Z w_op) c)  (at level 0, x at level 99).

 Notation "[|| x ||]" := 
   (zn2z_to_Z wwB (ww_to_Z w_op) x)
   (at level 0, x at level 99).

 Hint Rewrite 
    (spec_0 op_spec)
    (spec_1 op_spec)
    (spec_Bm1 op_spec)
    (spec_WW op_spec)
    (spec_CW op_spec)
    (spec_opp_c op_spec)
    (spec_opp_carry op_spec)
    (spec_succ_c op_spec)
    (spec_add_c op_spec)
    (spec_add_carry_c op_spec)
    (spec_add op_spec)
    (spec_pred_c op_spec)
    (spec_sub_c op_spec)
    (spec_sub_carry_c op_spec)
    (spec_sub op_spec)
    (spec_mul_c op_spec)
    (spec_mul op_spec)
    : w_rewrite.

 Ltac zarith := auto with zarith. 
 Ltac w_rewrite := autorewrite with w_rewrite.
 Ltac w_solve := trivial;w_rewrite;trivial;try ring;try omega.

 Lemma wwB_wBwB : wwB = wB * wB.
 Proof.
  unfold base;rewrite (Zpos_xO (znz_digits w_op)).
  replace  (2 * Zpos (znz_digits w_op)) with 
    (Zpos (znz_digits w_op) + Zpos (znz_digits w_op)).
  apply Zpower_exp; unfold Zge;simpl;intros;discriminate.
  ring.
 Qed.

 Hint Rewrite wwB_wBwB : w_rewrite1.

 Ltac w_rewrite1 := autorewrite with w_rewrite w_rewrite1.
 Ltac w_solve1 := trivial;w_rewrite1;trivial;try ring;try omega.

 Lemma spec_ww_to_Z   : forall x, 0 <= [[ x ]] < wwB.
 Proof with w_solve1.
  destruct x;simpl.
  split... 
  destruct (spec_to_Z op_spec (znz_0 w_op)); apply Zmult_lt_O_compat...
  destruct (spec_to_Z op_spec w0);destruct (spec_to_Z op_spec w1)...
  split.
  change 0 with (0+0);apply Zplus_le_compat...
  apply Zmult_le_0_compat ...
  apply Zle_lt_trans with (wB*wB - 1) ...
  replace (wB*wB - 1) with (wB*(wB - 1) + (wB - 1)) ...
  apply Zplus_le_compat...  apply Zmult_le_compat ...
 Qed.
  
 Axiom spec_ww_of_pos : forall p, 
       Zpos p = 
        (Z_of_N (fst (ww_of_pos w_op p)))*wB + [[(snd (ww_of_pos w_op p))]].

 Lemma spec_ww_0   : [[W0]] = 0.
 Proof. trivial. Qed.

 Lemma spec_ww_1   : [[WW (znz_0 w_op) (znz_1 w_op)]] = 1.
 Proof. simpl;w_solve. Qed.

 Lemma spec_ww_Bm1 : [[WW (znz_Bm1 w_op) (znz_Bm1 w_op)]] = wwB - 1.
 Proof. simpl;w_solve1. Qed.

 Lemma spec_ww_WW  : forall h l, [||ww_WW h l||] = [[h]] * wwB + [[l]].
 Proof with w_solve1.
  intros;simpl;unfold ww_WW.
  destruct h;simpl ... destruct l;simpl ...
 Qed.

 Hint Rewrite spec_ww_0 spec_ww_1 spec_ww_Bm1 spec_ww_WW : w_rewrite.

 Lemma spec_ww_CW  : 
   forall sign c l, 
    interp_carry sign (wwB*wwB) (zn2z_to_Z wwB (ww_to_Z w_op)) (ww_CW c l) =
        (interp_carry sign wwB (ww_to_Z w_op) c)* wwB + [[l]].
 Proof with w_solve.
  intros sign c l;destruct c;simpl ...
 Qed.

 Lemma spec_ww_hl: forall h l, [[WW h l]] = wB * [|h|] + [|l|].
intros; simpl; auto.
Qed.
Hint Rewrite spec_ww_hl: w_rewrite.

    (*    Auxillary lemmas *)

Theorem beta_lex: forall a b c d beta, beta * a + b <= beta * c + d -> 0 <= b < beta -> 0 <= d < beta -> a <= c.
intros a b c d beta H1 (H3, H4) (H5, H6).
assert (a - c < 1); auto with zarith.
apply Zmult_lt_reg_r with beta; auto with zarith.
repeat rewrite (fun x => Zmult_comm x beta).
apply Zle_lt_trans with (d  - b); auto with zarith.
rewrite Zmult_minus_distr_l; auto with zarith.
Qed.

Theorem beta_lex_inv: forall a b c d beta, a < c -> 0 <= b < beta -> 0 <= d < beta -> beta * a + b < beta * c + d. 
intros a b c d beta H1 (H3, H4) (H5, H6).
case (Zle_or_lt (beta * c + d) (beta * a + b)); auto with zarith.
intros H7; contradict H1; apply Zle_not_lt; apply beta_lex with (1 := H7); auto.
Qed.

Theorem wB_lex: forall a b c d, wB * a + b <= wB * c + d -> 0 <= b < wB -> 0 <= d < wB -> a <= c.
intros a b c d H1 H2 H3; apply beta_lex with (1 := H1); auto.
Qed.

Theorem wB_lex_inv: forall a b c d, a < c -> 0 <= b < wB -> 0 <= d < wB -> wB * a + b < wB * c + d. 
intros a b c d H1 H2 H3; apply beta_lex_inv with (1 := H1); auto.
Qed.

Theorem wBwB_lex: forall a b c d, wB * wB * a + b <= wB * wB * c + d -> 0 <= b < wB * wB -> 0 <= d < wB * wB -> a <= c.
intros a b c d H1 H2 H3; apply beta_lex with (1 := H1); auto.
Qed.

Theorem wBwB_lex_inv: forall a b c d, a < c -> 0 <= b < wB * wB -> 0 <= d < wB * wB -> wB * wB * a + b < wB * wB * c + d. 
intros a b c d H1 H2 H3; apply beta_lex_inv with (1 := H1); auto.
Qed.

    (* Comparison *)

 Lemma spec_ww_compare :
     forall x y, 
       match ww_compare w_op x y with
       | Eq => [[x]] = [[y]]
       | Lt => [[x]] < [[y]]
       | Gt => [[x]] > [[y]]
       end.
 Proof with w_solve.
  destruct x as [ |xh xl].

  destruct y as [ | yh yl];simpl ...
  destruct (spec_to_Z op_spec yl);destruct (spec_to_Z op_spec yh).
  assert (Hyh := spec_compare op_spec (znz_0 w_op) yh);
    destruct (znz_compare w_op (znz_0 w_op) yh).
  rewrite <-Hyh ...
  repeat rewrite Zmult_0_r. 
  pattern 0 at 1 3 5;rewrite <- (spec_0 op_spec).
  exact (spec_compare op_spec (znz_0 w_op) yl).
  change 0 with (0+0);apply Zplus_lt_le_compat ...
  apply Zmult_lt_O_compat...
  rewrite (spec_0 op_spec) in Hyh ...
  rewrite (spec_0 op_spec) in Hyh ...

  destruct (spec_to_Z op_spec xl);destruct (spec_to_Z op_spec xh).
  destruct y as [ | yh yl];simpl ...
  assert (Hxh := spec_compare op_spec xh (znz_0 w_op));
    destruct (znz_compare w_op xh (znz_0 w_op)).
  rewrite Hxh. rewrite (spec_0 op_spec).
  repeat rewrite Zmult_0_r. 
  pattern 0 at 2 4 6;rewrite <- (spec_0 op_spec).
  exact (spec_compare op_spec xl (znz_0 w_op)).
  rewrite (spec_0 op_spec) in Hxh ...
  rewrite (spec_0 op_spec) in Hxh; apply Zlt_gt.
  change 0 with (0+0);apply Zplus_lt_le_compat ...
  apply Zmult_lt_0_compat...

  destruct (spec_to_Z op_spec yl);destruct (spec_to_Z op_spec yh).
  assert (Hh := spec_compare op_spec xh yh);destruct (znz_compare w_op xh yh).
  rewrite Hh.   
  assert (Hl := spec_compare op_spec xl yl);
    destruct (znz_compare w_op xl yl)...
  apply wB_lex_inv; auto.
  apply Zlt_gt; apply wB_lex_inv; auto with zarith.
 Qed.

    (* Basic arithmetic operations *)
 Lemma spec_ww_opp_c : forall x, [-[ww_opp_c w_op x]] = -[[x]].
 Proof with w_solve1.
  destruct x;simpl ...
  assert (H1:=spec_opp_c op_spec w1);destruct (znz_opp_c w_op w1).
  simpl in H1.
  assert (znz_to_Z w_op w1 = 0). 
   destruct (spec_to_Z op_spec w2);destruct (spec_to_Z op_spec w1)...
  rewrite H...
  unfold interp_carry, ww_to_Z in * ...
 Qed.

 Lemma spec_ww_opp_carry : forall x, [[ww_opp_carry w_op x]] = wwB - [[x]] - 1.
 Proof. unfold ww_to_Z;destruct x;simpl; w_solve1. Qed.

 Lemma spec_ww_succ_c : forall x, [+[ww_succ_c w_op x]] = [[x]] + 1.
 Proof with w_solve.
  destruct x;simpl. w_solve.
  assert (H1:=spec_succ_c op_spec w1);destruct (znz_succ_c w_op w1).
  unfold interp_carry in * ...
  rewrite Zplus_assoc. rewrite (Zplus_comm 1);rewrite <- H1.
  unfold ww_to_Z;simpl...
  assert (H2:=spec_succ_c op_spec w0);destruct (znz_succ_c w_op w0);
   simpl;w_rewrite1.
  rewrite H2; unfold interp_carry in * ...
  rewrite H2; unfold interp_carry in * ... 
 Qed.

 Hint Rewrite spec_ww_opp_c spec_ww_opp_carry spec_ww_succ_c : w_rewrite.

 Lemma spec_ww_add_c  : forall x y, [+[ww_add_c w_op x y]] = [[x]] + [[y]].
 Proof with w_solve1.
  destruct x;simpl ...
  destruct y;simpl ...
  assert (H1:=spec_add_c op_spec w1 w3);destruct (znz_add_c w_op w1 w3);
   unfold interp_carry in H1 ...
 Qed.

 Lemma spec_ww_add_carry_c : 
   forall x y, [+[ww_add_carry_c w_op x y]] = [[x]] + [[y]] + 1.
 Proof with w_solve1.
  destruct x;simpl;intros y.
  fold (ww_succ_c w_op y)...
  destruct y;simpl.
  fold (ww_succ_c w_op (WW w0 w1)) ... simpl ...
  assert (H1:=spec_add_carry_c op_spec w1 w3);
    destruct (znz_add_carry_c w_op w1 w3);unfold interp_carry in H1 ...
 Qed.

 Hint Rewrite spec_ww_add_c spec_ww_add_carry_c : w_rewrite.


 Lemma spec_without_c : 
  forall (w:Set) B (interp:w->Z), (forall w, 0 <= interp w < B) ->
   forall sign c,
   interp (without_c c) = (interp_carry sign B interp c) mod B.
 Proof.
  intros;destruct c;simpl.
  rewrite Zmod_def_small;trivial.
  rewrite Zplus_comm;rewrite Z_mod_plus.
  rewrite Zmod_def_small;trivial.
  assert (H1 := H w1);omega.
 Qed.

 Lemma spec_ww_add : 
  forall x y, [[ww_add w_op x y]] = ([[x]] + [[y]]) mod wwB.
 Proof.
  intros x y;unfold ww_add.
  rewrite <- (spec_ww_add_c x y).
  apply (spec_without_c (ww_to_Z w_op) spec_ww_to_Z 1).
 Qed.
 Hint Rewrite spec_ww_add : w_rewrite.

 Opaque Zmult.
 
 Lemma spec_ww_pred_c : forall x, [-[ww_pred_c w_op x]] = [[x]] - 1.
 Proof with w_solve1.
  destruct x;simpl...
  assert (H:= spec_pred_c op_spec w1);destruct (znz_pred_c w_op w1).
  unfold interp_carry,ww_to_Z in * ...
  unfold interp_carry in H;w_solve1.
 Qed.

 Hint Rewrite spec_ww_pred_c : w_rewrite.

 Lemma spec_ww_sub_c : forall x y, [-[ww_sub_c w_op x y]] = [[x]] - [[y]].
 Proof with w_solve.
  destruct y;simpl ...
  destruct x.
  fold (ww_opp_c w_op (WW w0 w1)) ... simpl ...
  assert (H:= spec_sub_c op_spec w3 w1);destruct (znz_sub_c w_op w3 w1);
  unfold interp_carry in H;simpl;w_solve1.
 Qed.

 Lemma spec_ww_sub_carry_c : 
   forall x y, [-[ww_sub_carry_c w_op x y]] = [[x]] - [[y]] - 1.
 Proof with w_solve.
  destruct y;simpl.
  fold (ww_pred_c w_op x) ...
  destruct x;unfold ww_to_Z;simpl;w_solve1.
  assert (H1:=spec_sub_carry_c op_spec w3 w1);
    destruct (znz_sub_carry_c w_op w3 w1);unfold interp_carry in H1 ...
 Qed.

 Hint Rewrite spec_ww_sub_c spec_ww_sub_carry_c : w_rewrite.
 
 Lemma spec_ww_sub : 
  forall x y, [[ww_sub w_op x y]] = ([[x]] - [[y]]) mod wwB.
 Proof.
  intros x y;unfold ww_sub.
  rewrite <- (spec_ww_sub_c x y).
  apply (spec_without_c (ww_to_Z w_op) spec_ww_to_Z (-1)).
 Qed.
 Hint Rewrite spec_ww_add : w_rewrite.

 Lemma Zmult_lt_b : 
   forall b x y, 0 <= x < b -> 0 <= y < b -> 0 <= x * y <= b*b - 2*b + 1.
 Proof with zarith.
  intros b x y (Hx1,Hx2) (Hy1,Hy2);split...
  apply Zle_trans with ((b-1)*(b-1)).
  apply Zmult_le_compat...
  apply Zeq_le;ring.
 Qed.

 Ltac zmult_lt_b x y := 
   let H := fresh "H" in
   assert (H := Zmult_lt_b (spec_to_Z op_spec x)  (spec_to_Z op_spec y)).
 Ltac spec_to_Z x := 
   let H := fresh "H" in
   assert (H := spec_to_Z op_spec x).

Axiom wB_pos: 1 < wB.
Hint Resolve wB_pos.

Theorem wwB_pos: 1 < wwB.
rewrite wwB_wBwB.
rewrite <- (Zmult_1_r 1).
apply Zmult_lt_compat; auto with zarith.
generalize wB_pos; auto with zarith.
Qed.
Hint Resolve wwB_pos.

 Lemma sum_mul_carry : forall xh xl yh yl wc cc,
   [|wc|]*wB*wB + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] -> 
   0 <= [|wc|] <= 1.
 Proof.
  intros. zmult_lt_b xh yl;zmult_lt_b xl yh;spec_to_Z wc.
  assert (H3 := spec_ww_to_Z cc). split;zarith.
  apply wBwB_lex with (b := [[cc]]) (d := wB * wB - 2); auto with zarith.
  rewrite (Zmult_comm (wB * wB)); rewrite Zmult_assoc; auto with zarith.
  rewrite <- wwB_wBwB; auto with zarith.
  generalize wB_pos; auto with zarith.
 Qed.

Axiom ok: forall P, P.

Theorem mult_add_ineq: forall xH yH crossH, 0 <= [|xH|] * [|yH|] + [|crossH|] < wwB.
intros xH yH crossH.
generalize (spec_to_Z op_spec xH); intros HH.
generalize (spec_to_Z op_spec yH); intros HH1.
generalize (spec_to_Z op_spec crossH); intros HH2.
split; auto with zarith.
rewrite wwB_wBwB.
apply Zle_lt_trans with  ((wB - 1) * (wB - 1) + (wB -1)); auto with zarith.
apply Zplus_le_compat; auto with zarith.
apply Zmult_le_compat; auto with zarith.
repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); auto with zarith.
Qed.
Hint Resolve mult_add_ineq.

Theorem C1_plus: forall z,  [+[C1 z]] = wwB + [[z]].
  intros zz; simpl; case wwB; auto with zarith.
Qed.

Hint Rewrite C1_plus: w_rewrite.


Theorem spec_ww_add_carry: forall x y, [[ww_add_carry w_op x y]] = ([[x]] + [[y]] + 1) mod wwB.
  intros x y.
  unfold ww_add_carry, without_c; simpl.
  generalize (spec_ww_add_carry_c x y); case (ww_add_carry_c w_op x y); intro z;
  generalize (spec_ww_to_Z z); intros HH;
  autorewrite with w_rewrite; simpl; intros Hz; rewrite <- Hz.
  rewrite Zmod_def_small ; auto with zarith.
  pattern wwB at 1; rewrite <- Zmult_1_l; rewrite Zplus_comm; rewrite Z_mod_plus; 
     try rewrite Zmod_def_small; auto with zarith.
Qed.

 Lemma spec_mul_aux : forall xh xl yh yl wc (cc:zn2z w) hh ll,
   [[hh]] = [|xh|] * [|yh|] ->
   [[ll]] = [|xl|] * [|yl|] ->
   [|wc|]*wB*wB + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] ->
   [|| 
     match cc with
     | W0 => WW (ww_add w_op hh (WW wc (znz_0 w_op))) ll
     | WW cch ccl =>
     match ww_add_c w_op (WW ccl (znz_0 w_op)) ll with
       | C0 l => WW (ww_add w_op hh (WW wc cch)) l
       | C1 l => WW (ww_add_carry w_op hh (WW wc cch)) l
       end
     end ||] = [[WW xh xl]]*[[WW yh yl]].
 Proof with w_solve1.
  intros. 
  generalize (spec_to_Z op_spec xh); intros HH.
  generalize (spec_to_Z op_spec yh); intros HH1.
  generalize (spec_to_Z op_spec xl); intros HH2.
  generalize (spec_to_Z op_spec yl); intros HH3.
  generalize (spec_ww_to_Z hh); intros HH4.
  generalize (spec_ww_to_Z ll); intros HH5.
  generalize (sum_mul_carry _ _ _ _ _ _ H1); intros HH6.
   apply trans_equal with 
     ([|xh|]*[|yh|]*wB*wB + ([|xh|]*[|yl|]+[|xl|]*[|yh|])*wB +[|xl|]*[|yl|]).
  2:simpl...
  rewrite <- H;rewrite <- H0;rewrite <- H1.
  assert (H3 := Zmult_lt_b (spec_to_Z op_spec xh)  (spec_to_Z op_spec yh)).
  rewrite <- H in H3;destruct H3.
  assert (H5 := Zmult_lt_b (spec_to_Z op_spec xl)  (spec_to_Z op_spec yl)).
  rewrite <- H0 in H5;destruct H5.
  assert (H7 := Zmult_lt_b (spec_to_Z op_spec xh)  (spec_to_Z op_spec yl)).
  destruct H7.
  assert (HH8: 0 <= [[hh]] + wB * [|wc|] < wB * wB).
  split; auto with zarith.
  replace (wB * wB) with ((wB * wB - wB)  + wB); auto with zarith.
  apply Zplus_lt_le_compat; auto with zarith.
  rewrite H.
  apply Zle_lt_trans with ((wB -1) * (wB - 1)); auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); auto with zarith.
  generalize (wB_pos); auto with zarith.
  pattern wB at 2; rewrite <- Zmult_1_r; auto with zarith.
  destruct cc.
  simpl; autorewrite with w_rewrite.
  rewrite wwB_wBwB; rewrite Zmod_def_small; auto with zarith.
  ring.
  generalize (spec_to_Z op_spec w0); intros HH9.
  generalize (spec_to_Z op_spec w1); intros HH10.
  assert (U: 0 <= [[hh]] + (wB * [|wc|] + [|w0|]) < wB * wB).
  split; auto with zarith.
  generalize H1; autorewrite with w_rewrite; clear H1; intros H1.
  assert (wB * [|wc|] + [|w0|] < 2 * wB - 1); auto with zarith.
  apply Zmult_lt_reg_r with wB; auto with zarith.
  rewrite (Zmult_comm wB); rewrite Zmult_plus_distr_l; rewrite (Zmult_comm [|w0|]).
  apply Zplus_lt_reg_r with [|w1|].
  rewrite <- Zplus_assoc; rewrite H1.
  apply Zle_lt_trans with ((wB - 1) * (wB - 1) + (wB - 1) * (wB - 1)); auto with zarith.
  apply Zplus_le_compat; apply Zmult_le_compat; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); auto with zarith.
  repeat (rewrite Zmult_1_l || rewrite Zmult_1_r); auto with zarith.
  rewrite <- Zmult_assoc; auto with zarith.
  generalize (spec_ww_add_c  (WW w1 (znz_0 w_op)) ll); 
  case  (ww_add_c w_op (WW w1 (znz_0 w_op)) ll).
  simpl; autorewrite with w_rewrite.
  intros z Hz; rewrite Hz.
  rewrite wwB_wBwB; rewrite Zmod_def_small; auto with zarith.
  ring.
  autorewrite with w_rewrite.
  intros z Hz;  rewrite wwB_wBwB;  simpl.
  rewrite C1_plus in Hz; rewrite wwB_wBwB in Hz.
  rewrite spec_ww_add_carry; rewrite Zmod_def_small; auto with zarith;
    autorewrite with w_rewrite.
  match goal with |- ?X = _ =>
    match type of Hz with ?Y = _ => apply trans_equal with (Y - Y + X);
         [idtac | pattern Y at 1; rewrite Hz]; ring
   end end.
  autorewrite with w_rewrite; split; auto with zarith.
  apply Zmult_lt_reg_r with wwB; auto with zarith.
  generalize (spec_ww_to_Z z); intros HH11.
  match goal with |- ?X  < _ =>
    apply Zle_lt_trans with (X + [[z]])
   end; auto with zarith.
  generalize (spec_ww_to_Z (WW xh xl)); intros HH12.
  generalize (spec_ww_to_Z (WW yh yl)); intros HH13.
  match goal with |- ?X  < _ =>
    replace X with ((wB * [|xh|] + [|xl|]) * (wB * [|yh|] + [|yl|]))
  end; auto with zarith.
  apply Zle_lt_trans with ((wwB - 1) * (wwB - 1)); auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  simpl in HH12; auto with zarith.
  simpl in HH13; auto with zarith.
  repeat (rewrite Zmult_minus_distr_l || rewrite Zmult_minus_distr_r); auto with zarith.
  rewrite wwB_wBwB.
  match goal with |-  _ = ?X =>
    match type of Hz with ?Y = _ => apply trans_equal with (Y - Y + X);
         [pattern Y at 1; rewrite Hz | ring]
   end end.
  rewrite H; rewrite H0.
  match goal with |-  ?X = _  =>
    match type of H1 with _ = ?Y => apply trans_equal with (wB * (Y - Y) + X);
         [ring | pattern Y at 1; rewrite <- H1]
   end end.
  autorewrite with w_rewrite; ring.
Qed.

Theorem spec_ww_mul_c : forall x y, [|| ww_mul_c w_op x y ||] = [[x]] * [[y]].
  intros x y; case x; auto; intros xh xl.
  case y; auto; try ring; intros yh yl.
  match goal with |- _ = ?X => set (tmp:= X); simpl; unfold tmp end.
  set (hh :=  (znz_mul_c w_op xh yh)).
  set (ll  :=  (znz_mul_c w_op xl yl)).
  generalize (spec_ww_add_c (znz_mul_c w_op xh yl) (znz_mul_c w_op xl yh)).
  case (ww_add_c w_op (znz_mul_c w_op xh yl) (znz_mul_c w_op xl yh)).
  intros wc Hwc.
  apply  spec_mul_aux with (cc := wc) (wc := w_op.(znz_0)) (hh := hh) (ll := ll).
  unfold hh; unfold ww_to_Z; apply spec_mul_c; auto.
  unfold ll; unfold ww_to_Z; apply spec_mul_c; auto.
  simpl in Hwc; rewrite Hwc; autorewrite with w_rewrite.
  unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  intros z; case z.
  autorewrite with w_rewrite; simpl.
  autorewrite with w_rewrite; simpl.
  intros H.
  unfold ww_to_Z in H; rewrite spec_mul_c in H; auto.
  unfold ww_to_Z in H; rewrite spec_mul_c in H; auto.
  rewrite Zmod_def_small.
  rewrite wwB_wBwB in H; rewrite wwB_wBwB.
  unfold hh, ll; unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  match goal with |-  _ = ?X =>
    match type of H with _ = ?Y => apply trans_equal with (wB * (Y - Y) + X);
         [pattern Y at 1; rewrite <- H | idtac]; ring
   end end.
  generalize (spec_to_Z op_spec xh); intros HH.
  generalize (spec_ww_to_Z hh); intros HH1.
  rewrite Zmult_1_r; split; auto with zarith.
  apply Zle_lt_trans with ((wwB - 2 * wB + 1) + (wB + 0)); auto with zarith.
  apply Zplus_le_compat_r.
  unfold hh, ww_to_Z; repeat rewrite spec_mul_c; auto with arith.
  match goal with |- ?X <= ? Y => assert (0 <= X <= Y) end; auto with zarith.
  rewrite wwB_wBwB; apply Zmult_lt_b; w_solve1.
  apply spec_to_Z; auto.
  assert (1 < wB); auto with zarith.
  intros cc1 cc2 Hwc.
  apply  spec_mul_aux with (cc := (WW cc1 cc2)) (wc := w_op.(znz_1)) (hh := hh) (ll := ll).
  unfold hh; unfold ww_to_Z; apply spec_mul_c; auto.
  unfold ll; unfold ww_to_Z; apply spec_mul_c; auto.
  generalize Hwc; w_rewrite.
  unfold ww_to_Z; repeat rewrite spec_mul_c; auto.
  rewrite wwB_wBwB; clear Hwc; intros Hwc; rewrite <- Hwc; ring.
Qed.

Theorem Zmult_mod_distr_l: forall a b c, 0 < a -> 0 < c -> (a * b) mod (a * c) = a * (b mod c).
  intros a b c H Hc.
  apply sym_equal; apply Zmod_unique with (b / c); auto with zarith.
  apply Zmult_lt_0_compat; auto.
  case (Z_mod_lt b c); auto with zarith; intros; split; auto with zarith.
  apply Zmult_lt_compat_l; auto.
  rewrite <- Zmult_assoc; rewrite <- Zmult_plus_distr_r.
  rewrite <- Z_div_mod_eq; auto with zarith.
Qed.

Theorem spec_ww_mul: forall x y, [[ww_mul w_op x y]] = ([[x]] * [[y]]) mod wwB.
  assert (U: 0 < wB).
  apply Zlt_trans with 1; auto with zarith.
  assert (U1: 0 < wwB).
  apply Zlt_trans with 1; auto with zarith.
  intros x y; case x; auto; intros xh xl.
  case y; auto.
 simpl; rewrite Zmult_0_r; rewrite Zmod_def_small; auto with zarith.
 intros yh yl.
 simpl; w_rewrite.
 rewrite <- Zmod_plus; auto with zarith.
 unfold ww_to_Z; rewrite spec_mul_c; auto.
 repeat (rewrite Zmult_plus_distr_l || rewrite Zmult_plus_distr_r).
 rewrite <- Zmult_mod_distr_l; auto with zarith.
 rewrite <- wwB_wBwB; auto with zarith.
 rewrite Zplus_0_r; rewrite Zmod_plus; auto with zarith.
 rewrite Zmod_mod; auto with zarith.
 rewrite <- Zmod_plus; auto with zarith.
  match goal with |- ?X mod _ = _ =>
    rewrite <- Z_mod_plus with (a := X) (b := [|xh|] * [|yh|])
  end; auto with zarith.
  eq_tac; auto; rewrite wwB_wBwB; ring.
Qed.

(*
    
    (* Special divisions operations *)
    spec_ww_div21_fst : forall a1 a2 b, 
     (base (znz_digits ww_op)/2 <= [|b|] ->
     [+|fst (w_div21 a1 a2 b)|] = ([|a1|]*(base (znz_digits ww_op)+[|a2|])/ [|b|];
    spec_ww_div21_snd : forall a1 a2 b, 
     (base (znz_digits ww_op)/2 <= [|b|] ->
     [|snd (w_div21 a1 a2 b)|] = ([|a1|]*(base (znz_digits ww_op)+[|a2|]) mod [|b|];
    spec_ww_add_mul_div : forall x y p,
       0 < Zpos p < Zpos w_digits ->
       [| w_add_mul_div x y p|] =
	 ([|x|] * (Zpower 2 (Zpos p)) + 
          [|y|] / (Zpower 2 ((Zpos w_digits) - (Zpos p)))) mod (base (znz_digits ww_op)
  }.





