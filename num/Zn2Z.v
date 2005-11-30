Unset Boxed Definitions.
Set Implicit Arguments.

Require Import ZArith.
Require Import ZnZ.
Require Import ZAux.

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

 Let w_div21       := w_op.(znz_div21).
 Let w_add_mul_div := w_op.(znz_add_mul_div).

 Let _zn2z := zn2z w.

 Let wB := base w_digits.

 Let ww_digits := xO w_digits.

 Let ww_to_Z := zn2z_to_Z wB w_to_Z.

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
    ww_karastuba_c ww_mul
    ww_div21 ww_add_mul_div.

End Zn2Z. 
 (* ********************************************************** *)
 (* **                    The Proofs ...                    ** *)
 (* ********************************************************** *)

Section Proof.
 Variable w:Set.
 Variable w_op : znz_op w.
 Variable op_spec : znz_spec w_op.

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
 
 Ltac w_rewrite := autorewrite with w_rewrite.
 Ltac zarith := auto with zarith.
 Ltac w_solve := trivial;w_rewrite;trivial;try ring;try omega.

 Let wB := base (znz_digits w_op).

 Let ww_digits := xO (znz_digits w_op).

 Let ww_to_Z := (zn2z_to_Z (base (znz_digits w_op)) (znz_to_Z w_op)).

 Lemma base_xO_w_digits :
   base (xO (znz_digits w_op)) = 
    base (znz_digits w_op) * base (znz_digits w_op).
 Proof.
  unfold base;rewrite (Zpos_xO (znz_digits w_op)).
  replace  (2 * Zpos (znz_digits w_op)) with 
    (Zpos (znz_digits w_op) + Zpos (znz_digits w_op)).
  apply Zpower_exp; unfold Zge;simpl;intros;discriminate.
  ring.
 Qed.
 
 Lemma base_ww_digits :
   base ww_digits = base (znz_digits w_op) * base (znz_digits w_op).
 Proof base_xO_w_digits.
 Hint Rewrite base_xO_w_digits base_ww_digits : w_rewrite.


 Notation "[| x |]" := 
   (zn2z_to_Z (base (znz_digits w_op)) (znz_to_Z w_op) x)
   (at level 0, x at level 99).
  
 Notation "[+| c |]" := 
   (interp_carry 1 (base (xO (znz_digits w_op)))
          (zn2z_to_Z (base (znz_digits w_op)) (znz_to_Z w_op))Z c)  
   (at level 0, x at level 99).

 Notation "[-| c |]" := 
   (interp_carry (-1)  (base (xO (znz_digits w_op))) 
          (zn2z_to_Z (base (znz_digits w_op)) (znz_to_Z w_op)) c)  
   (at level 0, x at level 99).

 Notation "[|| x ||]" := 
   (zn2z_to_Z  (base (xO (znz_digits w_op))) 
          (zn2z_to_Z (base (znz_digits w_op)) (znz_to_Z w_op)) x)  
   (at level 0, x at level 99).

 Lemma spec_ww_to_Z   : forall x, 0 <= [| x |] < base ww_digits.
 Proof with w_solve.
  destruct x;simpl.
  split. zarith. unfold base;apply Zpower_lt_0;zarith.
  destruct (spec_to_Z op_spec w0);destruct (spec_to_Z op_spec w1)...
  split.
  change 0 with (0+0);apply Zplus_le_compat...
  apply Zmult_le_0_compat ...
  assert 
   (base (znz_digits w_op) * znz_to_Z w_op w0 + znz_to_Z w_op w1 <=
    base (znz_digits w_op)*(base (znz_digits w_op)) - 1)...
  replace (base (znz_digits w_op) * base (znz_digits w_op) - 1) with
    (base (znz_digits w_op) * (base (znz_digits w_op) - 1) + 
                (base (znz_digits w_op) - 1)) ...
  apply Zplus_le_compat...
  apply Zmult_le_compat ...
 Qed.
  
 Axiom spec_ww_of_pos : forall p, 
       Zpos p = 
        (Z_of_N (fst (ww_of_pos w_op p)))*wB + [|(snd (ww_of_pos w_op p))|].

 Lemma spec_ww_0   : [|W0|] = 0.
 Proof. trivial. Qed.

 Lemma spec_ww_1   : [|WW (znz_0 w_op) (znz_1 w_op)|] = 1.
 Proof. simpl;w_solve. Qed.

 Lemma spec_ww_Bm1 : [|WW (znz_Bm1 w_op) (znz_Bm1 w_op)|] = base ww_digits - 1.
 Proof. simpl;w_solve. Qed.

 Lemma spec_ww_WW  : forall h l,
    [||ww_WW h l||] = [|h|] * (base ww_digits) + [|l|].
 Proof with w_solve.
  intros;simpl;unfold ww_WW.
  destruct h;simpl ... destruct l;simpl ...
 Qed.

 Hint Rewrite spec_ww_0 spec_ww_1 spec_ww_Bm1 spec_ww_WW : w_rewrite.
 Lemma spec_ww_CW  : 
     forall sign c l, 
       interp_carry sign ((base ww_digits)*(base ww_digits))
         (zn2z_to_Z (base ww_digits) ww_to_Z) (ww_CW c l) =  
       (interp_carry sign (base ww_digits) ww_to_Z c)*
         (base ww_digits) + [|l|].
 Proof with w_solve.
  intros sign c l;destruct c;simpl ...
 Qed.
   
    (* Comparison *)

 Axiom HELP_Laurent : False.

 Ltac HELP_Laurent := elim HELP_Laurent.

 Lemma spec_ww_compare :
     forall x y, 
       match ww_compare w_op x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end.
 Proof with w_solve.
  destruct x as [ |xh xl].

  destruct y as [ | yh yl];simpl ...
  destruct (spec_to_Z op_spec yl);destruct (spec_to_Z op_spec yh).
  assert (Hyh := spec_compare op_spec (znz_0 w_op) yh);
    destruct (znz_compare w_op (znz_0 w_op) yh).
  rewrite <-Hyh. rewrite (spec_0 op_spec).
  repeat rewrite Zmult_0_r. 
  pattern 0 at 1 3 5;rewrite <- (spec_0 op_spec).
  exact (spec_compare op_spec (znz_0 w_op) yl).
  change 0 with (0+0);apply Zplus_lt_le_compat ...
  apply Zmult_lt_0_compat...
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

  HELP_Laurent.
  HELP_Laurent.
 Qed.

    (* Basic arithmetic operations *)
 Lemma spec_ww_opp_c : forall x, [-|ww_opp_c w_op x|] = -[|x|].
 Proof with w_solve.
  destruct x;simpl ...
  assert (H1:=spec_opp_c op_spec w1);destruct (znz_opp_c w_op w1).
  simpl in H1.
  assert (znz_to_Z w_op w1 = 0). 
   destruct (spec_to_Z op_spec w2);destruct (spec_to_Z op_spec w1)...
  rewrite H...
  simpl in H1.
  unfold interp_carry in * ...
  change (-1*znz_to_Z w_op w1) with (-znz_to_Z w_op w1).
  rewrite <- H1 ...
















    spec_ww_opp_carry : forall x, [|w_opp_carry x|] = [-|w_opp_c x|] - 1;

    spec_ww_succ_c : forall x, [+|w_succ_c x|] = [|x|] + 1;
    spec_ww_add_c  : forall x y, [+|w_add_c x y|] = [|x|] + [|y|];
    spec_ww_add_carry_c : forall x y, [+|w_add_carry_c x y|] = [|x|] + [|y|] + 1;
    spec_ww_add : forall x y, [|w_add x y|] = ([|x|] + [|y|]) mod (base (znz_digits ww_op);

    spec_ww_pred_c : forall x, [-|w_pred_c x|] = [|x|] - 1;
    spec_ww_sub_c : forall x y, [-|w_sub_c x y|] = [|x|] - [|y|];
    spec_ww_sub_carry_c : forall x y, [-|w_sub_carry_c x y|] = [|x|] - [|y|] - 1;
    spec_ww_sub : forall x y, [|w_sub x y|] = ([|x|] - [|y|]) mod (base (znz_digits ww_op);
  
    spec_ww_mul_c : forall x y, [|| w_mul_c x y ||] = [|x|] * [|y|];
    spec_ww_mul : forall x y, [|w_mul x y|] = ([|x|] * [|y|]) mod (base (znz_digits ww_op);
    
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





