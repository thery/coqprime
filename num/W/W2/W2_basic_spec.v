Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.



(* ** Proof that the basic functions are correct ** *)

Lemma w2_to_Z_spec : forall x, 0 <= [|x|] < w2_B.
Proof
fun x =>
 match x as x return 0 <= [|x|] < w2_B with
 | OO => conj (Zle_refl 0) (refl_equal Lt)
 | OI => conj (Zle_0_pos 1) (refl_equal Lt)
 | IO => conj (Zle_0_pos 2) (refl_equal Lt)
 | II => conj (Zle_0_pos 3) (refl_equal Lt)
end.

Lemma w2_of_pos_spec : forall p, Zpos p = (Z_of_N (fst (w2_of_pos p)))*w2_B + [|snd (w2_of_pos p)|].
Proof
fun p0 =>
 eq_ind_r (fun z : Z => Zpos p0 = z + [|snd (w2_of_pos p0)|])
 match p0 as p0 return Zpos p0 = w2_B*(Z_of_N (fst (w2_of_pos p0))) + [|snd (w2_of_pos p0)|] with
 | xH => refl_equal (Zpos xH)
 | xO p1 =>
    match p1 as p1 return Zpos (xO p1) = w2_B*(Z_of_N (fst (w2_of_pos (xO p1)))) + [|snd (w2_of_pos (xO p1))|] with
    | xH => refl_equal (Zpos (xO xH))
    | xO p2 =>
      refl_equal (Zpos (xO (xO p2)))
    | xI p2 =>
      refl_equal (Zpos (xO (xI p2)))
    end
 | xI p1 =>
    match p1 as p1 return Zpos (xI p1) = w2_B*(Z_of_N (fst (w2_of_pos (xI p1)))) + [|snd (w2_of_pos (xI p1))|] with
    | xH => refl_equal (Zpos (xI xH))
    | xO p2 =>
      refl_equal (Zpos (xI (xO p2)))
    | xI p2 =>
      refl_equal (Zpos (xI (xI p2)))
    end
 end (Zmult_comm (Z_of_N (fst (w2_of_pos p0))) w2_B).

Lemma w2_0_spec : [|OO|] = 0.
Proof
(refl_equal 0).

Lemma w2_1_spec : [|OI|] = 1.
Proof
(refl_equal 1).

Lemma w2_Bm1_spec : [|II|] = w2_B - 1.
Proof
(refl_equal 3).

Lemma w2_WW_spec : forall h l, [||w2_WW h l||] = [|h|] * w2_B + [|l|].
Proof
fun h l =>
 match h as h return [||w2_WW h l||] = [|h|] * w2_B + [|l|] with
 | OO => 
    match l as l return [||w2_WW OO l||] = [|OO|] * w2_B + [|l|] with
    | OO => refl_equal 0
    | OI => refl_equal 1
    | IO => refl_equal 2
    | II => refl_equal 3
    end
 | OI => refl_equal ([||w2_WW OI l||])
 | IO => refl_equal ([||w2_WW IO l||])
 | II => refl_equal ([||w2_WW II l||])
 end.

Lemma w2_CW_spec : forall sign c l, interp_carry sign (w2_B*w2_B) (zn2z_to_Z w2_B w2_to_Z) (w2_CW c l) = (interp_carry sign w2_B w2_to_Z c)*w2_B + [|l|].
Proof.
intros sign c l;case c;intro h;simpl;fold (w2_WW h l); rewrite w2_WW_spec;unfold w2_B; ring.
Qed.

