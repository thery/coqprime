Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Open Local Scope w2_scope.
Require Import W2_add.


Lemma w2_succ_c_spec : forall x, [+|w2_succ_c x|] = [|x|] + 1.
Proof
fun x =>
 match x as x return [+|w2_succ_c x|] = [|x|] + 1 with
 | OO => refl_equal (0+1)
 | OI => refl_equal (1+1)
 | IO => refl_equal (2+1)
 | II => refl_equal (3+1)
 end.

Lemma w2_succ_spec : forall x, [|w2_succ x|] = ([|x|] + 1) mod w2_B.
Proof
fun x =>
 match x as x return [|w2_succ x|] = ([|x|] + 1) mod w2_B with
 | OO => refl_equal ((0+1) mod w2_B)
 | OI => refl_equal ((1+1) mod w2_B)
 | IO => refl_equal ((2+1) mod w2_B)
 | II => refl_equal ((3+1) mod w2_B)
 end.

Lemma w2_carry_succ_c_spec : forall c, [+|c|] <= w2_B + (w2_B - 2) -> [+|w2_carry_succ_c c|] = [+|c|] + 1.
Proof
fun c =>
 match c as c return [+|c|] <= w2_B + (w2_B - 2) -> [+|w2_carry_succ_c c|] = [+|c|] + 1 with
 | C0 x => fun (H:[+|C0 x|] <= w2_B + (w2_B - 2))=> w2_succ_c_spec x
 | C1 x =>
    match x as x return [+|(C1 x)|] <= w2_B + (w2_B - 2) -> [+|w2_carry_succ_c (C1 x)|] = [+|(C1 x)|] + 1 with
    | OO => fun (H:[+|C1 OO|] <= w2_B + (w2_B - 2)) => refl_equal 5
    | OI => fun (H:[+|C1 OI|] <= w2_B + (w2_B - 2)) => refl_equal 6
    | IO => fun (H:[+|C1 IO|] <= w2_B + (w2_B - 2)) => refl_equal 7
    | II =>
      fun (H:[+|C1 II|] <= w2_B + (w2_B - 2)) =>
        False_ind
          ([+|w2_carry_succ_c (C1 II)|] = [+|(C1 II)|] + 1)
          (H (refl_equal Gt))
    end
 end.

