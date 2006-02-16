Require Import ZArith.
Open Local Scope Z_scope.
Require Import W2_basic.
Require Import W2_basic_spec.
Open Local Scope w2_scope.
Require Import W2_compare.


Lemma w2_compare_spec : forall x y, match w2_compare x y return Prop with  | Eq => [|x|] = [|y|] | Lt => [|x|] < [|y|] | Gt => [|x|] > [|y|] end.
Proof
fun x y =>
 let typ x y := match w2_compare x y return Prop with  | Eq => [|x|] = [|y|] | Lt => [|x|] < [|y|] | Gt => [|x|] > [|y|] end in
 match x as x return typ x y with
 | OO => 
    match y as y return typ OO y with
    | OO => refl_equal 0
    | _ => refl_equal Lt
    end
 | OI => 
    match y as y return typ OI y with
    | OO => refl_equal Gt
    | OI => refl_equal 1
    | _ => refl_equal Lt
    end
 | IO => 
    match y as y return typ IO y with
    | OO => refl_equal Gt
    | OI => refl_equal Gt
    | IO => refl_equal 2
    | _ => refl_equal Lt
    end
 | II => 
    match y as y return typ II y with
    | OO => refl_equal Gt
    | OI => refl_equal Gt
    | IO => refl_equal Gt
    | II => refl_equal 3
    end
 end.

Lemma false_true_A : forall A:Prop, false = true -> A.
 intros A H;  discriminate H.
Qed.

Lemma w2_eq0_spec : forall x, w2_eq0 x = true -> [|x|] = 0.
Proof
fun x =>
 match x as x return w2_eq0 x = true -> [|x|] = 0 with
 | OO => fun H => refl_equal 0
 | OI => fun H => false_true_A (
[|OI|] = 0) H
 | IO => fun H => false_true_A (
[|IO|] = 0) H
 | II => fun H => false_true_A (
[|II|] = 0) H
 end.

