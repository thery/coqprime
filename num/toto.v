Require Import List.
Require Import ZArith.
Require Import Q.

Fixpoint map (n: nat) (m: BinInt.Z) {struct n}: list BinInt.Z :=
  m ::  match n with 0 => nil | (S n1) => (map n1 (BinInt.Zsucc m)) end.


Definition foo1 n := 
  let l1 := map n (BinInt.Zpos BinPos.xH) in
  let v1 := fold_left (fun y x => add (Qq (Arith.Z.of_Z (fst x)) (Arith.Z.to_N (Arith.Z.of_Z (snd x)))) y) (list_prod l1 (rev l1)) zero in
  v1.

Definition foo2 n := 
  let l1 := map n (BinInt.Zpos BinPos.xH) in
  let v2 := fold_left (fun y x => add_norm (Qq (Arith.Z.of_Z (fst x)) (Arith.Z.to_N (Arith.Z.of_Z (snd x)))) y) (list_prod l1 (rev l1)) zero in
  v2.

Definition print q :=
  match q as x return 
    match x with Qz _ => BinInt.Z | _ =>  (BinInt.Z* BinInt.Z)%type end with
  | Qz x => Arith.Z.to_Z x
  | Qq n d => (Arith.Z.to_Z n, Arith.N.to_Z d)
  end.

Definition foo1' n := 
  let l1 := map n (BinInt.Zpos BinPos.xH) in
  let v1 := fold_left (fun y x => add (Qq (Arith.Z.of_Z (fst x)) (Arith.Z.to_N (Arith.Z.of_Z (snd x)))) y) (list_prod l1 (rev l1)) zero in
 print v1.


Definition foo2' n := 
  let l1 := map n (BinInt.Zpos BinPos.xH) in
  let v2 := fold_left (fun y x => add_norm (Qq (Arith.Z.of_Z (fst x)) (Arith.Z.to_N (Arith.Z.of_Z (snd x)))) y) (list_prod l1 (rev l1)) zero in
  print v2.

Time Eval vm_compute in  (foo1' 1).
Time Eval vm_compute in map 1 (BinInt.Zpos BinPos.xH).
Time Eval vm_compute in map 2 (BinInt.Zpos BinPos.xH).

Time Eval vm_compute in  (foo1' 2).
Time Eval vm_compute in  (foo2' 2).

(* sur ma machine 115 secondes *)
Time Eval vm_compute in  (foo2' 1).

Time Eval vm_compute in  compare (foo1 100) (foo2 100).
(* sur ma machine 6 secondes *)


