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


Definition myabs x :=
 match x with
 |BinInt.Zpos p => p
 |BinInt.Z0 => xH
 |BinInt.Zneg p => p
 end.
 
Definition foo1'' n := 
  let l1 := map n (BinInt.Zpos BinPos.xH) in
  let v1 := fold_left (fun y x => add (make_norm (fst x) (myabs (snd x))) y) 
      (list_prod l1 (rev l1)) zero in
 print v1.


Definition foo2'' n := 
  let l1 := map n (BinInt.Zpos BinPos.xH) in
  let v2 := 
   fold_left 
     (fun y x => add_norm (make_norm (fst x) (myabs (snd x))) y) 
     (list_prod l1 (rev l1)) zero in
  print v2.

Time Eval vm_compute in  (foo1' 1).
Time Eval vm_compute in  (foo1'' 1).
Time Eval vm_compute in map 1 (BinInt.Zpos BinPos.xH).
Time Eval vm_compute in map 2 (BinInt.Zpos BinPos.xH).

Time Eval vm_compute in  (foo1' 2).
Time Eval vm_compute in  (foo2' 2).
Time Eval vm_compute in  (foo1'' 2).
Time Eval vm_compute in  (foo2'' 2).

(* sur ma machine 115 secondes *)
Time Eval vm_compute in  (foo2' 1).

Time Eval vm_compute in  compare (foo1 100) (foo2 100).
(* sur ma machine 6 secondes *)


Eval vm_compute in 
  let l1 := map 2 (BinInt.Zpos BinPos.xH) in
     (list_prod l1 (rev l1)).
 

Fixpoint sum (add:Q.t->Q.t->Q.t) (n d:BinInt.Z) 
   (dn : nat) (res:Q.t) {struct dn} : Q.t:=
  match dn with 
  | 0 => res
  | S dn =>
    sum add (Zsucc n) (Zpred d) dn (add res (make_norm n (myabs d)))
  end.

Definition sum1 n := sum add 1 (Z_of_nat n) n Q.zero.
Definition sum2 n := sum add_norm 1 (Z_of_nat n) n Q.zero.

Time Eval vm_compute in  print (sum1 2).
Time Eval vm_compute in  print (sum2 2).

Time Eval vm_compute in  print (sum1 3).
Time Eval vm_compute in  print (sum2 3).
