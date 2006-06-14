(*************************************************)
(* Thanks to P. Letouzey for these examples      *)
(*************************************************)


Require Import Q.
Require Import ZArith.

Open Scope Z_scope.

Definition Qdiv x y := mul x (Q.inv y).

Definition Qnorm n :=
  match n with Qz _ => n | Qq p n => Q.norm p n end.

Definition Qsign n :=
  match Q.compare zero n with Eq => one | Lt => one  | Gt  => Q.opp one end.

Definition get_first_n_decimal_digits n r :=
  match r with Qz p => (Arith.Z.to_Z p) 
  | Qq p q => 
     Arith.Z.to_Z (Arith.Z.div (Arith.Z.mul (Arith.Z.power_pos (Arith.Z.of_Z 10) n) p) 
        (Arith.Z.Pos q))
  end.

Fixpoint fib_pair (n:nat) : Z*Z := match n with 
 | O => (0,1)
 | S n => let (p,q) := fib_pair n in (q,p+q)
 end.

Definition fibonacci (n:nat) := snd (fib_pair n). 

Definition two := Eval compute in Q.of_Z 2.

Fixpoint sqrt2_newton (n:nat) : q_type := match n with 
 | O => one
 | S n => let q := sqrt2_newton n in  
               (Q.add (Q.mul (Q.inv two) q) (Q.inv q))
 end.

(*
Time Eval vm_compute in sqrt2_newton 10.
*)

Time Eval vm_compute in (get_first_n_decimal_digits 100 (sqrt2_newton 10)).

(*
1414213562373095048801688724209698078569671875376948073176679737990\
7324784621070388503875343276415727

Finished transaction in 0. secs (0.26u,0.03s)
*)
 

(* from bc: 
scale=100
sqrt(2)
1.414213562373095048801688724209698078569671875376948073176679737990\
7324784621070388503875343276415727
*)


Fixpoint e_frac_aux (n:nat) : q_type*(q_type * q_type) := 
match n with 
 | O => (one, (one, one))
 | S n => let (q,pr) := e_frac_aux n in 
               let (fact,next) := pr in 
               let nextfact:=(Q.mul next fact) in
               (Qnorm (Q.add q (Q.inv nextfact)), (nextfact,Q.add one next))
 end.

Definition e_frac (n:nat) := fst (e_frac_aux n).

Time Eval vm_compute in (get_first_n_decimal_digits 100 (e_frac 75)).
(*
2718281828459045235360287471352662497757247093699959574966967627724\
0766303535475945713821785251664274
Finished transaction in 4. secs (3.69u,0.06s)

*) 

(* from bc: 
scale=100
2.718281828459045235360287471352662497757247093699959574966967627724\
0766303535475945713821785251664274
*)

Fixpoint atan_aux (n:nat)(q:q_type) {struct n } : (q_type*(q_type*q_type)) := 
match n with 
	                          (* part sum / last term / (-1)^n*(2n+1) *)
  | O => (q,(q,one)) 
  | S n => let (sum,pr) := atan_aux n q in 
                let (power,div) := pr in 
                let nextpower:=Q.mul (Q.mul q q) power in 
	        let nextdiv:= Q.sub (Q.mul (Q.opp two) (Qsign div)) div in 
                (Qnorm  (Q.add sum (Qdiv nextpower nextdiv)), (nextpower, nextdiv))
 end.

Definition atan (n:nat)(q:q_type) := fst (atan_aux n q).

Definition sixteen := Eval compute in Q.of_Z 16.
Definition five := Eval compute in Q.of_Z 5.
Definition twothreenine := Eval compute in Q.of_Z 239.
Definition four := Eval compute in Q.of_Z 4.

Definition pi_frac (n:nat) := Qnorm 
  (Q.sub  
    (Q.mul sixteen (atan n (Q.inv five)))
    (Q.mul four (atan n (Q.inv twothreenine)))).


Time Eval vm_compute in get_first_n_decimal_digits 100 (pi_frac 75).

(*
3141592653589793238462643383279502884197169399375105820974944592307
8164062862089986280348253421170679

Finished transaction in 101. secs (98.09u,1.s)


bc:
3.141592653589793238462643383279502884197169399375105820974944592307\
8164062862089986280348253421170680
*)
