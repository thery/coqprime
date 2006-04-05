Require Import ZArith.
Require Import Arith.

Inductive q_type : Set := 
 | Qz : Z.t -> q_type
 | Qq : Z.t -> N.t -> q_type.

Definition t := q_type.

Definition zero := Qz Z.zero.
Definition one  := Qz Z.one.
Definition minus_one := Qz Z.minus_one.

Definition of_Z x := Qz (Z.of_Z x).

Definition d_to_Z d := Z.Pos (N.succ d).

Definition compare x y :=
 match x, y with
 | Qz zx, Qz zy => Z.compare zx zy
 | Qz zx, Qq ny dy => Z.compare (Z.mul zx (d_to_Z dy)) ny
 | Qq nx dy, Qz zy => Z.compare nx (Z.mul zy (d_to_Z dy))
 | Qq nx dx, Qq ny dy =>
   Z.compare (Z.mul nx (d_to_Z dy)) (Z.mul ny (d_to_Z dx))
 end.

Definition opp x :=
 match x with
 | Qz zx => Qz (Z.opp zx)
 | Qq nx dx => Qq (Z.opp nx) dx
 end.

(* Inv d > 0, Pour la forme normal unique on veut d > 1 *)
Definition norm n d :=
 if Z.eq_bool n Z.zero then zero
 else
   let gcd := N.gcd (Z.to_N n) d in
   if N.eq_bool gcd N.one then Qq n (N.pred d)
   else	
    let n := Z.div n (Z.Pos gcd) in
    let d := N.div d gcd in
    if N.eq_bool d N.one then Qz n
    else Qq n (N.pred d).
   
Definition add x y :=
 match x, y with
 | Qz zx, Qz zy => Qz (Z.add zx zy)
 | Qz zx, Qq ny dy => Qq (Z.add (Z.mul zx (d_to_Z dy)) ny) dy
 | Qq nx dx, Qz zy => Qq (Z.add nx (Z.mul zy (d_to_Z dx))) dx
 | Qq nx dx, Qq ny dy => 
   let dx' := N.succ dx in
   let dy' := N.succ dy in
   let n := Z.add (Z.mul nx (Z.Pos dy')) (Z.mul ny (Z.Pos dx')) in
   let d := N.pred (N.mul dx' dy') in
   Qq n d
 end.

Definition add_norm x y := 
 match x, y with
 | Qz zx, Qz zy => Qz (Z.add zx zy)
 | Qz zx, Qq ny dy => 
   let d := N.succ dy in
   norm (Z.add (Z.mul zx (Z.Pos d)) ny) d 
 | Qq nx dx, Qz zy =>
   let d := N.succ dx in
   norm (Z.add (Z.mul zy (Z.Pos d)) nx) d
 | Qq nx dx, Qq ny dy =>
   let dx' := N.succ dx in
   let dy' := N.succ dy in
   let n := Z.add (Z.mul nx (Z.Pos dy')) (Z.mul ny (Z.Pos dx')) in
   let d := N.mul dx' dy' in
   norm n d 
 end.
 
Definition sub x y := add x (opp y).

Definition sub_norm x y := add_norm x (opp y).

Definition mul x y :=
 match x, y with
 | Qz zx, Qz zy => Qz (Z.mul zx zy)
 | Qz zx, Qq ny dy => Qq (Z.mul zx ny) dy
 | Qq nx dx, Qz zy => Qq (Z.mul nx zy) dx
 | Qq nx dx, Qq ny dy => 
   Qq (Z.mul nx ny) (N.pred (N.mul (N.succ dx) (N.succ dy)))
 end.

Definition mul_norm x y := 
 match x, y with
 | Qz zx, Qz zy => Qz (Z.mul zx zy)
 | Qz zx, Qq ny dy =>
   if Z.eq_bool zx Z.zero then zero
   else	
     let d := N.succ dy in
     let gcd := N.gcd (Z.to_N zx) d in
     if N.eq_bool gcd N.one then Qq (Z.mul zx ny) dy
     else 
       let zx := Z.div zx (Z.Pos gcd) in
       let d := N.div d gcd in
       if N.eq_bool d N.one then Qz (Z.mul zx ny)
       else Qq (Z.mul zx ny) (N.pred d)
 | Qq nx dx, Qz zy =>   
   if Z.eq_bool zy Z.zero then zero
   else	
     let d := N.succ dx in
     let gcd := N.gcd (Z.to_N zy) d in
     if N.eq_bool gcd N.one then Qq (Z.mul zy nx) dx
     else 
       let zy := Z.div zy (Z.Pos gcd) in
       let d := N.div d gcd in
       if N.eq_bool d N.one then Qz (Z.mul zy nx)
       else Qq (Z.mul zy nx) (N.pred d)
 | Qq nx dx, Qq ny dy => 
   norm (Z.mul nx ny) (N.mul (N.succ dx) (N.succ dy))
 end.

Definition inv x := 
 match x with
 | Qz (Z.Pos n) => Qq Z.one n
 | Qz (Z.Neg n) => Qq Z.minus_one n
 | Qq (Z.Pos n) d => Qq (Z.Pos (N.succ d)) (N.pred n)
 | Qq (Z.Neg n) d => Qq (Z.Neg (N.succ d)) (N.pred n)
 end.

Definition square x :=
 match x with
 | Qz zx => Qz (Z.square zx)
 | Qq nx dx => Qq (Z.square nx) (N.pred (N.square (N.succ dx)))
 end.

Definition power_pos x p :=
 match x with
 | Qz zx => Qz (Z.power_pos zx p)
 | Qq nx dx => Qq (Z.power_pos nx p) (N.pred (N.power_pos (N.succ dx) p))
 end.

