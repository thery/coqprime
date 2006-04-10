Require Import Bool.
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

Definition make x y := 
 match y with
 | Zpos p => Qq (Z.of_Z x) (N.of_pos p)
 | Z0 => zero
 | Zneg p => Qq (Z.of_Z (Zopp x)) (N.of_pos p)
 end.

(* d <> 0 *)
Definition norm n d := 
 if Z.eq_bool n Z.zero then zero
 else
   if N.eq_bool d N.one then Qz n
   else 
     let p := N.gcd (Z.to_N n) d in
     if N.eq_bool p N.one then Qq n d
     else 
       let n1 := Z.div n (Z.Pos p) in
       let d1 := N.div d p in
       if N.eq_bool d1 N.one then Qz n1
       else Qq n1 d1.
      
Definition make_norm x y := 
 match y with
 | Zpos p => norm (Z.of_Z x) (N.of_pos p)
 | Z0 => zero
 | Zneg p => norm (Z.of_Z (Zopp x)) (N.of_pos p)
 end.

Definition opp x :=
 match x with
 | Qz zx => Qz (Z.opp zx)
 | Qq nx dx => Qq (Z.opp nx) dx
 end.

Definition add x y :=
 match x with
 | Qz zx =>
   match y with
   | Qz zy => Qz (Z.add zx zy)
   | Qq ny dy => 
     if N.eq_bool dy N.zero then x
     else Qq (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
   end
 | Qq nx dx =>
   if N.eq_bool dx N.zero then y  
   else match y with
   | Qz zy => Qq (Z.add nx (Z.mul zy (Z.Pos dx))) dx
   | Qq ny dy => 
     if N.eq_bool dy N.zero then x
     else 
       Qq (Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)))
          (N.mul dx dy)
   end
 end.

Definition add_norm x y :=
 match x with
 | Qz zx =>
   match y with
   | Qz zy => Qz (Z.add zx zy)
   | Qq ny dy => 
     if N.eq_bool dy N.zero then x
     else Qq (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
   end
 | Qq nx dx =>
   if N.eq_bool dx N.zero then y  
   else match y with
   | Qz zy => Qq (Z.add nx (Z.mul zy (Z.Pos dx))) dx
   | Qq ny dy => 
     if N.eq_bool dy N.zero then x
     else
       let p := N.gcd dx dy in
       if N.eq_bool p N.one then
         Qq (Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)))
            (N.mul dx dy)
       else 
         let d1 := N.div dx p in
         let d2 := N.div dy p in
         let n := Z.add (Z.mul nx (Z.Pos d2)) (Z.mul ny (Z.Pos d1)) in
         let p' := N.gcd (Z.to_N n) p in
         let d := N.mul d1 (N.div dy p') in
         if N.eq_bool d N.one then Qz (Z.div n (Z.Pos p')) 
         else Qq (Z.div n (Z.Pos p')) d
   end
 end.

Definition sub x y := add x (opp y).

Definition sub_norm x y := add_norm x (opp y).

Definition mul x y :=
 match x, y with
 | Qz zx, Qz zy => Qz (Z.mul zx zy)
 | Qz zx, Qq ny dy => Qq (Z.mul zx ny) dy
 | Qq nx dx, Qz zy => Qq (Z.mul nx zy) dx
 | Qq nx dx, Qq ny dy => Qq (Z.mul nx ny) (N.mul dx dy)
 end.

Definition mul_norm x y :=
 match x, y with
 | Qz zx, Qz zy => Qz (Z.mul zx zy)
 | Qz zx, Qq ny dy =>
   let p := N.gcd (Z.to_N zx) dy in
   match N.compare p N.one with
   | Lt => zero             (* p < 1 => dy = 0 /\ zx = 0 *)
   | Eq => Qq (Z.mul zx ny) dy
   | Gt => 
     let n := Z.mul (Z.div zx (Z.Pos p)) ny in
     let d := N.div dy p in
     if N.eq_bool d N.one then Qz n
     else Qq n d
   end
 | Qq nx dx, Qz zy => 
   let p := N.gcd (Z.to_N zy) dx in
   match N.compare p N.one with
   | Lt => zero             (* p < 1 => dx = 0 /\ zy = 0 *)
   | Eq => Qq (Z.mul zy nx) dx
   | Gt => 
     let n := Z.mul (Z.div zy (Z.Pos p)) nx in
     let d := N.div dx p in
     if N.eq_bool d N.one then Qz n
     else Qq n d
   end
 | Qq nx dx, Qq ny dy =>
   let p1 := N.gcd (Z.to_N nx) dy in
   let p2 := N.gcd (Z.to_N ny) dx in
   match N.compare p1 N.one with
   | Lt => zero 
   | Eq =>
     match N.compare p2 N.one with
     | Lt => zero
     | Eq => Qq (Z.mul nx ny) (N.mul dx dy)
     | Gt => 
       let n2 := Z.div ny (Z.Pos p2) in
       let d1 := N.div dx p2 in
       Qq (Z.mul nx n2) (N.mul d1 dy)
     end
   | Gt =>
     let n1 := Z.div nx (Z.Pos p1) in
     let d2 := N.div dy p1 in 
     match N.compare p2 N.one with
     | Lt => zero
     | Eq => Qq (Z.mul n1 ny) (N.mul dx d2) 
     | Gt => 
       let n2 := Z.div ny (Z.Pos p2) in
       let d1 := N.div dx p2 in
       let d := N.mul d1 d2 in
       if N.eq_bool d N.one then Qz (Z.mul n1 n2)
       else Qq (Z.mul n1 n2) d
     end
   end
 end.

Definition square x := 
 match x with
 | Qz zx => Qz (Z.square zx)
 | Qq nx dx => Qq (Z.square nx) (N.square dx)
 end.

Definition power_pos x p := 
 match x with
 | Qz zx => Qz (Z.power_pos zx p)
 | Qq nx dx => Qq (Z.power_pos nx p) (N.power_pos dx p) 
 end.
 
Definition inv x :=
 match x with
 | Qz (Z.Pos nx) => if N.eq_bool nx N.zero then zero else Qq Z.one nx
 | Qz (Z.Neg nx) => if N.eq_bool nx N.zero then zero else Qq Z.minus_one nx
 | Qq (Z.Pos nx) dy => if N.eq_bool nx N.zero then zero else Qq (Z.Pos dy) nx
 | Qq (Z.Neg nx) dy => if N.eq_bool nx N.zero then zero else Qq (Z.Neg dy) nx
 end.

Definition compare x y :=
 match x, y with
 | Qz zx, Qz zy => Z.compare zx zy
 | Qz zx, Qq ny dy =>
   if N.eq_bool dy N.zero then Z.compare zx Z.zero
   else match Z.cmp_sign zx ny with
   | Lt => Lt
   | Gt => Gt 
   | Eq => Z.compare (Z.mul zx (Z.Pos dy)) ny
   end
 | Qq nx dx, Qz zy =>
   if N.eq_bool dx N.one then Z.compare Z.zero zy
   else match Z.cmp_sign nx zy with
   | Lt => Lt
   | Gt => Gt
   | Eq => Z.compare nx (Z.mul zy (Z.Pos dx))
   end
 | Qq nx dx, Qq ny dy =>
   if N.eq_bool dx N.zero then 
     if N.eq_bool dy N.zero then Eq
     else Z.compare Z.zero ny
   else 
     if N.eq_bool dy N.zero then Z.compare nx Z.zero
     else match Z.cmp_sign nx ny with
     | Lt => Lt
     | Gt => Gt
     | Eq => Z.compare (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx))
     end
 end.





 
