open Str

open Big_int

let shift = 6

let skip s n =
     (String.sub s n (String.length s - n))

let nhexa =regexp  "^N\\$="
let shexa =regexp  "^S\\$="
let rhexa =regexp  "^R\\$="
let ahexa =regexp  "^A\\$="
let bhexa =regexp  "^B\\$="
let thexa =regexp  "^T\\$="
let jhexa =regexp  "^J\\$="
let t0hexa =regexp  "^Type=0"
let t1hexa =regexp  "^Type=1"
let t2hexa =regexp  "^Type=2"
let t3hexa =regexp  "^Type=3"
let t4hexa =regexp  "^Type=4"
let hexa = regexp "-?[ABCDEF0123456789]*"

let hexstring s =
  let rec main rem s = 
    if String.length s <= shift then
     (add_big_int
       (mult_big_int 
         (power_int_positive_int 16 (String.length s))
          rem)
       (big_int_of_int (int_of_string ("0x" ^ s))))
    else
     main
     (add_big_int
       (mult_big_int 
         (power_int_positive_int 16 shift)
          rem)
       (big_int_of_int (int_of_string ("0x" ^ (String.sub s 0 shift)))))
     (skip s shift) in
    let _ = string_match hexa s 0 in ();
    let s1 = matched_string s in 
    if (String.contains s1 '-') then
      minus_big_int (main zero_big_int (skip s1 1))
    else
      main zero_big_int s1




let rec comp2 r =
   let (q, r) = quomod_big_int r (big_int_of_int 2) in
     if eq_big_int r zero_big_int then
       succ_big_int (comp2 q)
     else zero_big_int

let gsqr n1 r =
  let f = div_big_int n1 r in
  let (s1,r1) = quomod_big_int r
               (mult_big_int (big_int_of_int 2) f) in
  sqrt_big_int
   (sub_big_int
      (square_big_int r1)
      (mult_big_int (big_int_of_int 8) s1))


let n = ref zero_big_int
let s = ref zero_big_int
let r = ref zero_big_int
let a = ref zero_big_int
let b = ref zero_big_int
let t = ref zero_big_int
let j = ref zero_big_int
let ty = ref (-1)
let file = ref ""
let co = ref stdout
let sep = ref ""

let pe s =
  output_string !co s;
  output_string !co "\n";
  flush !co

let change_sep () =
  if !sep = "" then sep := "(" else
  if !sep = "(" then sep := "::"

let process_type() =
  if !ty != -1 then
    begin
    if !ty = 4 then
      let n  = !n in
      let t  = !t in
      let j  = !j in
      let a  = 
           mult_big_int 
             (mult_big_int (big_int_of_int 3) j)
             (sub_big_int (big_int_of_int 1728) j) in
      let b = 
           mult_big_int 
             (mult_big_int (big_int_of_int 2) j)
             (square_big_int (sub_big_int (big_int_of_int 1728) j)) in
      let l = mod_big_int
               (add_big_int (power_big_int_positive_int t 3)
                  (add_big_int  (mult_big_int a t) b))
                n in
      let a = mod_big_int 
                (mult_big_int a (square_big_int l)) n in
      let b = mod_big_int 
                (mult_big_int b (power_big_int_positive_int l 3)) n in
      let x = mod_big_int (mult_big_int t l) n in
      let y = mod_big_int (square_big_int l) n in
      begin             
       pe !sep;
       pe ("(Ell_certif");
       pe ((string_of_big_int n));
       pe ((string_of_big_int !s));
       pe ("((" ^ (string_of_big_int !r) ^ ",1)::nil)");
       pe ((string_of_big_int a));
       pe ((string_of_big_int b));
       pe ((string_of_big_int x));
       pe ((string_of_big_int y) ^ ")");
       flush !co;
       change_sep()
      end
    else if !ty = 3 then
      let n  = !n in
      let t  = !t in 
      let a  = !a in
      let b =  !b in
      let l = mod_big_int
               (add_big_int (power_big_int_positive_int t 3)
                  (add_big_int  (mult_big_int a t) b))
                n in
      let a = mod_big_int 
                (mult_big_int a (square_big_int l)) n in
      let b = mod_big_int 
                (mult_big_int b (power_big_int_positive_int l 3)) n in
      let x = mod_big_int (mult_big_int t l) n in
      let y = mod_big_int (square_big_int l) n in
      
      begin       
       pe !sep;
       pe ("(Ell_certif");
       pe ((string_of_big_int n));
       pe ((string_of_big_int !s));
       pe ("((" ^ (string_of_big_int !r) ^ ",1)::nil)");
       pe ((string_of_big_int a));
       pe ((string_of_big_int b));
       pe ((string_of_big_int x));
       pe ((string_of_big_int y) ^ ")");
       change_sep()
      end
    else if !ty = 1 then
      begin   
       pe !sep;         
       pe ("(SPock_certif ");
       pe ((string_of_big_int !n));
       pe ((string_of_big_int !b));
       pe ("((" ^ (string_of_big_int !r)  ^ ", 1)::nil))" );
       flush !co;
       change_sep()      
      end
    else if !ty = 0 then
      begin             
       pe (!sep ^ " (Proof_certif " ^ (string_of_big_int !n) ^
            " prime" ^ (string_of_big_int !n)  ^ ") :: nil)).");
       pe "exact_no_check (refl_equal true).";
       pe "Time Qed.";
       flush !co
      end
    else 
      begin             
       pe ("Type = " ^ (string_of_int !ty));
       flush !co
      end
   end;
   n := !r




let rf f = 
n :=  zero_big_int;
s :=  zero_big_int;
r :=  zero_big_int;
a :=  zero_big_int;
b :=  zero_big_int;
t :=  zero_big_int;
j :=  zero_big_int;
ty:= (-1);
file := "";
co := stdout;
sep := "";
let ic = open_in f in
  let line = ref "" in
  try 
    while true do
    line := input_line ic; 

    if string_match nhexa !line 0 then
 (
             n := hexstring (skip !line 3);
           file := "prime" ^ (String.sub (string_of_big_int !n) 0 1) ^ ".v";
             co := open_out !file;
(*
             pe "Require Import PocklingtonRefl.";
             pe "Set Virtual Machine.";
             pe "Open Local Scope positive_scope.";
*)
             pe ("Lemma prime" ^ (string_of_big_int !n) ^
                ": prime  " ^ (string_of_big_int !n) ^ ".");
             pe "apply (Pocklington_refl ";
             r := !n)
    else if string_match shexa !line 0 then 
          s := (hexstring (skip !line 3))
    else if string_match rhexa !line 0 then 
          r := (hexstring (skip !line 3))
    else if string_match ahexa !line 0 then 
          a := (hexstring (skip !line 3))
    else if string_match bhexa !line 0 then 
          b := (hexstring (skip !line 3))
    else if string_match thexa !line 0 then 
          t := (hexstring (skip !line 3))
    else if string_match jhexa !line 0 then 
          j := (hexstring (skip !line 3))
    else if string_match t0hexa !line 0 then 
          (process_type();ty := 0;process_type())
    else if string_match t1hexa !line 0 then 
          (process_type(); ty := 1)
    else if string_match t2hexa !line 0 then 
          (process_type(); ty := 2;)
    else if string_match t3hexa !line 0 then 
          (process_type(); ty := 3)
    else if string_match t4hexa !line 0 then 
          (process_type();ty := 4)
    done                 

  with e ->              
    close_in_noerr ic;   
    close_out_noerr !co

                         

let _ = 
  if (Array.length Sys.argv) == 2 then
    rf Sys.argv.(1)
  else print_string "o2v file.out";
       print_newline()
