open Str

open Big_int

let shift = 6

let skip s n =
     (String.sub s n (String.length s - n))

let nhexa =regexp  "^N="
let shexa =regexp  "^S="
let whexa =regexp  "^W="
let ahexa =regexp  "^A="
let bhexa =regexp  "^B="
let thexa =regexp  "^T="
let jhexa =regexp  "^J="
let hexa = regexp "-?\\$?[ABCDEF0123456789]*"
let lemmaExp =regexp  "^Lemma"

(* Conversion function *)
let hexstring s =
  if (String.contains s '$') then
    if (String.contains s '-') then
        big_int_of_string ("-0x" ^ (skip s 2)) else
    big_int_of_string ("0x" ^ (skip s 1))
  else big_int_of_string s

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

type certif =

(* Elliptic (n, s, r, a, b, x, y) *)
  Elliptic of 
     big_int * big_int * big_int * big_int * big_int * big_int * big_int
(* Pocklington (n, b, r)          *)
| Pocklington of big_int * big_int * big_int
(* External n                     *)
| External of big_int
(* Error t                        *)
| Error of int;;

let n = ref zero_big_int
let s = ref zero_big_int
let r = ref zero_big_int
let w = ref zero_big_int
let a = ref zero_big_int
let b = ref zero_big_int
let t = ref zero_big_int
let j = ref zero_big_int
let ty = ref (-1)
let file = ref ""
let co = ref stdout
let sep = ref ""
let res = ref ([] : certif list)
let split = ref false
let fileout = ref "a"
let fileoutflag = ref false
let name = ref "primo"
let debug = ref false

let process_type() =
  let elt =
  (if !ty != -1 then
    (if !ty = 4 then
      let n  = !n in
      let s = !s in
      let t  = !t in
      let j  = !j in
      let w = !w in
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
      (r := div_big_int (sub_big_int (add_big_int n (big_int_of_int 1)) w) s;
       Elliptic (n, s, !r, a, b, x, y))
     else if !ty = 3 then
      let n  = !n in
      let t  = !t in
      let s = !s in
      let w = !w in
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
      (r := div_big_int (sub_big_int (add_big_int n (big_int_of_int 1)) w) s;
       Elliptic (n, s, !r, a, b, x, y))
      else
       Error !ty)
  else Error 0)
  in (n := !r; elt)



let parse f =
n :=  zero_big_int;
s :=  zero_big_int;
r :=  zero_big_int;
a :=  zero_big_int;
b :=  zero_big_int;
t :=  zero_big_int;
j :=  zero_big_int;
ty:= (-1);
file := "";
sep := "";
res := [];
let ic = open_in f in
  let line = ref "" in
  (try
    while true do
    line := input_line ic;
    (if !debug then 
      (print_string "line="; print_string !line; print_newline()));
    if string_match nhexa !line 0 then
            (
             n := hexstring (skip !line 2);
             (if !debug then
                (print_string "n="; print_string (string_of_big_int !n);
                 print_newline()));
             r := !n)
    else if string_match shexa !line 0 then
          (s := (hexstring (skip !line 2)); ty := 4;
           (if !debug then
              (print_string "s="; print_string (string_of_big_int !s);
               print_newline()));
          )
    else if string_match whexa !line 0 then
          (w := (hexstring (skip !line 2));
           (if !debug then 
              (print_string "w="; print_string (string_of_big_int !w);
               print_newline()));
          )
    else if string_match ahexa !line 0 then
          (a := (hexstring (skip !line 2)); ty := 3;
           (if !debug then
              (print_string "a="; print_string (string_of_big_int !a);
               print_newline()));
          )
    else if string_match bhexa !line 0 then
          (b := (hexstring (skip !line 2));
           (if !debug then
              (print_string "b="; print_string (string_of_big_int !b);
               print_newline()));
          )
    else if string_match jhexa !line 0 then
          (j := (hexstring (skip !line 2));
           (if !debug then
              (print_string "j="; print_string (string_of_big_int !j);
               print_newline()));
          )
    else if string_match thexa !line 0 then
          (t := (hexstring (skip !line 2));
           (if !debug then
              (print_string "t="; print_string (string_of_big_int !t);
               print_newline()));
           res := process_type() :: !res; ty := -1)
    done
  with e ->
    close_in_noerr ic);
  (if !debug then 
      (print_string "external=";
       print_string (string_of_big_int !r); print_newline()));
  List.rev (External !r :: !res)

let rec gen_name k l =
  match l with
  [] -> ()
| Elliptic (n, s, r, a, b, x, y) :: l1 ->
    print_string "Let p" ; print_int k; print_string " = ";
    print_string (string_of_big_int n); print_string ";"; print_newline();
    gen_name (k + 1) l1
| Pocklington (n, b, r) :: l1 ->
    print_string "Let p" ; print_int k; print_string " = ";
    print_string (string_of_big_int n); print_string ";"; print_newline();
    gen_name (k + 1) l1
| External n :: l1 ->
    print_string "Let p" ; print_int k; print_string " = ";
    print_string (string_of_big_int n); print_string ";"; print_newline();
    gen_name (k + 1) l1
| _ :: l1 ->
    print_string "(* Error *)"; print_newline(); gen_name (k + 1) l1

let pe s =
  output_string !co s;
  output_string !co "\n";
  flush !co

let pef s =
  output_string !co s;
  flush !co


let print_header () =
   pe "From Coqprime Require Import PocklingtonRefl.";
   pe "Local Open Scope positive_scope."

let split_begin k =
  if !split then
   (let fname = !fileout ^ "_" ^ (string_of_int k) ^ ".v" in
      co :=  open_out fname;
      print_header())


let split_close k =
  if !split then
   (close_out !co)

let print_elliptic k n s r a  b x y  =
   split_begin k;
   pe  "";
   pe ("Lemma " ^ !name ^ (string_of_int k) ^
         ":");
   pe ("  prime  " ^ (string_of_big_int r) ^ "->");
   pe ("  prime  " ^ (string_of_big_int n) ^ ".");
   pe "Proof.";
   pe "intro H.";
   pe "apply (Pocklington_refl ";
   pe ("     (Ell_certif");
   pe ("      " ^ (string_of_big_int n));
   pe ("      " ^ (string_of_big_int s));
   pe ("      ((" ^ (string_of_big_int r) ^ ",1)::nil)");
   pe ("      " ^ (string_of_big_int a));
   pe ("      " ^ (string_of_big_int b));
   pe ("      " ^ (string_of_big_int x));
   pe ("      " ^ (string_of_big_int y) ^ ")");
   pe  "     ((Proof_certif _ H) :: nil)).";
   pe  "native_cast_no_check (refl_equal true).";
   pe  "Time Qed.";
   split_close k


let print_external k n =
  let fname = !fileout ^ "_" ^ (string_of_int k) ^ ".v" in
  let _ = Sys.command (Filename.dirname (Sys.executable_name)^
                "/pocklington -o " ^ fname ^ " -n " ^ !name ^
                 (string_of_int k)^ " " ^
                 (string_of_big_int n)) in
  if (not !split) then
  (let ic = open_in fname in
  let line = ref "" in
  let flag = ref false in
  (try
    while true do
    line := input_line ic;
    if string_match lemmaExp !line 0 then flag := true;
    if !flag then pe !line
    done
  with e ->
    close_in_noerr ic);
  Sys.remove fname)


let print_pocklington k n b r =
   split_begin k;
   pe  "";
   pe ("Lemma " ^ !name  ^ (string_of_int k) ^
         ":");
   pe ("  prime  " ^ (string_of_big_int r) ^ "->");
   pe ("  prime  " ^ (string_of_big_int n) ^ ".");
   pe "Proof.";
   pe "intro H.";
   pe "apply (Pocklington_refl ";
   pe ("  (SPock_certif ");
   pe ("   " ^ (string_of_big_int n));
   pe ("   " ^ (string_of_big_int b));
   pe ("   ((" ^ (string_of_big_int r)  ^ ", 1)::nil))" );
   pe  "   ((Proof_certif _ H) :: nil)).";
   pe  "native_cast_no_check (refl_equal true).";
   pe  "Time Qed.";
   split_close k

let rec print_goals k l =
  match l with
  [] -> ()
| Elliptic (n, s, r, a, b, x, y) :: l1 ->
    print_elliptic  k n s r a b x y;
    print_goals (k + 1) l1
| Pocklington (n, b, r) :: l1 ->
    print_pocklington k n b r;
    print_goals (k + 1) l1
| External n :: l1 ->
    print_external k n;
    print_goals k l1
| _ :: l1 ->
   print_goals k l1

let rec rprint_main k l =
  match l with
  [] -> ()
| Elliptic (n, s, r, a, b, x, y) :: l1 ->
    pef ("(");
    pef (!name  ^ (string_of_int k) ^ " ");
    rprint_main (k + 1) l1;
    pef (")");
| Pocklington (n, b, r) :: l1 ->
    pef ("(");
    pef (!name  ^ (string_of_int k)^ " ");
    rprint_main (k + 1) l1;
    pef (")");
| External n :: l1 ->
    pef (!name  ^ (string_of_int k));
    rprint_main k l1
| _ :: l1 ->
    rprint_main k l1


let rec print_main l =
  match l with
  [] -> ()
| Elliptic (n, s, r, a, b, x, y) :: _ ->
    pe ("");
    pe ("Lemma  " ^ !name ^ ": prime " ^
         (string_of_big_int n)^ ".");
    pe ("Proof.");
    pe ("exact");
    rprint_main 0 l;
    pe (".");
    pe ("Qed.")
| Pocklington (n, b, r) :: l1 ->
    pe ("");
    pe ("Lemma  " ^ !name  ^ ": prime " ^
         (string_of_big_int n)^ ".");
    pe ("Proof.");
    pe ("exact");
    rprint_main 0 l;
    pe (".");
    pe ("Qed.")
| External n :: l1 ->
    pe ("");
    pe ("Lemma  " ^ !name ^ " : prime " ^
         (string_of_big_int n)^ ".");
    pe ("Proof.");
    pef ("exact ");
    rprint_main 0 l;
    pe (".");
    pe ("Qed.")
| _ :: l1 ->
    print_main l1


let rec print_require k l =
  match l with
  [] -> ()
| Elliptic (n, s, r, a, b, x, y) :: l1 ->
    pe ("Require Import  " ^ !fileout ^ "_" ^ (string_of_int k) ^ ".");
    print_require (k + 1) l1
| Pocklington (n, b, r) :: l1 ->
    pe ("Require Import  " ^ !fileout ^ "_" ^  (string_of_int k) ^ ".");
    print_require (k + 1) l1
| External n :: l1 ->
    pe ("Require Import  " ^ !fileout ^ "_" ^  (string_of_int k) ^ ".");
    print_require (k + 1) l1
| _ :: l1 ->
    print_require k l1



let rec print_make k l =
  match l with
  [] -> ()
| Elliptic (n, s, r, a, b, x, y) :: l1 ->
    pe (!fileout ^ "_" ^ (string_of_int k) ^ ".v");
    print_make (k + 1) l1
| Pocklington (n, b, r) :: l1 ->
    pe (!fileout ^ "_" ^ (string_of_int k) ^ ".v");
    print_make (k + 1) l1
| External n :: l1 ->
    pe (!fileout ^ "_" ^ (string_of_int k) ^ ".v");
    print_make (k + 1) l1
| _ :: l1 ->
    print_make k l1


let _ =
  let v = ref (Array.length Sys.argv) in
  let k = ref 1 in
  let flag = ref true in
  while !flag do
    if Sys.argv.(!k) = "-split" then
      (k := !k + 1; v := !v -1; split := true)
    else if  Sys.argv.(!k) = "-o" then
      (k := !k + 2; v := !v - 2;
        (try
          fileout := Filename.chop_extension (Sys.argv.(!k - 1))
        with e -> fileout := Sys.argv.(!k - 1));
       fileoutflag := true)
    else if  Sys.argv.(!k) = "-n" then
      (k := !k + 2; v := !v - 2; name := Sys.argv.(!k - 1))
    else (flag := false)
  done;
  if (!v) == 2 then
    (let p = parse Sys.argv.(!k) in
    if (not !fileoutflag) then
        (try
          fileout := Filename.chop_extension (Sys.argv.(!k))
        with e -> fileout := Sys.argv.(!k));
    if (not !split) then
     (let fname = !fileout ^ ".v" in
      co := open_out fname;
      print_header ());
    print_goals 0 p;
    if (!split) then
     (let fname = !fileout ^ ".v" in
      co := open_out fname;
      print_header ();
      print_require 0 p);
    print_main p;
    close_out !co;
    if (!split) then
     (let fname = !fileout ^ "_make" in
      co := open_out fname;
      pe (!fileout ^ ".v");
      print_make 0 p);
    close_out !co)
  else (print_string "o2v [-split] [-o file.out] [-n name] file.in ";
        print_newline())
