
let digits = ref 2

let usage =  "Usage : genW [-o filename] digits\n"

let setsize s =
  let n = int_of_string s in
  if n < 2 || n > 12 then begin
    print_string "number of digits should be between 2 and 9\n"; 
    exit 1
  end;
  digits := n

let defaultname = ref true

let filename = ref ""

let setname s = 
  filename := s;
  defaultname := false

(* ** Parse the arguments ** *)

let _ = 
  Arg.parse [("-o",Arg.String setname, "")] 
    setsize 
    usage

(* ** compute the base and set the out channel ** *)

let (base, fd) =     
  let base = 1 lsl !digits in
  let outname = 
    if !defaultname then "W"^(string_of_int !digits)^".v"
    else !filename in 
  let fd = 
    try 
      Unix.openfile outname [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_TRUNC] 0o640 
    with _ -> 
      print_string ("can not open file "^outname^"\n"); 
      exit 1  in
  let out = Unix.out_channel_of_descr fd in
  Format.set_formatter_out_channel out;
  (base,fd)

let print = Format.print_string
let println s = print s;print "\n"
let printi = Format.print_int
let print_title s =
  println "";
  print "(* ** ";print s;println " ** *)";
  println ""

let wt = "w"^(string_of_int !digits)

let w_digits = wt^"_digits"
let w_B = wt^"_B"
let w_to_Z = wt^"_to_Z"
let w_of_pos = wt^"_of_pos"
let w_of_N = wt^"_of_N"
let w_head0 = wt^"_head0"
let w_0 = wt^"_0"
let w_1 = wt^"_1"
let w_Bm1 = wt^"_Bm1"
let w_WW = wt^"_WW"
let w_CW = wt^"_CW"
let w_compare = wt^"_compare"
let w_opp_c = wt^"_opp_c"
let w_opp_carry = wt^"_opp_carry"
let w_succ_c = wt^"_succ_c"
let w_carry_succ_c = wt^"_carry_succ_c"
let w_add_c = wt^"_add_c" 
let w_add_carry_c = wt^"_add_carry_c"
let w_add = wt^"_add"
let w_pred_c = wt^"_pred_c"
let w_sub_c = wt^"_sub_c"
let w_sub_carry_c = wt^"_sub_carry_c"
let w_sub = wt^"_sub"
let w_mul_c = wt^"_mul_c"
let w_mul = wt^"_mul"
let w_square_c = wt^"_square_c"
let w_div_wB = wt^"_div_wB"
let w_div21 = wt^"_div21"
let w_lsl_i i = wt^"_lsl"^(string_of_int i)
let w_lsr_i i = wt^"_lsr"^(string_of_int i)
let w_add_mul_div = wt^"_add_mul_div"
let w_op = wt^"_op"

let print_wt () = print wt;;

let print_def f args =
  print "Definition ";print f;
  if args != "" then (print " ";print args);
  println " :="

let print_match args =
  print " match ";print args;println " with"


let print_w n = 
  let s = ref "" in
  let n = ref n in
  for i = 1 to !digits do
    let d = if !n mod 2 = 0 then "O" else "I" in
    s := d^(!s);
    n := !n/2
  done;
  print !s

let print_c n =
  if n < 0 then (print "C1 ";print_w (base + n))
  else 
    if n/base = 0 then (print "C0 ";print_w n)
    else begin 
      assert (n < 2*base - 1);
      print "C1 ";print_w n
    end
    
let rec print_pos_s s n =
  if n <= 1 then print s
  else begin
    if n mod 2 = 0 then print "(xO "
    else print "(xI ";
    print_pos_s s (n/2);print ")"
  end

let print_pos = print_pos_s "xH"
 
let rec nb_head0 n =
 if n = 0 then !digits else nb_head0 (n/2) - 1

let _ = 
  println "Require Import ZArith.";
  println "Require Import ZnZ.";
  println "";

  println "Unset Boxed Definitions.";
  println "";
  println "Open Local Scope Z_scope.";
  println "";

  print  ("Inductive "^wt^" : Set :=");
  for i = 0 to base - 1 do
    println "";
    print " | "; print_w i;print " : ";print_wt()
  done; println ".";
  println "";

  print_title "Conversion functions with Z, N and positive";

  print_def w_to_Z "x";
  print_match "x";
  for i = 0 to base - 1 do
    print  " | ";print_w i;print " => ";printi i;println "";
  done;
  println  " end.";
  println "";

  print_def w_of_pos "p";
  print_match "p";
  for i = 1 to base - 1 do
    print " | ";print_pos i;print " => (N0, ";print_w i;println ")"
  done;
  for i = 0 to base - 1 do
    print " | ";print_pos_s "p" (i+base);
         print " => (Npos p, ";print_w i;println ")"
  done;
  println  " end.";
  println "";

  print_def w_head0 "x";
  print_match "x";
  for x = 0 to base - 1 do
    let nb = nb_head0 x in
    print " | ";print_w x; print " => ";
    if nb = 0 then println "N0"
    else (print "Npos ";print_pos nb;println "")
  done;
  println  " end.";
  println "";

  print_def w_of_N "n";
  print_match "n";
  print    " | N0 => (N0, ";print_w 0;println ")";
  println (" | Npos p => "^w_of_pos^" p");
  println  " end.";
  println "";

  print_title "Constructors for the next level";

  print_def w_WW "xh xl";
  print_match "xh, xl";
  print    " | ";print_w 0;print ", ";print_w 0;println " => W0";
  println  " | _, _ => WW xh xl";
  println "end.";
  println "";
  
  print_def w_CW "ch xl";
  print_match "ch";
  println (" | C0 xh => C0 ("^w_WW^" xh xl)");
  println (" | C1 xh => C1 ("^w_WW^" xh xl)");
  println " end.";
  println "";

  
  print_title "Comparison";
  
  print_def w_compare "x y";
  print_match "x";

  for x = 0 to base - 1 do
    print " | ";print_w x;print " => match y with ";
    for y = 0 to x - 1 do
      print " | ";print_w y; print " => Gt"
    done;
    print " | ";print_w x; print " => Eq";
    if x < base - 1 then println " | _ => Lt end"
    else println " end"
  done;
  println " end.";
  println "";


  print_title "Opposites";

  print_def w_opp_c "x";
  print_match "x";
  print " | ";print_w 0;print " => C0 "; print_w 0;println "";
  for i = 1 to base - 1 do
    print " | ";print_w i;print " => C1 "; print_w (base - i);println ""
  done;
  println  " end.";
  println "";
  
  print_def w_opp_carry "x";
  print_match "x";
  for i = 0 to base - 1 do
    print " | ";print_w i;print " => "; print_w (base - i - 1);println ""
  done;
  println  " end.";
  println "";

  print_title "Additions";

  print_def w_succ_c "x";
  print_match "x";
  for i = 0 to base - 1 do
    print  " | ";print_w i;print " => ";print_c (i+1);println "";
  done;
  println  " end.";
  println "";

  print_def w_carry_succ_c "cx";
  print_match "cx";
  print   " | C0 x => "; print w_succ_c;println " x";
  print   " | C1 x => C1 (without_c ("; print w_succ_c;println " x))"; 
  println " end.";
  println "";
  
  print_def w_add_c "x y";
  print_match "x";
  print     " | ";print_w 0;println " => C0 y";
  for x = 1 to base - 1 do
    print " | ";print_w x;
    print " => match y with "; print_w 0;print " => C0 ";print_w x;
    for y = 1 to base - 1 do
      print    " | ";print_w y; print " => ";
      print_c (x+y);
    done;
    println " end"
  done;
  println  " end.";
  println "";

  print_def w_add_carry_c "x y";
  print_match "x";
  for x = 0 to base - 2 do
    print " | ";print_w x;
    print   " => match y with ";print_w 0;print " => ";print_c (x+1);
    for y = 1 to base - 1 do
      print    " | ";print_w y; print " => "; print_c (x+y+1);
    done;
    println " end";
  done;
  print    " | ";print_w (base-1);println " => C1 y";
  println  " end.";
  println "";

  print_def w_add "x y";
  println (" without_c ("^w_add_c^" x y).");
  println "";

  print_title "Subtractions";
  
  print_def w_pred_c "x";
  print_match "x";
  for i = 0 to base - 1 do
    print    " | "; print_w i;print " => ";print_c (i-1);println ""
  done;
  println  " end.";
  println "";
  
  print_def w_sub_c "x y";
  print_match "y";
  print    " | ";print_w 0;println " => C0 x";
  for y = 1 to base - 1 do
    print " | ";print_w y;
    print   " => match x with ";print_w 0;print " => ";print_c (-y);
    for x = 1 to base - 1 do
      print    " | ";print_w x; print " => "; print_c (x-y)
    done;
    println " end"
  done;
  println  " end.";
  println "";
  
  print_def w_sub_carry_c "x y";
  print_match "y";
  for y = 0 to base - 2 do
    print " | ";print_w y;
    print   " => match x with ";print_w 0;print " => ";print_c (-y-1);
    for x = 1 to base - 1 do
      print    " | ";print_w x; print " => "; print_c (x-y-1);
    done;
    println " end"
  done;
  print    " | ";print_w (base-1);println " => C1 x";
  println  " end.";
  println "";

  print_def w_sub "x y";
  println (" without_c ("^w_sub_c^" x y).");
  println "";

  print_title "Multiplcations";

  print_def w_mul_c "x y";
  print_match "x";
  print     " | ";print_w 0; print " => W0";println "";
  print     " | ";print_w 1; print " => WW ";print_w 0;println " y";
  for x = 2 to base - 1 do
    print " | ";print_w x;
    print   " => match y with ";print_w 0;print " => W0";
    print   " | ";print_w 1; print " => WW ";print_w 0;print " x";
    for y = 2 to base - 1 do
      let prod = x * y in
      print " | ";print_w y; print " => WW ";
      print_w (prod/base);print " ";print_w prod
    done;
    println " end"
  done;
  println  " end.";
  println "";

  print_def w_mul "x y";
  print_match (w_mul_c^" x y");
  print   " | W0 => ";print_w 0;println "";
  println " | WW _ l => l";
  println " end.";
  println "";

  print_def w_square_c "x";
  print_match "x";
  for x = 0 to base - 1 do 
    let prod = x * x in
    print " | ";print_w x;print " => WW ";
    print_w (prod/base);print " ";print_w prod;println ""
  done;
  println  " end.";
  println "";

  print_title "Division";

  print_def w_div_wB "x y";
  print_match "y";
  for y = 0 to base/2 - 1 do
    print " | ";print_w y;print " => (C0 ";print_w 0; 
                                      print ", ";print_w 0;println ")"; 
  done;
  for y = base/2 to base - 1 do
    print " | ";print_w y;print " => match x with ";
    print_w 0;print " => (C0 ";print_w 0; print ", ";print_w 0;print ")"; 
    for x = 1 to base - 1 do
      print " | ";print_w x;print " => (";
      let xB = x*base in 
      let q, r = xB / y, xB mod y in
      print_c q; print ", ";print_w r;print ")";
    done;
    println "   end";
  done;
  println " end.";
  println "";
    
  print_def w_div21 "a1 a2 b";
  println (" let (q,s) := "^w_div_wB^" a1 b in");
  println (" match "^w_add_c^" s a2 with");
  println (" | C0 r =>");
  println ("   match "^w_compare^" r b with");
  println ("   | Lt => (q, r)");
  println ("   | _ =>");
  println ("     let q := "^w_carry_succ_c^" q in");
  println ("     let r := "^w_sub^" r b in");
  println ("     match "^w_compare^" r b with");
  println ("     | Lt => (q, r)");
  println ("     | _ => ("^w_carry_succ_c^" q, "^w_sub^" r b)");
  println ("     end");
  println ("   end");
  println (" | C1 r =>");
  println ("   let q := "^w_carry_succ_c^" q in");
  println ("   match "^w_sub_c^" r b with");
  println ("   | C0 r => ("^w_carry_succ_c^" q, "^w_sub^" r b)");
  println ("   | C1 r =>");
  println ("     match "^w_compare^" r b with");
  println ("     | Lt => (q, r)");
  println ("     | _ => ("^w_carry_succ_c^" q, "^w_sub^" r b)");
  println ("     end");
  println ("   end");
  println (" end.");
  println "";

  print_title "Lift operations";

  for i = 1 to !digits - 1 do
    print_def (w_lsl_i i) "x";
    print_match "x";
    for x = 0 to base - 1 do
      print " | ";print_w x;print " => ";print_w (x lsl i); println "";
    done;
    println (" end.");
    println ""
  done;
  println "";
 
  for i = 1 to !digits - 1 do
    print_def (w_lsr_i i) "x";
    print_match "x";
    for x = 0 to base - 1 do
      print " | ";print_w x;print " => ";print_w (x lsr i); println "";
    done;
    println (" end.");
    println ""
  done;
  println "";

  print_def w_add_mul_div "x y p";
  print_match "p";
  for p = 1 to !digits - 1 do
    print " | ";print_pos p; println (" => "^
       w_add^" ("^(w_lsl_i p)^" x) ("^(w_lsr_i (!digits - p))^" y)")
  done;
  print " | _ => ";print_w 0;println "";
  print " end.";
  println "";

  print_title ("Record of basic operators for base "^(string_of_int base));

  print_def w_op "";
  print    " mk_znz_op ";printi !digits; println "";
  print    "       ";print w_to_Z; println (" "^w_of_pos^" "^w_head0);
  print    "       ";print_w 0;print " ";print_w 1;print " ";
                                            print_w (base-1);println ""; 
  println ("       "^w_WW^" "^w_CW);
  println ("       "^w_compare);
  println ("       "^w_opp_c^" "^w_opp_carry);
  println ("       "^w_succ_c); 
  println ("       "^w_add_c^" "^w_add_carry_c^" "^w_add);
	      println ("       "^w_pred_c); 
  println ("       "^w_sub_c^" "^w_sub_carry_c^" "^w_sub);
  println ("       "^w_mul_c^" "^w_mul^" "^w_square_c); 
  println ("       "^w_div21^" "^w_add_mul_div^"."); 
  println ""

  
let _ = 
  Format.print_flush ()

