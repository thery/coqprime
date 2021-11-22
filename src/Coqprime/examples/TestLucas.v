
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Import ZArith.
From Coqprime Require Import Lucas.

Eval native_compute in 2.

Time Eval native_compute in lucas 2.

Eval native_compute in 3.

Time Eval native_compute in lucas 3.

Eval native_compute in 5.

Time Eval native_compute in lucas 5.

Eval native_compute in 7.

Time Eval native_compute in lucas 7.

Eval native_compute in 13.

Time Eval native_compute in lucas 13.

Eval native_compute in 17.

Time Eval native_compute in lucas 17.

Eval native_compute in 19.

Time Eval native_compute in lucas 19.

Eval native_compute in 31.

Time Eval native_compute in lucas 31.

Eval native_compute in 61.

Time Eval native_compute in lucas 61.

Eval native_compute in 89.

Time Eval native_compute in lucas 89.

Eval native_compute in 107.

Time Eval native_compute in lucas 107.

Eval native_compute in 127.

Time Eval native_compute in lucas 127.

Eval native_compute in 521.

Time Eval native_compute in lucas 521.

Eval native_compute in 607.

Time Eval native_compute in lucas 607.

Eval native_compute in 1279.

Time Eval native_compute in lucas 1279.

Eval native_compute in 2203.

Time Eval native_compute in lucas 2203.

Eval native_compute in 2281.

Time Eval native_compute in lucas 2281.

Eval native_compute in 3217.

Time Eval native_compute in lucas 3217.

Eval native_compute in 4253.

Time Eval native_compute in lucas 4253.

Eval native_compute in 4423.

Time Eval native_compute in lucas 4423.

Time Eval native_compute in 9689.

Time Eval native_compute in lucas 9689.

Time Eval native_compute in 9941.

(* 
Time Eval native_compute in lucas 9941.

Time Eval native_compute in 11213.

Time Eval native_compute in lucas 11213.

Time Eval native_compute in 19937.

Time Eval native_compute in lucas 19937.

Time Eval native_compute in 21701.

Time Eval native_compute in lucas 21701.

Time Eval native_compute in 23209.

Time Eval native_compute in lucas 23209.

Time Eval native_compute in 44497.

Time Eval native_compute in lucas 44497.

Time Eval native_compute in 86243.

Time Eval native_compute in lucas 86243.

Time Eval native_compute in 110503.

Time Eval native_compute in lucas 110503.

Time Eval native_compute in 132049.

Time Eval native_compute in lucas 132049.

Time Eval native_compute in 216091.

Time Eval native_compute in lucas 216091.
*)

(*
     = 3
     = 0
Finished transaction in 0. secs (0.01u,0.s)
     = 5
     = 0
Finished transaction in 0. secs (0.u,0.s)
     = 7
     = 0
Finished transaction in 0. secs (0.u,0.s)
     = 13
     = 0
Finished transaction in 0. secs (0.u,0.s)
     = 17
     = 0
Finished transaction in 0. secs (0.u,0.s)
     = 19
     = 0
Finished transaction in 0. secs (0.u,0.s)
     = 31
     = 0
Finished transaction in 0. secs (0.u,0.s)
     = 61
     = 0
Finished transaction in 0. secs (0.01u,0.s)
     = 89
     = 0
Finished transaction in 0. secs (0.02u,0.s)
     = 107
     = 0
Finished transaction in 0. secs (0.02u,0.s)
     = 127
     = 0
Finished transaction in 0. secs (0.04u,0.s)
     = 521
     = 0
Finished transaction in 2. secs (1.85u,0.01s)
     = 607
     = 0
Finished transaction in 3. secs (2.78u,0.07s)
     = 1279
     = 0
Finished transaction in 21. secs (20.21u,0.26s)
     = 2203
     = 0
Finished transaction in 94. secs (89.1u,1.05s)
     = 2281
     = 0
Finished transaction in 102. secs (97.59u,1.1s)
     = 3217
     = 0
Finished transaction in 244. secs (237.65u,2.39s)
     = 4253
     = 0
Finished transaction in 506. secs (494.09u,4.65s)
     = 4423
     = 0
Finished transaction in 572. secs (563.27u,5.45s)

*)

