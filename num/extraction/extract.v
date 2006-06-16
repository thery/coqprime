Require Import GenWord.
Require Import Mod_op.
Require Import Lucas.

Unset Extraction Optimize.
Unset Extraction AutoInline.

Recursive Extraction Library GenWord.
Recursive Extraction Library Mod_op.
Recursive Extraction Library Lucas.

coqtop  -I ../ -I ../../Tactic -I ../../N -I ../../Z -I ../../PrimalityTest -I ../../List  -I ../W/W8
