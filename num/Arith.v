Require Import ZArith.
Require Import W8_op.
Require Import W8_op_spec.
Require NMake.
Require ZMake.

Module W0.

 Definition w := w8.
 Definition w_op := w8_op.
 Definition w_spec := w8_op_spec.

End W0.

Module N <: ZMake.NType := NMake.Make W0.

Module Z := ZMake.Make N.

