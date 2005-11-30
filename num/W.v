Unset Boxed Definitions.
Set Implicit Arguments.

Require Import ZArith.
Require Import ZnZ.
Require Import Zn2Z.
Require Import W8.


(* ** Type of words ** *)

Definition w16 := zn2z w8.
Definition w32 := zn2z w16.
Definition w64 := zn2z w32.
Definition w128 := zn2z w64.
Definition w256 := zn2z w128.
Definition w512 := zn2z w256.
Definition w1024 := zn2z w512.
Definition w2048 := zn2z w1024.
Definition w4096 := zn2z w2048.
Definition w8192 := zn2z w4096.
Definition w16384 := zn2z w8192.
Definition w32768 := zn2z w16384.
Definition w65536 := zn2z w32768.
Definition w131072 := zn2z w65536.

(* ** Operators ** *)
Definition w16_op := mk_zn2z_op w8_op.           
Definition w32_op := mk_zn2z_op w16_op.
Definition w64_op := mk_zn2z_op w32_op.
Definition w128_op := mk_zn2z_op_karastuba w64_op.
Definition w256_op := mk_zn2z_op_karastuba w128_op.
Definition w512_op := mk_zn2z_op_karastuba w256_op.
Definition w1024_op := mk_zn2z_op_karastuba w512_op.
Definition w2048_op := mk_zn2z_op_karastuba w1024_op.
Definition w4096_op := mk_zn2z_op_karastuba w2048_op.
Definition w8192_op := mk_zn2z_op_karastuba w4096_op.
Definition w16384_op := mk_zn2z_op_karastuba w8192_op.
Definition w32768_op := mk_zn2z_op_karastuba w16384_op.
Definition w65536_op := mk_zn2z_op_karastuba w32768_op.
Definition w131072_op := mk_zn2z_op_karastuba w65536_op.





