#include "caml/config.h"
#include "caml/alloc.h"
#include "caml/memory.h"
#include "caml/mlvalues.h"


#define Eq (Val_int(0))
#define Lt (Val_int(1))
#define Gt (Val_int(2))

#define Coq_true (Val_int(0))
#define Coq_false (Val_int(1))

#define Alloc_small(res, n, tag) (res = caml_alloc_small(n, tag))

#define Make_C0(res, v) do {     \
    Alloc_small(res, 1, 0);      \
    Field(res, 0) = v;           \
    } while(0)                   

#define Make_C1(res, v) do {     \
    Alloc_small(res, 1, 1);      \
    Field(res, 0) = v;           \
    } while(0)                   \

#define UWtype unsigned long
#define UWsize 32
#define UWhalfsize (UWsize/2)
#define __ll_highpart(x) (((UWtype)(x))>> UWhalfsize)
#define __ll_lowpart(x) (((UWtype)(x)) & 0xFFFF)
#define __ll_B (1 << UWhalfsize)

CAMLprim value uint_compare(value x, value y) {
  unsigned long ux, uy;
  ux = ((unsigned long)x); uy = ((unsigned long)y);
  if (ux < uy) return Lt;
  else if (ux == uy) return Eq;
  else return Gt;
}

CAMLprim value uint_add_c (value x, value y) {
  value res, _r;
  _r =(value)((long)x + (long)y -1);
  if (((UWtype)_r) < ((UWtype)x)) Make_C1(res,_r);
  else Make_C0(res, _r);
  return res;
}

CAMLprim value uint_add_carry_c (value x, value y) {
  value res, _r;
  _r =(value)((long)x + (long)y + 1);
  if (((UWtype)_r) <= ((UWtype)x)) Make_C1(res,_r);
  else Make_C0(res, _r);
  return res;
}


CAMLprim value uint_sub_c(value x, value y) {
  value res, _r;
  _r =(value) ((long)x - (long) y + 1);
  if ((UWtype)x < (UWtype)_r) Make_C1(res, _r);
  else Make_C0(res, _r);
  return res;
}

CAMLprim value uint_sub_carry_c(value x, value y) {
  value res, _r;
   _r = (value)((long)x - (long)y - 1);
  if ((UWtype)x <= (UWtype)_r) Make_C1(res, _r);
  else Make_C0(res,_r);
  return res;
}


CAMLprim value uint_mul_c (value u, value v) {
  uint64 x, y, z;
  value res;
  x = (uint64) (Unsigned_long_val(u));
  y = (uint64) (((UWtype)v) ^ 1);
  z = x * y;
  if (z == 0) res = Val_long(0);
  else {
    Alloc_small(res, 2, 0);
    Field(res, 0) = Val_long((uint32)(z >> 32));
    Field(res, 1) = (value)
         (((uint32)(z  & (((uint64)1 << 32) - 1))) | 1);
  }
  return res;
 
}

CAMLprim value uint_div21(value v1, value v0, value vd) {
  uint64 x, y, q, r;
  value res;
  x = (uint64) (Unsigned_long_val(v1)) << 32 | 
      (uint64) (((UWtype)v0) ^ 1);
  y = (uint64) (((UWtype)vd) ^ 1);

  q = x / y;
  r = x - y * q;
  
  Alloc_small(res, 2, 0);
  Field(res, 0) = Val_long((uint32)q);
  Field(res, 1) = (value)((uint32)r | 1);
  return res;
}

CAMLprim value uint_div_eucl(value x, value y) {
  value res;
  unsigned long ux, uy, uq, ur;
  ux =Unsigned_long_val(x);
  uy = Unsigned_long_val(y);
  uq = ux / uy;
  ur = ux % uy;
  Alloc_small(res, 2, 0);
  Field(res, 0) = Val_long(uq);
  Field(res, 1) = Val_long(ur);
  return res;
}

CAMLprim value uint_mod(value x, value y) {
  unsigned long ux, uy;
  ux =Unsigned_long_val(x);
  uy = Unsigned_long_val(y);
  return Val_long (ux % uy);
}


   

  

