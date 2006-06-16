#include "caml/alloc.h"
#include "caml/memory.h"
#include "caml/mlvalues.h"

#define Eq (Val_int(0))
#define Lt (Val_int(1))
#define Gt (Val_int(2))

#define Coq_true (Val_int(0))
#define Coq_false (Val_int(1))

#define Alloc_small(res, n, tag) (res = caml_alloc_small(n, tag))

#define UWtype unsigned long
#define UWsize 32
#define UWhalfsize (UWsize/2)
#define __ll_highpart(x) (((UWtype)(x))>> UWhalfsize)
#define __ll_lowpart(x) (((UWtype)(x)) & 0xFFFF)
#define __ll_B (1 << UWhalfsize)

CAMLprim value uint_lt (value x, value y) {
  if (((unsigned long)x) < ((unsigned long)y)) return Coq_true;
  else return Coq_false;
}

CAMLprim value uint_le (value x, value y) {
  if (((unsigned long)x) <= ((unsigned long)y)) return Coq_true;
  else return Coq_false;
}

CAMLprim value uint_compare(value x, value y) {
  unsigned long ux, uy;
  ux = ((unsigned long)x); uy = ((unsigned long)y);
  if (ux < uy) return Lt;
  else if (ux == uy) return Eq;
  else return Gt;
}


CAMLprim value uint_mul_c (value u, value v) {
  value res;
  UWtype w1, w0;
  UWtype __x0, __x1, __x2, __x3;					
  UWtype __ul, __vl, __uh, __vh;					
  UWtype __v = ((UWtype)v) ^ 1;
  
  __ul = __ll_lowpart(Unsigned_long_val(u));
  __uh = ((UWtype)u) >> (UWhalfsize + 1);
  __vl = __ll_lowpart (__v);			
  __vh = __ll_highpart (__v);			
						
  __x0 = (UWtype) __ul * __vl;		
  __x1 = (UWtype) __ul * __vh;		
  __x2 = (UWtype) __uh * __vl;		
  __x3 = (UWtype) __uh * __vh;		
									
  __x1 += __ll_highpart (__x0); /* this can't give carry */		
  __x1 += __x2;		        /* but this indeed can */		
  if (__x1 < __x2)		/* did we get it? */			
    __x3 += __ll_B;		/* yes, add it in the proper pos. */	
  
  w1 = __x3 + __ll_highpart (__x1);			
  w0 = ((__x1 << UWhalfsize) + __ll_lowpart (__x0));

  Alloc_small(res, 2, 0);
  Field(res, 0) = Val_long(w1);
  Field(res, 1) = (value)(w0 | 1);
  return res;
 
}

CAMLprim value uint_div21(value v1, value v0, value vd) {
  value res;
  unsigned long q, r, n1, n0, d; 
  unsigned long __d1, __d0, __q1, __q0, __r1, __r0, __m;
  d = ((UWtype)vd) ^ 1;
  n0 = ((UWtype)v0) ^ 1;
  n1 = Unsigned_long_val(v1);
  /* start GMP code */
  __d1 = __ll_highpart (d);						
  __d0 = __ll_lowpart (d);						
	
    __q1 = (n1) / __d1;							
    __r1 = (n1) - __q1 * __d1;						
    __m = (UWtype) __q1 * __d0;						
    __r1 = __r1 * __ll_B | __ll_highpart (n0);				
    if (__r1 < __m)							
      {									
	__q1--, __r1 += (d);						
	if (__r1 >= (d)) /* i.e. we didn't get carry when adding to __r1 */
	  if (__r1 < __m)						
	    __q1--, __r1 += (d);					
      }									
    __r1 -= __m;							
									
    __q0 = __r1 / __d1;							
    __r0 = __r1  - __q0 * __d1;						
    __m = (UWtype) __q0 * __d0;						
    __r0 = __r0 * __ll_B | __ll_lowpart (n0);				
    if (__r0 < __m)							
      {									
	__q0--, __r0 += (d);						
	if (__r0 >= (d))						
	  if (__r0 < __m)						
	    __q0--, __r0 += (d);					
      }									
    __r0 -= __m;							
									
    q = (UWtype) __q1 * __ll_B | __q0;				
    r = __r0;								
    /* end GMP code */
    Alloc_small(res, 2, 0);
    Field(res, 0) = Val_long(q);
    Field(res, 1) = (value)(r | 1);
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


   

  

