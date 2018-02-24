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

#define UWtype uint64
#define UWsize 64
#define __ll_B ((UWtype)1 << (UWsize / 2))
#define __ll_lowpart(t) ((UWtype) (t) & (__ll_B - 1))
#define __ll_highpart(t) ((UWtype) (t) >> (UWsize / 2))

CAMLprim value uint64_compare(value vx, value vy) {
  UWtype x, y;
  x = (UWtype)Int64_val(vx);
  y = (UWtype)Int64_val(vy);
  if ((UWtype)x < (UWtype)y) return Lt;
  else if ((UWtype)x > (UWtype)y) return Gt;
  else return Eq;
}

CAMLprim value uint64_add_c (value vx, value vy) 
{
  CAMLparam0();
  CAMLlocal2(res, r);
  UWtype x, y, _r;
  x = (UWtype)Int64_val(vx);
  y = (UWtype)Int64_val(vy);
  _r = x + y;
  r = caml_copy_int64(_r);
  if ((UWtype)_r < (UWtype)x) Alloc_small(res, 1, 1);
  else Alloc_small(res, 1, 0);
  Field(res, 0) = r;
  CAMLreturn(res);
}

CAMLprim value uint64_add_carry_c (value vx, value vy) 
{
  CAMLparam0();
  CAMLlocal2(res, r);
  UWtype x, y, _r;
  x = (UWtype)Int64_val(vx);
  y = (UWtype)Int64_val(vy);
  _r = x + y + (UWtype)1;
  r = caml_copy_int64(_r);
  if ((UWtype)_r <= (UWtype)x) Alloc_small(res, 1, 1);
  else Alloc_small(res, 1, 0);
  Field(res, 0) = r;
  CAMLreturn(res);
}

CAMLprim value uint64_sub_c (value vx, value vy) 
{
  CAMLparam0();
  CAMLlocal2(res, r);
  UWtype x, y, _r;
  x = (UWtype)Int64_val(vx);
  y = (UWtype)Int64_val(vy);
  _r = x - y;
  r = caml_copy_int64(_r);
  if ((UWtype)x < (UWtype)_r) Alloc_small(res, 1, 1);
  else Alloc_small(res, 1, 0);
  Field(res, 0) = r;
  CAMLreturn(res);
}

CAMLprim value uint64_sub_carry_c (value vx, value vy) 
{
  CAMLparam0();
  CAMLlocal2(res, r);
  UWtype x, y, _r;
  x = (UWtype)Int64_val(vx);
  y = (UWtype)Int64_val(vy);
  _r = x - y - (UWtype)1;
  r = caml_copy_int64(_r);
  if ((UWtype)x <= (UWtype)_r) Alloc_small(res, 1, 1);
  else Alloc_small(res, 1, 0);
  Field(res, 0) = r;
  CAMLreturn(res);
}

CAMLprim value uint64_mul_c (value vu, value vv) 
{
  CAMLparam0();
  CAMLlocal3(res, H, L);
  UWtype u, v, h, l;
  UWtype __x0, __x1, __x2, __x3;					
  UWtype __ul, __vl, __uh, __vh;					

  u = Int64_val(vu);
  v = Int64_val(vv);

  if (u == (UWtype)0 && v == (UWtype)0) CAMLreturn (Val_int(0)); 

  __ul = __ll_lowpart(u);
  __uh = __ll_highpart(u);
  __vl = __ll_lowpart (v);			
  __vh = __ll_highpart (v);			
						
  __x0 = (UWtype) __ul * __vl;		
  __x1 = (UWtype) __ul * __vh;		
  __x2 = (UWtype) __uh * __vl;		
  __x3 = (UWtype) __uh * __vh;		
									
  __x1 += __ll_highpart (__x0); /* this can't give carry */		
  __x1 += __x2;		        /* but this indeed can */		
  if (__x1 < __x2)		/* did we get it? */			
    __x3 += __ll_B;		/* yes, add it in the proper pos. */	
  
  h = __x3 + __ll_highpart (__x1);			
  l = ((__x1 << (UWsize / 2)) + __ll_lowpart (__x0));

  H = caml_copy_int64(h);
  L = caml_copy_int64(l);
  Alloc_small(res, 2, 0);
  Field(res, 0) = H;
  Field(res, 1) = L;
  CAMLreturn(res);
}

CAMLprim value uint64_div21(value v1, value v0, value vd) {
  CAMLparam0();
  CAMLlocal3(res, Q, R);
  UWtype q, r, n1, n0, d; 
  UWtype __d1, __d0, __q1, __q0, __r1, __r0, __m;
  d = (UWtype)Int64_val(vd);
  n0 = (UWtype)Int64_val(v0);
  n1 = (UWtype)Int64_val(v1);
  /* start GMP code */
  __d1 = __ll_highpart (d);						
  __d0 = __ll_lowpart (d);						
	
    __q1 = (n1) / __d1;							
    __r1 = (n1) - __q1 * __d1;						
    __m = (UWtype) __q1 * __d0;						
    __r1 = (__r1 << (UWsize /2)) | __ll_highpart (n0);				
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
    __r0 = (__r0 << (UWsize /2)) | __ll_lowpart (n0);
    if (__r0 < __m)							
      {									
	__q0--, __r0 += (d);						
	if (__r0 >= (d))						
	  if (__r0 < __m)						
	    __q0--, __r0 += (d);					
      }									
    __r0 -= __m;							
									
    q = (UWtype) (__q1 << ( UWsize / 2)) | __q0;
    r = __r0;								
    /* end GMP code */

    Q = caml_copy_int64(q);
    R = caml_copy_int64(r);
    Alloc_small(res, 2, 0);
    Field(res, 0) = Q;
    Field(res, 1) = R;
    CAMLreturn(res);
}

CAMLprim value uint64_div_eucl(value vx, value vy) {
  CAMLparam0();
  CAMLlocal3(res, Q, R);
  UWtype x, y, q, r;
  x = (UWtype)Int64_val(vx);
  y = (UWtype)Int64_val(vy);
  q = x / y;
  r = x % y;
  Q = caml_copy_int64(q);
  R = caml_copy_int64(r);
  Alloc_small(res, 2, 0);
  Field(res, 0) = Q;
  Field(res, 1) = R;
  CAMLreturn(res);
}

CAMLprim value uint64_mod(value vx, value vy) {
  UWtype x, y, r;
  x = (UWtype)Int64_val(vx);
  y = (UWtype)Int64_val(vy);
  r = x % y;
  return caml_copy_int64(r);
}


   

  

