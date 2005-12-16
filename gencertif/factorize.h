#include "gmp.h"
#include "certif.h"

#ifndef __FACTORIZE_H__

void set_verbose();
pock_certif_t mersenne_certif (mpz_t t, unsigned long int p);
pock_certif_t pock_certif (mpz_t t);
void extend_lc (certif_t lc, pock_certif_t c, unsigned long int min,
		unsigned long int max );
#define  __FACTORIZE_H__
#endif  /* __FACTORIZE_H__ */
