#include "mini-gmp.h"
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/
{
  return x >= 0 ? x : -x;
}

int gmp_max(int a, int b)
/*@
  Require emp
  Ensure __return == Zmax(a, b)
*/
{
  return a > b ? a : b;
}

int gmp_cmp(int a, int b)
/*@
  Require emp
  Ensure 
    emp * 
    (a > b && __return == 1 || 
    a == b && __return == 0 ||
    a < b && __return == -1)
*/
{
  return (a > b) - (a < b);
}

/* MPN interface */

/* 从 低地址向高地址 顺序复制 */
void
mpn_copyi (unsigned int *d, unsigned int *s, int n)
/*@
  With val l2 cap1 cap2
  Require
    mpd_store_Z(s, val, n, cap1) *
    store_uint_array(d, cap2, l2) &&
    Zlength(l2) == cap2 &&
    cap2 >= n
  Ensure 
    mpd_store_Z(s, val, n, cap1) *
    mpd_store_Z(d, val, n, cap2)
*/
{
  /*@
    mpd_store_Z(s, val, n, cap1)
    which implies
    exists l,
      n <= cap1 && 
      Zlength(l) == n &&
      cap1 <= 100000000 &&
      store_uint_array(s, n, l) *
      store_undef_uint_array_rec(s, n + 1, cap1) &&
      list_store_Z(l, val)
  */
  /*@
    store_uint_array(d, cap2, l2) && Zlength(l2) == cap2
    which implies
    store_uint_array_rec(d, 0, cap2, l2) * store_uint_array(d, 0, nil) &&
    Zlength(l2) == cap2
  */
  int i;
    /*@ Inv
    exists l l',
    0 <= i && i <= n && Zlength(l) == n && 
    list_store_Z(l, val) && n <= cap1 && 
    store_uint_array(s, n, l) *
    store_undef_uint_array_rec(s, n + 1, cap1) * 
    store_uint_array(d, i, sublist(0, i, l)) * 
    store_uint_array_rec(d, i, cap2, l')
  */
  for (i = 0; i < n; i++) {
      /*@
        Given l l'
      */
      /*@
        0 <= i && i < n && n <= cap2 &&
        store_uint_array_rec(d, i, cap2, l') *
        store_uint_array(d, i, sublist(0, i, l))
        which implies
        exists a l2',
        l' == cons(a, l2') && i < n && n <= cap2 &&
        store_uint_array_rec(d, i + 1, cap2, l2') *
        store_uint_array(d, i + 1, app(sublist(0, i, l), cons(a, nil)))
      */
      d[i] = s[i];
  }
}

/* 大于返回1，小于返回-1，等于返回0 */
int
mpn_cmp (unsigned int *ap, unsigned int *bp, int n)
/*@
  With cap1 cap2 val1 val2
  Require
    mpd_store_Z(ap, val1, n, cap1) *
    mpd_store_Z(bp, val2, n, cap2) &&
    n <= cap1 && n <= cap2
  Ensure
    val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1
*/
{
  /*@
    mpd_store_Z(ap, val1, n, cap1) * mpd_store_Z(bp, val2, n, cap2)
    which implies
    exists l1 l2,
    mpd_store_list(ap, l1, cap1) * mpd_store_list(bp, l2, cap2) &&
    list_store_Z(l1, val1) && list_store_Z(l2, val2) &&
    n == Zlength(l1) && n == Zlength(l2)
  */
  /*@
    Given l1 l2
  */
  --n;
  /*@Inv
    mpd_store_list(ap, l1, cap1) * mpd_store_list(bp, l2, cap2) &&
    list_store_Z(l1, val1) && list_store_Z(l2, val2) &&
    n@pre == Zlength(l1) && n@pre == Zlength(l2) &&
    sublist(n, n@pre, l1) == sublist(n, n@pre, l2)
  */
  while (n >= 0)
    {
      /*@
        mpd_store_list(ap, l1, cap1) * mpd_store_list(bp, l2, cap2)
        which implies
        store_uint_array(ap, n, l1) * store_uint_array(bp, n, l2) *
        store_undef_uint_array(ap, n + 1, cap1) * store_uint_array(bp, n + 1, cap2) &&
      */
      if (ap[n] != bp[n])
	      return ap[n] > bp[n] ? 1 : -1;
      --n;
    }
  // Note: The parser cannot parse "--n" in loop so we paraphrased it.
  /*
  while (--n >= 0)
    {
      if (ap[n] != bp[n])
	return ap[n] > bp[n] ? 1 : -1;
    }
  */
  return 0;
}

/*处理位数不同的情况*/
static int
mpn_cmp4 (unsigned int *ap, int an, unsigned int *bp, int bn)
{
  if (an != bn)
    return an < bn ? -1 : 1;
  else
    return mpn_cmp (ap, bp, an);
}

/*返回非0的位数*/
static int
mpn_normalized_size (unsigned int *xp, int n)
{
  while (n > 0 && xp[n-1] == 0)
    --n;
  return n;
}

/* 多精度数ap 加上单精度数b，返回最后产生的进位 */
unsigned int
mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
{
  int i;
  //assert (n > 0);
  i = 0;
  do
    {
      unsigned int r = ap[i] + b;
      /* Carry out */
      b = (r < b);
      rp[i] = r;
    }
  while (++i < n);

  return b;
}

/* 位数相同的多精度数ap 加上多精度数bp，返回最后产生的进位 */
unsigned int
mpn_add_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
{
  int i;
  unsigned int cy;

  for (i = 0, cy = 0; i < n; i++)
    {
      unsigned int a, b, r;
      a = ap[i]; b = bp[i];
      r = a + cy;
      cy = (r < cy);
      r += b;
      cy += (r < b);
      rp[i] = r;
    }
  return cy;
}

/*不同位数的多精度数相加，返回最后的进位*/
unsigned int
mpn_add (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
{
  unsigned int cy;
  //assert (an >= bn);
  cy = mpn_add_n (rp, ap, bp, bn);
  if (an > bn)
    cy = mpn_add_1 (rp + bn, ap + bn, an - bn, cy);
  return cy;
}

unsigned int
mpn_sub_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
{
  int i;
  //assert (n > 0);
  i = 0;
  do
    {
      unsigned int a = ap[i];
      /* Carry out */
      unsigned int cy = a < b;
      rp[i] = a - b;
      b = cy;
    }
  while (++i < n);

  return b;
}

unsigned int
mpn_sub_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
{
  int i;
  unsigned int cy;

  for (i = 0, cy = 0; i < n; i++)
    {
      unsigned int a, b;
      a = ap[i]; b = bp[i];
      b += cy;
      cy = (b < cy);
      cy += (a < b);
      rp[i] = a - b;
    }
  return cy;
}

unsigned int
mpn_sub (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
{
  unsigned int cy;
  //assert (an >= bn);
  cy = mpn_sub_n (rp, ap, bp, bn);
  if (an > bn)
    cy = mpn_sub_1 (rp + bn, ap + bn, an - bn, cy);
  return cy;
}

/* MPZ interface */

void
mpz_clear (mpz_t r)
{
  if (r->_mp_alloc)
    gmp_free_limbs (r->_mp_d, r->_mp_alloc);
}

static unsigned int *
mpz_realloc (mpz_t r, int size)
{
  size = gmp_max (size, 1);

  if (r->_mp_alloc)
    r->_mp_d = gmp_realloc_limbs (r->_mp_d, r->_mp_alloc, size);
  else
    r->_mp_d = gmp_alloc_limbs (size);
  r->_mp_alloc = size;

  if (gmp_abs (r->_mp_size) > size)
    r->_mp_size = 0;

  return r->_mp_d;
}

/* Realloc for an mpz_t WHAT if it has less than NEEDED limbs.  */
unsigned int *mrz_realloc_if(mpz_t z,int n) {
  return n > z->_mp_alloc ? mpz_realloc(z, n) : z->_mp_d;
}

/* MPZ comparisons and the like. */
int
mpz_sgn (const mpz_t u)
{
  return gmp_cmp (u->_mp_size, 0);
}

void
mpz_swap (mpz_t u, mpz_t v)
{
  int_swap (u->_mp_alloc, v->_mp_alloc);
  unsigned int *_swap(u->_mp_d, v->_mp_d);
  int_swap (u->_mp_size, v->_mp_size);
}

/* MPZ addition and subtraction */

static int
mpz_abs_add (mpz_t r, const mpz_t a, const mpz_t b)
{
  int an = gmp_abs (a->_mp_size);
  int bn = gmp_abs (b->_mp_size);
  unsigned int *rp;
  unsigned int cy;

  if (an < bn)
    {
      mpz_srcptr_swap (a, b);
      int_swap (an, bn);
    }

  rp = mrz_realloc_if (r, an + 1);
  cy = mpn_add (rp, a->_mp_d, an, b->_mp_d, bn);

  rp[an] = cy;

  return an + cy;
}

static int
mpz_abs_sub (mpz_t r, const mpz_t a, const mpz_t b)
{
  int an = gmp_abs (a->_mp_size);
  int bn = gmp_abs (b->_mp_size);
  int cmp;
  unsigned int *rp;

  cmp = mpn_cmp4 (a->_mp_d, an, b->_mp_d, bn);
  if (cmp > 0)
    {
      rp = mrz_realloc_if (r, an);
      mpn_sub (rp, a->_mp_d, an, b->_mp_d, bn);
      return mpn_normalized_size (rp, an);
    }
  else if (cmp < 0)
    {
      rp = mrz_realloc_if (r, bn);
      mpn_sub (rp, b->_mp_d, bn, a->_mp_d, an);
      return -mpn_normalized_size (rp, bn);
    }
  else
    return 0;
}

void
mpz_add (mpz_t r, const mpz_t a, const mpz_t b)
{
  int rn;

  if ( (a->_mp_size ^ b->_mp_size) >= 0)
    rn = mpz_abs_add (r, a, b);
  else
    rn = mpz_abs_sub (r, a, b);

  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}

void
mpz_sub (mpz_t r, const mpz_t a, const mpz_t b)
{
  int rn;

  if ( (a->_mp_size ^ b->_mp_size) >= 0)
    rn = mpz_abs_sub (r, a, b);
  else
    rn = mpz_abs_add (r, a, b);

  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}
