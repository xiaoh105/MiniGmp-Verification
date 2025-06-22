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
  Ensure __return == Z::max(a, b)
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
      store_undef_uint_array_rec(s, n, cap1) &&
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
    store_undef_uint_array_rec(s, n, cap1) * 
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
    mpd_store_Z_compact(ap, val1, n, cap1) *
    mpd_store_Z_compact(bp, val2, n, cap2) &&
    0 <= n && n <= cap1 && n <= cap2 && 
    cap1 <= 100000000 && cap2 <= 100000000
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(ap@pre, val1, n@pre, cap1) *
    mpd_store_Z_compact(bp@pre, val2, n@pre, cap2)
*/
{
  /*@
    mpd_store_Z_compact(ap@pre, val1, n@pre, cap1) * mpd_store_Z_compact(bp@pre, val2, n@pre, cap2)
    which implies
    exists l1 l2,
    store_uint_array(ap@pre, n@pre, l1) * store_uint_array(bp@pre, n@pre, l2) *
    store_undef_uint_array_rec(ap@pre, n@pre, cap1) * 
    store_undef_uint_array_rec(bp@pre, n@pre, cap2) &&
    list_store_Z_compact(l1, val1) && list_store_Z_compact(l2, val2) &&
    n@pre == Zlength(l1) && n@pre == Zlength(l2)
  */
  /*@
    Given l1 l2
  */
  --n;
  /*@Inv
    -1 <= n && n < n@pre &&
    store_uint_array(ap@pre, n@pre, l1) * store_uint_array(bp@pre, n@pre, l2) *
    store_undef_uint_array_rec(ap@pre, n@pre, cap1) * 
    store_undef_uint_array_rec(bp@pre, n@pre, cap2) &&
    list_store_Z_compact(l1, val1) && list_store_Z_compact(l2, val2) &&
    n@pre == Zlength(l1) && n@pre == Zlength(l2) &&
    sublist(n + 1, n@pre, l1) == sublist(n + 1, n@pre, l2)
  */
  while (n >= 0)
    {
      if (ap[n] != bp[n])
	      return ap[n] > bp[n] ? 1 : -1;
      --n;
    }
  // Note: The parser cannot parse "--n" in loop condition so we paraphrased it.
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
/*@
  With cap1 cap2 val1 val2
  Require
    mpd_store_Z_compact(ap, val1, an, cap1) *
    mpd_store_Z_compact(bp, val2, bn, cap2) &&
    an >= 0 && bn >= 0 && an <= cap1 && bn <= cap2 &&
    cap1 <= 100000000 && cap2 <= 100000000
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(ap@pre, val1, an@pre, cap1) *
    mpd_store_Z_compact(bp@pre, val2, bn@pre, cap2)
*/
{
  if (an != bn)
    return an < bn ? -1 : 1;
  else {
    /*@
      an@pre == bn@pre && bn@pre <= cap2
      which implies
      an@pre <= cap2
    */
    return mpn_cmp (ap, bp, an);
  }
}


/*返回非0的位数*/
static int
mpn_normalized_size (unsigned int *xp, int n)
/*@
  With cap val
  Require
    mpd_store_Z(xp, val, n, cap) &&
    0 <= n && n <= cap && cap <= 100000000
  Ensure
    0 <= __return && __return <= cap &&
    mpd_store_Z_compact(xp@pre, val, __return, cap)
*/
{
  /*@
    mpd_store_Z(xp@pre, val, n, cap)
    which implies
    exists l,
    list_store_Z(sublist(0, n, l), val) &&
    Zlength(l) == n &&
    store_uint_array(xp@pre, n, sublist(0, n, l)) *
    store_undef_uint_array_rec(xp@pre, n, cap)
  */
  /*@
    Given l
  */
  /*@Inv
    n >= 0 && n <= n@pre && 
    n@pre >= 0 && n@pre <= cap && cap <= 100000000 &&
    list_store_Z(sublist(0, n, l), val) &&
    store_uint_array(xp@pre, n, sublist(0, n, l)) *
    store_undef_uint_array_rec(xp@pre, n, cap)
  */
  while (n > 0 && xp[n-1] == 0)
    --n;
  return n;
}

/* 多精度数ap 加上单精度数b，返回最后产生的进位 */
unsigned int
mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
/*@
  With val l2 cap1 cap2
  Require
    mpd_store_Z(ap, val, n, cap1) *
    store_uint_array(rp, cap2, l2) &&
    Zlength(l2) == cap2 &&
    cap2 >= n &&
    cap1 <= 100000000 &&
    cap2 <= 100000000 &&
    n > 0 && n <= cap1
  Ensure
    exists val',
    mpd_store_Z(ap@pre, val, n@pre, cap1) *
    mpd_store_Z(rp@pre, val', n@pre, cap2) &&
    (val' + __return * Z::pow(UINT_MOD, n@pre) == val + b@pre)
*/
{
  /*@
    mpd_store_Z(ap@pre, val, n@pre, cap1)
    which implies
    exists l,
      n@pre <= cap1 && 
      Zlength(l) == n@pre &&
      cap1 <= 100000000 &&
      store_uint_array(ap@pre, n@pre, l) *
      store_undef_uint_array_rec(ap@pre, n@pre, cap1) &&
      list_store_Z(l, val)
  */
  int i;
  //assert (n > 0);
  i = 0;
  /*
  do
    {
      unsigned int r = ap[i] + b;
      // Carry out
      b = (r < b);
      rp[i] = r;
      ++i;
    }
  while (i < n);
  */

  /*@
    store_uint_array(rp@pre, cap2, l2) && Zlength(l2) == cap2
    which implies
    store_uint_array_rec(rp@pre, 0, cap2, l2) * store_uint_array(rp@pre, 0, nil) &&
    Zlength(l2) == cap2
  */

  /*@Inv
    exists l l' l'' val1 val2,
    0 <= i && i <= n@pre &&
    list_store_Z(l, val) && n@pre <= cap1 &&
    store_uint_array(ap@pre, n@pre, l) *
    store_undef_uint_array_rec(ap@pre, n@pre, cap1) &&
    list_store_Z(sublist(0, i, l), val1) &&
    list_store_Z(l', val2) &&
    store_uint_array(rp@pre, i, l') *
    store_uint_array_rec(rp@pre, i, cap2, l'') &&
    (val2 + b * Z::pow(UINT_MOD, i) == val1 + b@pre) &&
    Zlength(l') == i
  */
  while (i<n) {
    /*@
      Given l l' l'' val1 val2
    */
    unsigned int r = ap[i] + b;
    /*@ 0 <= b && b <= UINT_MAX by local */
    b = (r < b);
    /*@
      0 <= i && i < n@pre && n@pre <= cap2 &&
      store_uint_array(rp@pre, i, l') *
      store_uint_array_rec(rp@pre, i, cap2, l'') 
      which implies
      exists a l''',
      l'' == cons(a, l''') && 0<= i  && i<n@pre && n@pre <=cap2 &&
      store_uint_array_rec(rp@pre, i+1, cap2, l''') *
      store_uint_array(rp@pre, i+1, app(l', cons(a, nil)))
     */
    rp[i] = r;
    ++i;
  }

  return b;
}

/* 位数相同的多精度数ap 加上多精度数bp，返回最后产生的进位 */
unsigned int
mpn_add_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
/*@
 With cap_a cap_b cap_r val_a val_b l_r
 Require
   mpd_store_Z(ap, val_a, n, cap_a) *
   mpd_store_Z(bp, val_b, n, cap_b) *
   store_uint_array(rp, cap_r, l_r) &&
   Zlength(l_r) == cap_r &&
   cap_a <= 100000000 &&
   cap_b <= 100000000 &&
   cap_r <= 100000000 &&
   n > 0 && n <= cap_a && n <= cap_b && n <= cap_r
 Ensure
   exists val_r_out,
   mpd_store_Z(ap@pre, val_a, n@pre, cap_a) *
   mpd_store_Z(bp@pre, val_b, n@pre, cap_b) *
   mpd_store_Z(rp@pre, val_r_out, n@pre, cap_r) &&
   (val_r_out + __return * Z::pow(UINT_MOD, n@pre) == val_a + val_b)
*/
{
  /*@
    mpd_store_Z(ap@pre, val_a, n@pre, cap_a)
    which implies
    exists l_a,
      n@pre <= cap_a &&
      Zlength(l_a) == n@pre &&
      cap_a <= 100000000 &&
      store_uint_array(ap@pre, n@pre, l_a) *
      store_undef_uint_array_rec(ap@pre, n@pre, cap_a) &&
      list_store_Z(l_a, val_a)
  */
  /*@
    mpd_store_Z(bp@pre, val_b, n@pre, cap_b)
    which implies
    exists l_b,
      n@pre <= cap_b &&
      Zlength(l_b) == n@pre &&
      cap_b <= 100000000 &&
      store_uint_array(bp@pre, n@pre, l_b) *
      store_undef_uint_array_rec(bp@pre, n@pre, cap_b) &&
      list_store_Z(l_b, val_b)
  */
  int i;
  unsigned int cy;

  /*@
  store_uint_array(rp@pre, cap_r, l_r) && Zlength(l_r) == cap_r
  which implies
    store_uint_array_rec(rp@pre, 0, cap_r, l_r) * store_uint_array(rp@pre, 0, nil) &&
    Zlength(l_r) == cap_r
  */
  i = 0;
  cy = 0;
  /*@Inv
    exists l_a l_b l_r_prefix l_r_suffix val_a_prefix val_b_prefix val_r_prefix,
      0 <= i && i <= n@pre && n@pre <= cap_a && n@pre <= cap_b && n@pre <= cap_r &&
      list_store_Z(l_a, val_a) &&
      list_store_Z(l_b, val_b) &&
      list_store_Z(sublist(0, i, l_a), val_a_prefix) &&
      list_store_Z(sublist(0, i, l_b), val_b_prefix) &&
      list_store_Z(l_r_prefix, val_r_prefix) &&
      Zlength(l_r_prefix) == i &&
      (val_r_prefix + cy * Z::pow(UINT_MOD, i) == val_a_prefix + val_b_prefix) &&
      store_uint_array(ap@pre, n@pre, l_a) *
      store_undef_uint_array_rec(ap@pre, n@pre, cap_a) *
      store_uint_array(bp@pre, n@pre, l_b) *
      store_undef_uint_array_rec(bp@pre, n@pre, cap_b) *
      store_uint_array(rp@pre, i, l_r_prefix) *
      store_uint_array_rec(rp@pre, i, cap_r, l_r_suffix)
  */
  while (i < n)
    {
      /*@
        Given l_a l_b l_r_prefix l_r_suffix val_a_prefix val_b_prefix val_r_prefix
      */
      /*@ 0 <= cy && cy <= UINT_MAX by local */
      unsigned int a, b, r;
      a = ap[i]; b = bp[i];
      r = a + cy;
      cy = (r < cy);
      r += b;
      cy += (r < b);
      /*@
        0 <= i && i < n@pre && n@pre <= cap_r &&
        store_uint_array(rp@pre, i, l_r_prefix) *
        store_uint_array_rec(rp@pre, i, cap_r, l_r_suffix)
        which implies
        exists a l_r_suffix',
        l_r_suffix == cons(a, l_r_suffix') && 0 <= i && i < n@pre && n@pre <= cap_r &&
        store_uint_array_rec(rp@pre, i+1, cap_r, l_r_suffix') *
        store_uint_array(rp@pre, i+1, app(l_r_prefix, cons(a, nil)))
      */
      rp[i] = r;
      ++i;
    }
  return cy;
}

/*不同位数的多精度数相加，返回最后的进位*/
/*unsigned int
mpn_add (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
{
  unsigned int cy;
  //assert (an >= bn);
  cy = mpn_add_n (rp, ap, bp, bn);
  if (an > bn)
    cy = mpn_add_1 (rp + bn, ap + bn, an - bn, cy);
  return cy;
}*/

/*unsigned int
mpn_sub_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
{
  int i;
  //assert (n > 0);
  i = 0;
  do
    {
      unsigned int a = ap[i];
      // Carry out
      unsigned int cy = a < b;
      rp[i] = a - b;
      b = cy;
    }
  while (++i < n);

  return b;
}*/

/*unsigned int
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
}*/

/*unsigned int
mpn_sub (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
{
  unsigned int cy;
  //assert (an >= bn);
  cy = mpn_sub_n (rp, ap, bp, bn);
  if (an > bn)
    cy = mpn_sub_1 (rp + bn, ap + bn, an - bn, cy);
  return cy;
}*/

/* MPZ interface */

void
mpz_clear (mpz_t r)
/*@
  With
    n
  Require
    store_Z(r, n)
  Ensure
    exists size cap ptr,
      r@pre -> _mp_size == size && r@pre -> _mp_alloc == cap && r@pre -> _mp_d == ptr
*/
{
  /*@
    store_Z(r@pre, n)
    which implies
    exists ptr size cap,
      (size < 0 && n < 0 && mpd_store_Z_compact(ptr, -n, -size, cap) ||
        size >= 0 && n >= 0 && mpd_store_Z_compact(ptr, n, size, cap)) &&
      r@pre -> _mp_size == size &&
      r@pre -> _mp_alloc == cap &&
      r@pre -> _mp_d == ptr
  */
  if (r->_mp_alloc)
    gmp_free_limbs (r->_mp_d, r->_mp_alloc);
}

static unsigned int *
mpz_realloc (mpz_t r, int size)
/*@
  With
    ptr old cap n
  Require
    size >= cap && size <= 100000000 && cap >= 0 && cap <= 100000000 &&
    (old < 0 && n < 0 && mpd_store_Z_compact(ptr, -n, -old, cap) ||
        old >= 0 && n >= 0 && mpd_store_Z_compact(ptr, n, old, cap)) &&
      r -> _mp_size == old &&
      r -> _mp_alloc == cap &&
      r -> _mp_d == ptr
  Ensure
    exists c ptr_new,
    c >= size@pre && 
    (n < 0 && mpd_store_Z_compact(ptr_new, -n, -old, c) ||
      n >= 0 && mpd_store_Z_compact(ptr_new, n, old, c)) &&
    r@pre -> _mp_size == old &&
    r@pre -> _mp_alloc == c &&
    r@pre -> _mp_d == ptr_new
*/
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
/*unsigned int *mrz_realloc_if(mpz_t z,int n) 
{
  return n > z->_mp_alloc ? mpz_realloc(z, n) : z->_mp_d;
}*/

/* MPZ comparisons and the like. */
int
mpz_sgn (const mpz_t u)
/*@
  With
    n
  Require
    store_Z(u, n)
  Ensure
    store_Z(u@pre, n) &&
    (n > 0 && __return == 1 || n == 0 && __return == 0 ||
      n < 0 && __return == -1)
*/
{
  /*@
    store_Z(u, n)
    which implies
    exists ptr cap size,
      (size < 0 && n < 0 && mpd_store_Z_compact(ptr, -n, -size, cap) ||
        size >= 0 && n >= 0 && mpd_store_Z_compact(ptr, n, size, cap)) &&
      u->_mp_size == size && 
      u->_mp_alloc == cap && 
      u->_mp_d == ptr
  */
  return gmp_cmp (u->_mp_size, 0);
}

void
mpz_swap (mpz_t u, mpz_t v)
/*@
  With
    n m
  Require
    store_Z(u, n) * store_Z(v, m)
  Ensure
    store_Z(u@pre, m) * store_Z(v@pre, n)
*/
{
  /*@
    store_Z(u, n)
    which implies
    exists ptr1 cap1 size1,
      (size1 < 0 && n < 0 && mpd_store_Z_compact(ptr1, -n, -size1, cap1) ||
        size1 >= 0 && n >= 0 && mpd_store_Z_compact(ptr1, n, size1, cap1)) &&
      u->_mp_size == size1 && 
      u->_mp_alloc == cap1 && 
      u->_mp_d == ptr1
  */
  /*@
    store_Z(v, m)
    which implies
    exists ptr2 cap2 size2,
      (size2 < 0 && m < 0 && mpd_store_Z_compact(ptr2, -m, -size2, cap2) ||
        size2 >= 0 && m >= 0 && mpd_store_Z_compact(ptr2, m, size2, cap2)) &&
      v->_mp_size == size2 && 
      v->_mp_alloc == cap2 && 
      v->_mp_d == ptr2
  */
  /*@
    Given ptr1 cap1 size1 ptr2 cap2 size2
  */
  int_swap (&u->_mp_alloc, &v->_mp_alloc);
  mp_ptr_swap(&u->_mp_d, &v->_mp_d);
  int_swap (&u->_mp_size, &v->_mp_size);
}

/* MPZ addition and subtraction */

/*static int
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
}*/

/*static int
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
}*/

/*void
mpz_add (mpz_t r, const mpz_t a, const mpz_t b)
{
  int rn;

  if ( (a->_mp_size ^ b->_mp_size) >= 0)
    rn = mpz_abs_add (r, a, b);
  else
    rn = mpz_abs_sub (r, a, b);

  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}*/

/*void
mpz_sub (mpz_t r, const mpz_t a, const mpz_t b)
{
  int rn;

  if ( (a->_mp_size ^ b->_mp_size) >= 0)
    rn = mpz_abs_sub (r, a, b);
  else
    rn = mpz_abs_add (r, a, b);

  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}*/
