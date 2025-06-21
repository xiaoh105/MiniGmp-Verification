typedef struct
{
  int _mp_alloc;		/* Number of *limbs* allocated and pointed
				   to by the _mp_d field.  */
  int _mp_size;			/* abs(_mp_size) is the number of limbs the
				   last field points to.  If _mp_size is
				   negative this is a negative number.  */
  unsigned int *_mp_d;		/* Pointer to the limbs.  */
} __mpz_struct;

/* mpz_t is an array type that contains a single element of __mpz_struct, acting as a reference. */
typedef __mpz_struct mpz_t[1];
typedef __mpz_struct *mpz_ptr;
typedef const __mpz_struct *mpz_srcptr;

/* BEGIN Given Functions */

/* Swap functions. */
void int_swap(int x, int y);

void mp_ptr_swap(unsigned int *x, unsigned int *y);

void mpz_srcptr_swap(mpz_srcptr x, mpz_srcptr y);

/* Memory allocation functions. */
static unsigned int *
gmp_alloc_limbs (int size);

static unsigned int *
gmp_realloc_limbs (unsigned int *old, int old_size, int size);

static void
gmp_free_limbs (unsigned int *old, int size);

/* END Given Functions  */

void mpn_copyi (unsigned int *d, unsigned int *s, int n);

int mpn_cmp (unsigned int *ap, unsigned int *bp, int n);

unsigned int mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b);
unsigned int mpn_add_n (unsigned int *, unsigned int *, unsigned int *, int);
unsigned int mpn_add (unsigned int *, unsigned int *, int, unsigned int *, int);

unsigned int mpn_sub_1 (unsigned int *, unsigned int *, int, unsigned int);
unsigned int mpn_sub_n (unsigned int *, unsigned int *, unsigned int *, int);
unsigned int mpn_sub (unsigned int *, unsigned int *, int, unsigned int *, int);

void mpz_clear (mpz_t);

int mpz_sgn (const mpz_t);

void mpz_neg (mpz_t, const mpz_t);
void mpz_swap (mpz_t, mpz_t);

void mpz_add (mpz_t, const mpz_t, const mpz_t);
void mpz_sub (mpz_t, const mpz_t, const mpz_t);

void mpz_set (mpz_t, const mpz_t);

/*@ Import Coq Require Import Coq.ZArith.ZArith */
/*@ Import Coq Local Open Scope Z_scope */

/*@ 
  Extern Coq (Zabs : Z -> Z) 
             (Z::max : Z -> Z -> Z)
             (Z::pow : Z -> Z -> Z)
             (mpd_store_Z : Z -> Z -> Z -> Z -> Assertion)
             (mpd_store_Z_compact: Z -> Z -> Z -> Z -> Assertion)
             (mpd_store_list : Z -> list Z -> Z -> Assertion)
             (list_store_Z : list Z -> Z -> Prop)
             (list_store_Z_compact: list Z -> Z -> Prop)
             (last: list Z -> Z -> Z)
             (UINT_MOD: Z)
*/