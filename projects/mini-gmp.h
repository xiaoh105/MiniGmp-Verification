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

int mpn_cmp (unsigned int *, unsigned int *, int);

unsigned int mpn_add_1 (unsigned int *, unsigned int *, int, unsigned int);
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

/*@ 
  Extern Coq (Zabs: Z -> Z) 
             (Zmax: Z -> Z -> Z)
             (mpd_store_Z: Z -> Z -> Z -> Z -> Assertion)
*/