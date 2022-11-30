/*
  25Jul05
  - First version as follows:
  You need to start reading it from page 266, after We shall...

  Well, also, formula in Proposition 2.6 in earlier section is important.
  What I need is the code with

  INPUT (d, q_1,...q_n) (all positive integers) with
  
  v_1,....,v_n (positive integers)
  u_1,....,u_n (positive integers)
  
  defined by
  w_i=u_i/v_i (irreducible representation for these ratios),
  and w_i=d/q_i (rational numbers)

  OUTPUT: d_1,...,d_r and \kappa of Proposition 2.6

  29Jul05
  - First release.

  01Aug05
  - In the final loop that calculates d_j the loop should be running
   j<=maxkappas, not j<maxkappas.
  - added debug flag (-d)
  - added support for reading tuples from a file

  15Aug05
  - kappa, as used in the internal d_j calculation, need not be an
  integer so the kappa not integral test has been abandoned callers
  modified accordingly.

  24Aug05
  - Overflow!  Convert to use GMP for arithmetic
  - use getopt to process command line args
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <getopt.h>
#include <gmp.h>
#include <stdarg.h>

typedef struct {
  int u;
  int v;
} rational;

static int debug;

static int gcd2(int a, int b) {
  /* Greatest common divisor of 2 POSITIVE integers. */
  int r;
  
  if (a > b){
    r = a;
    a = b;
    b = r;
  }
  
  r = b % a;
  while (r > 0){
    b = a;
    a = r;
    r = b % a;
  }
  
  return a;
}

static void gcd_m(mpz_t r, int n, mpz_t *tuple) {
  if( n==2 ) {
    mpz_gcd(r, tuple[0], tuple[1]);
   } else {
    gcd_m(r, n-1, &tuple[1]);
    mpz_gcd(r, r, tuple[0]);
  }
  return;
}

static int gcd(int n, int *tuple) {
  /* gcd of an array of POSITIVE integers. */

  if( n==2 ) return gcd2(tuple[0], tuple[1]);
  else return gcd2(tuple[0], gcd(n-1, &tuple[1]));
}

static int lcm2(int a, int b) {
  return a*b/gcd2(a,b);
}

static int lcm(int n, int *tuple) {
  /* Least common multiple of an array of integers */
  if( n==2 ) return lcm2(tuple[0], tuple[1]);
  else return lcm2(tuple[0], lcm(n-1, &tuple[1]));
}

static void reduce(rational *r) {
  /* Convert a rational to its irreducible representation. */
  int d;
  if( r->u==0 ) {
    r->u   = 0;
    r->v = 1;
  } else {
    d = gcd2(labs(r->v), labs(r->u));
    r->u   /= d;
    r->v /= d;
  }
}

static int* getint(int n) {
  void *r = calloc(n, sizeof(int));
  if( !r ) {
    printf("Could not allocate %d bytes of memory\n", sizeof(int)*n);
    exit(0);
  }
  return r;
}

static rational* getRational(int n) {
  void *r = calloc(n, sizeof(rational));
  if( !r ) {
    printf("Could not allocate %d bytes of memory\n", sizeof(rational)*n);
    exit(0);
  }
  return r;
}

static mpq_t* get_mpq(int n) {
  mpq_t *r = calloc(n, sizeof(mpq_t));
  int i;
  if( !r ) {
    printf("Could not allocate %d bytes of memory\n", sizeof(rational)*n);
    exit(0);
  }
  for(i=0; i<n; i++) mpq_init(r[i]);
  return r;
}

static void free_mpq(int n, mpq_t *p) {
  int i;
  for(i=0; i<n; i++) mpq_clear(p[i]);
  free(p);
}

static mpz_t* get_mpz(int n) {
  mpz_t *r = calloc(n, sizeof(mpz_t));
  int i;
  if( !r ) {
    printf("Could not allocate %d bytes of memory\n", sizeof(rational)*n);
    exit(0);
  }
  for(i=0; i<n; i++) mpz_init(r[i]);
  return r;
}

static void free_mpz(int n, mpz_t *p) {
  int i;
  for(i=0; i<n; i++) mpz_clear(p[i]);
  free(p);
}

static void usage(void) {
  printf("usage: poop [-dm] d q_1...q_n\n"
	 " or    poop [-dm] file\n"
	 "   -d: extra data are printed.\n"
	 "   -m: do NOT use GMP multiprecision library for arithmetic.\n");
  exit(0);
}

void printtuple(int n, int *tuple) {
  int i;
  for(i=0; i<n-1; i++) printf("%d ", tuple[i]);
  printf("%d", tuple[i]);
}

static int* makeintarray(int n, char **argv) {
  int i;
  int *r = getint(n);
  for(i=0; i<n; i++) {
    r[i] = atoi(argv[i]);
  }
  return r;
}

static rational *makeRATIONALarray(int n, int d, int *q) {
  rational *r = calloc(n, sizeof(*r));
  int i;
  if( !r ) {
    printf("Could not allocate %d bytes of memory\n", sizeof(*r)*n);
    exit(0);
  }
  for(i=0; i<n; i++) {
    r[i].u   = d;
    r[i].v = q[i];
    reduce(&r[i]);
  }
  return r;
}

static void makeRATIONALarray_m(mpq_t *r, int n, int d, int *q) {
  int i;
  for(i=0; i<n; i++) {
    mpq_set_si(r[i], d, q[i]);
    mpq_canonicalize(r[i]);
  }
  return;
}

static void addRational(rational *r1, rational *r2) {
  /* add 2 rationals and return the result in r1 */
  r1->u = r1->u*r2->v + r1->v*r2->u;
  r1->v = r1->v*r2->v;
  reduce(r1);
}

static void multiplyRational(rational *r1, rational *r2) {
  /* multiply 2 rationals and return the result in r1 */
  r1->u   *= r2->u;
  r1->v *= r2->v;
  reduce(r1);
}

static char *printRational(rational *r) {
  static char buf[5][1000];
  char *rb;
  static int b;
  rb = buf[b];
  if( r->v==1 )
    snprintf(rb, 1000, "%d", r->u);
  else
    snprintf(rb, 1000, "%d/%d", r->u, r->v);
  if( ++b==5 ) b = 0;
  return rb;
}

static char * printBinary(int width, int value) {
  static char buf[5][33];
  static int bi;
  char *rb;
  int i;
  buf[bi][32] = '\0';
  for(i=31; i>31-width; i--) {
    if( value%2 )
      buf[bi][i] = '1';
    else
      buf[bi][i] = '0';
    value >>= 1;
  }
  rb = &buf[bi][++i];
  if( ++bi==5 ) bi = 0;
  return rb;
}

static rational * kappa(int n, rational *w) {
  rational *kappa = getRational(1);
  rational work;
  int i, s;
  int indx, jndx, runninglcm;

  for(i=0, indx=1; i<n; i++) indx *= 2;

  kappa->u = 0; kappa->v = 1;
  while( indx-- ) { /* Subset loop */
    jndx = indx;
    runninglcm = 1;
    s=0;
    work.u = 1; work.v = 1;
    
    for(i=0;i<n;i++) {
      if( jndx%2 ) {
	multiplyRational(&work, &w[i]);
	runninglcm = lcm2(runninglcm, w[i].u);
	s++;
      }
      jndx >>= 1;
    }
    
    work.v *= runninglcm;
    if( (n-s)%2 ) work.u *= -1;
    addRational(kappa, &work);
  }

  return kappa;
}

static void kappa_m(mpq_t kappa, int n, mpq_t *w) {
  mpq_t work;
  int i, s;
  unsigned int indx, jndx;
  mpz_t runninglcm;

  mpq_init(work);
  mpz_init(runninglcm);
  
  for(i=0, indx=1; i<n; i++) indx *= 2;

  mpq_set_si(kappa, 0, 1);
  while( indx-- ) { /* Subset loop */
    jndx = indx;
    mpz_set_si(runninglcm, 1);
    s=0;
    mpq_set_si(work, 1, 1);
    
    for(i=0;i<n;i++) {
      if( jndx%2 ) {
	mpq_mul(work, work, w[i]);
	mpz_lcm(runninglcm, runninglcm, mpq_numref(w[i]));
	s++;
      }
      jndx >>= 1;
    }
    
    mpz_mul(mpq_denref(work), mpq_denref(work), runninglcm);
    if( (n-s)%2 ) mpq_neg(work, work);
    mpq_canonicalize(work);
    mpq_add(kappa, kappa, work);
  }

  mpq_clear(work);
  mpz_clear(runninglcm);
  
  return;
}

static int cntbits(int i) {
  int rc=0;
  while(i) {
    rc += i%2;
    i >>= 1;
  }
  return rc;
}

static int cmpindx(const void *i1, const void *i2) {
  int j1 = cntbits(*(int*)i1);
  int j2 = cntbits(*(int*)i2);
  if( j1<j2 ) return -1;
  if( j1>j2 ) return  1;
  return 0;
}

static int *maskarray; // This is also used in Djs

static int* Cs(int n, rational *w) {
  int indx, *maskarraymap;
  int i, j, gcdwork;
  int *C, *u, p;

  u = getint(n);
  for(i=0; i<n; i++) u[i] = w[i].u;
  
  for(i=0, indx=1; i<n; i++) indx *= 2;
  
  C = getint(indx);

  /* maskarray is an array of bitmaps specifying the subsets
     ordered by the cardinality of the subset. maskarraymap
     is a lil'ol map to tell us where the start of each
     new cardinality is. */
  maskarray = getint(indx);
  maskarraymap = getint(n+2);
  for(i=0; i<indx; i++) maskarray[i] = i;
  qsort(maskarray, indx, sizeof(*maskarray), cmpindx);
  for(i=0, j=0; i<indx; i++)
    if( j==cntbits(maskarray[i]) ) maskarraymap[j++] = i;
  maskarraymap[j] = n;
  
  
  /* loop subsets, in ascending order of cardinality */
  C[0] = gcd(n, u); /* empty set, initialising case */
  if( debug )
    printf("C_%s=%d/%d\n", printBinary(n,0), C[0], 1);
  for(i=1; i<indx; i++) {
    int mask = maskarray[i];
    int b = cntbits(mask);
    int ii;

    /* The product calculation for the demoninator */
    p = 1;
    for(j=0; j<maskarraymap[b]; j++) {
      int submask = maskarray[j];
      /* all bits in the subset mask must also be in set mask */
      int subset = cntbits(mask&submask)==cntbits(submask);
      if( subset )
	p *= C[j];
    }

    /* The GCD calculation */
    gcdwork = 0;
    ii = mask;
    for(j=0; j<n; j++) {
      if( ii%2==0 ) {
	if( gcdwork )
	  gcdwork = gcd2(gcdwork, u[j]);
	else
	  gcdwork = u[j];
      }
      ii >>= 1;
    }
    /* What is the GCD of an empty tuple??? */
    if( !gcdwork ) gcdwork = 1;

    if( debug )
      printf("C_%s=%d/%d\n", printBinary(n,mask), gcdwork, p);
    fflush(stdout);
    C[i] = gcdwork/p;
  }

  free(maskarraymap);
  free(u);
  
  return C;
}

static void Cs_m(mpz_t **C, int n, mpq_t *w) {
  int indx, *maskarraymap;
  int i, j;
  mpz_t *u, p, gcdwork;

  mpz_init(p);
  mpz_init(gcdwork);
  u = get_mpz(n);
  for(i=0; i<n; i++)  mpz_set(u[i], mpq_numref(w[i]));
  
  for(i=0, indx=1; i<n; i++) indx *= 2;
  
  *C = get_mpz(indx);

  /* maskarray is an array of bitmaps specifying the subsets
     ordered by the cardinality of the subset. maskarraymap
     is a lil'ol map to tell us where the start of each
     new cardinality is. */
  maskarray = getint(indx);
  maskarraymap = getint(n+2);
  for(i=0; i<indx; i++) maskarray[i] = i;
  qsort(maskarray, indx, sizeof(*maskarray), cmpindx);
  for(i=0, j=0; i<indx; i++)
    if( j==cntbits(maskarray[i]) ) maskarraymap[j++] = i;
  maskarraymap[j] = n;
  
  
  /* loop subsets, in ascending order of cardinality */
  gcd_m((*C)[0], n, u); /* empty set, initialising case */
  if( debug )
    gmp_printf("C_%s=%Zd/%d\n", printBinary(n,0), C[0], 1);
  for(i=1; i<indx; i++) {
    int mask = maskarray[i];
    int b = cntbits(mask);
    int ii;

    /* The product calculation for the demoninator */
    mpz_set_si(p, 1);
    for(j=0; j<maskarraymap[b]; j++) {
      int submask = maskarray[j];
      /* all bits in the subset mask must also be in set mask */
      int subset = cntbits(mask&submask)==cntbits(submask);
      if( subset )
	mpz_mul(p, p, (*C)[j]);
    }

    /* The GCD calculation */
    mpz_set_si(gcdwork, 0);
    ii = mask;
    for(j=0; j<n; j++) {
      if( ii%2==0 ) {
	if( mpz_sgn(gcdwork)!=0 )
	  mpz_gcd(gcdwork, gcdwork, u[j]);
	else
	  mpz_set(gcdwork, u[j]);
      }
      ii >>= 1;
    }
    /* What is the GCD of an empty tuple??? */
    if( mpz_sgn(gcdwork)==0 ) mpz_set_si(gcdwork, 1);

    if( debug )
      gmp_printf("C_%s=%Zd/%Zd\n", printBinary(n,mask), gcdwork, p);
    fflush(stdout);
    mpz_div((*C)[i], gcdwork, p);
  }

  free(maskarraymap);
  free_mpz(n, u);
  mpz_clear(p);
  mpz_clear(gcdwork);
  
  return;
}

#define max(a,b) (a)>(b)?(a):(b)

static int *Djs(int n, int *C, rational *uv) {
  /* Calculate the d_j from the Cs */
  int i, j, k, indx, mask;
  int *kappas, maxkappas, *d_j;
  rational *subuv = getRational(n);
  rational *kwork;

  if( !subuv ) {
    printf("Could not allocate %d bytes of memory\n", n*sizeof(*subuv));
    exit(0);
  }

  for(i=0, indx=1; i<n; i++) indx *= 2;
  kappas = getint(indx*sizeof(*kappas));

  maxkappas = 0;
  for(i=0; i<indx; i++) {
    mask = i;
    j = k = 0;
    while(mask) {
      if( mask%2 ) {
	subuv[j].u = uv[k].u;
	subuv[j].v = uv[k].v;
	j++;
      }
      k++;
      mask >>= 1;
    }

    if( (n-j)%2 ) {
      kwork = kappa(j, subuv);
      kappas[i] = kwork->u/kwork->v;
      free(kwork);
    } else
      kappas[i] = 0;
    maxkappas = max(maxkappas, kappas[i]);
    if( debug )
      printf("kappas[%d]=%d(%s) j=%d\n",
	     i, kappas[i], printBinary(n,i), j);
  }

  d_j = getint(maxkappas+1);
  for(j=0; j<=maxkappas; j++) {
    d_j[j] = 0;
    for(i=0; i<indx; i++) {
      if( kappas[i]>=j ) {
	/* Find the right entry in C */
	k = 0; while( maskarray[k++]!=i ); k--;
	if( k>indx ) {
	  printf("Logic error calculating d_j\n");
	  exit(0);
	}

	/* Grab the entry from C and update d_j */
	if( d_j[j] ) d_j[j] *= C[k];
	else d_j[j] = C[k];
      }
    }
    if( d_j[j] ) printf("d_%d=%d\n", j, d_j[j]);
  }

  free(kappas);
  return d_j;
	
  
}

static void Djs_m(mpz_t *d_j, int n, mpz_t **C, mpq_t *uv) {
  /* Calculate the d_j from the Cs */
  int i, j, k, indx, mask;
  mpz_t *kappas;
  int maxkappas;
  mpq_t *subuv = get_mpq(n);
  mpq_t kwork;

  mpq_init(kwork);

  for(i=0, indx=1; i<n; i++) indx *= 2;
  kappas = get_mpz(indx);

  maxkappas = 0;
  for(i=0; i<indx; i++) {
    mask = i;
    j = k = 0;
    while(mask) {
      if( mask%2 ) {
	mpq_set(subuv[j], uv[k]);
	j++;
      }
      k++;
      mask >>= 1;
    }

    if( (n-j)%2 ) {
      kappa_m(kwork, j, subuv);
      mpz_fdiv_q(kappas[i], mpq_numref(kwork), mpq_denref(kwork));
    } else
      mpz_set_si(kappas[i], 0);
    maxkappas = max(maxkappas, mpz_get_ui(kappas[i]));
    if( debug )
      gmp_printf("kappas[%d]=%Zd(%s) j=%d\n",
		 i, kappas[i], printBinary(n,i), j);
  }

  d_j = get_mpz(maxkappas+1);
  for(j=0; j<=maxkappas; j++) {
    for(i=0; i<indx; i++) {
      if( mpz_get_ui(kappas[i])>=j ) {
	/* Find the right entry in C */
	k = 0; while( maskarray[k++]!=i ); k--;
	if( k>indx ) {
	  printf("Logic error calculating d_j\n");
	  exit(0);
	}

	/* Grab the entry from C and update d_j */
	if( mpz_sgn(d_j[j])!=0 ) mpz_mul(d_j[j], d_j[j], (*C)[k]);
	else  mpz_set(d_j[j], (*C)[k]);
      }
    }
    if( mpz_sgn(d_j[j])!=0 ) gmp_printf("d_%d=%Zd\n", j, d_j[j]);
  }

  mpq_clear(kwork);
  free_mpz(indx, kappas);
  
  return;  
}

static int getnexttuple(FILE *f, int *n, int *d, int **w) {
  int bp;
  char buf[1000];
  static int win[1000];

 restart:
  if( !fgets(buf, 1000, f) ) return 0;
  if( strlen(buf) == 1000-1 ) {
    printf("Line too long in file\n");
    exit(0);
  }

  bp = 0;
  while( ('0'>buf[bp] || buf[bp]>'9') && buf[bp]!=0 ) bp++;
  if( buf[bp]==0 )
    goto restart; /* empty line */
  
  sscanf(&buf[bp], "%d", d);
  while( '0'<=buf[bp] && buf[bp]<='9' ) bp++;
  
  *n = 0;
  *w = win;
  while( buf[bp] ) {
    while( ('0'>buf[bp] || buf[bp]>'9') && buf[bp]!=0 ) bp++;
    if( buf[bp]==0 ) break;
    sscanf(&buf[bp], "%d", &win[*n]);
    while( '0'<=buf[bp] && buf[bp]<='9' ) bp++;
    (*n)++;
  }

  return 1;  
}


int main(int argc, char **argv) {
  int d, *w, *C, *dj;
  rational *k, *uv;
  mpq_t k_m, *uv_m;
  mpz_t *C_m, *dj_m;
  int n;
  FILE *f;
  int c=0;
  int single_precision = 0;
  extern int optind;

  do {
    c = getopt(argc, argv, "dm");

    switch(c) {
    case 'd':
      debug = 1;
      break;

    case 'm':
      single_precision = 1;
      break;

    case -1:
      break;

    default:
      usage();
      break;
    }
  } while(c >= 0);

  if( !single_precision ) {
    mpq_init(k_m);
  }

  if( argc-optind > 2 ) {
    /* Arguments are on the command line */
    n = argc-optind-1;

    d = atoi(argv[optind]);
    w = makeintarray(n, &argv[optind+1]);

    if( single_precision ) {
      uv = makeRATIONALarray(n, d, w);
      k  = kappa(n, uv);
      printf("kappa=%s\n", printRational(k));
      C  = Cs(n, uv);
      dj = Djs(n, C, uv);
      free(k);
    } else {
      uv_m = get_mpq(n);
      makeRATIONALarray_m(uv_m, n, d, w);
      kappa_m(k_m, n, uv_m);
      gmp_printf("kappa=%Qd\n", k_m);
      Cs_m(&C_m, n, uv_m);
      Djs_m(dj_m, n, &C_m, uv_m);
    }

    return 0;
  }

  /* Read a file */
  f = fopen(argv[optind], "r");
  if( !f ) {
    printf("Your file couldn't be opened, could it.\n");
    return 0;
  }

  while( getnexttuple(f, &n, &d, &w) ) {
    if( single_precision ) {
      uv = makeRATIONALarray(n, d, w);
      k  = kappa(n, uv);
      printf("kappa=%s\n", printRational(k));
      free(k);
      C  = Cs(n, uv);
      dj = Djs(n, C, uv);
    } else {
      uv_m = get_mpq(n);
      makeRATIONALarray_m(uv_m, n, d, w);
      kappa_m(k_m, n, uv_m);
      gmp_printf("kappa=%Qd\n", k_m);
      Cs_m(&C_m, n, uv_m);
      Djs_m(dj_m, n, &C_m, uv_m);
      free_mpq(n, uv_m);
    }

  }
    
  
  return 0;
}
