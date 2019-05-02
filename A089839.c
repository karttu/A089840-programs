/*****************************************************************************/
/* http://www.research.att.com/~njas/sequences/a089839.c.txt                 */
/*                                                                           */
/* a089839.c -- A lean and fast C-program to count empirically the amount of */
/*              distinct non-recursive Catalan automorphisms.                */
/*                                                                           */
/* See the entries A089831-A089843 in Neil Sloane's Online-Encyclopedia      */
/* of Integer Sequences at: http://www.research.att.com/~njas/sequences/     */
/*                                                                           */
/* Coded 2003 by Antti Karttunen, http://www.iki.fi/kartturi/                */
/* and placed in Public Domain.                                              */
/* First edited  7. Nov 2003.                                                */
/* Edited  11. Oct 2006. (Sequences in A123XXX range).                       */
/* Edited  22. May 2007. (Sequences A129604-A129612.)                        */
/* Last edited 05 Jan 2009 (Sequences A153826-A153834 & A154121-A154126)     */
/*                                                                           */
/* Mirrored at:                                                              */
/* http://www.iki.fi/kartturi/matikka/Nekomorphisms/a089839.c                */
/*                                                                           */
/* The idea of program in short:                                             */
/* In principle (*), iterate over all partial_sums(A089836) compositions     */
/* of binary tree "transformation clauses", and examine which ones           */
/* give bijections which are not encountered before. Count them,             */
/* and give the results as table A089831, etc.                               */
/*                                                                           */
/* (* in practice we can do some obvious filtering, see the functions        */
/* clause_seq_next_composition and clause_seq_next)                          */
/*                                                                           */
/* For the essence of the fast implementation, see the functions             */
/* apply_clauses_to_x  and select_vectors_needed                             */
/*                                                                           */
/* To get correct results (and to avoid crashing!), the command line         */
/* parameters must be large enough:                                          */
/* Both a089839 127 8 19394489  and a089839 127 9 15485863                   */
/* produce the results that are submitted to OEIS as of 5 Dec 2003.          */
/*                                                                           */
/* Note: This program is growing too complex, with all the low level memory  */
/* allocation, hash table lookups, tricky optimizations, and so on.          */
/* Currently we are in a vicious circle: this program practically defines    */
/* how the table A089840 and many of the associated sequences are formed,    */
/* against which the correctness of this program should be checked!          */
/* (However, see the comments before the function increment_clause.)         */
/*                                                                           */
/* We need to write a separate, clean, non-optimized implementation in some  */
/* higher level language (Prolog, Scheme, Haskell?), that might be very      */
/* slow, but at least it would be easier to reckon that the program returns  */
/* intended results. The said program could generate all the nonrecursive    */
/* automorphisms, say, from A089840[0] to A089840[1786785] and store them to */
/* a separate file/database in some accessible format                        */
/* (e.g. as CLAUSESEQ's/Prolog-rules's and possibly also automatically       */
/* construed/optimized Scheme-functions) and the program together with its   */
/* output would then serve as a frozen reference against which the output    */
/* of this program (and its future improved versions) could be compared to.  */
/*                                                                           */
/* Also, we need a formal proof about what is the minimum size of binary     */
/* trees which need to be checked up to, before the equivalence of two       */
/* nonrecursive automorphisms with similarly beginning signature             */
/* permutations can be rigorously decided. (And to detect which clause       */
/* sequences are not bijections.)                                            */
/* However, intuitively it seems that it is enough to choose the size where  */
/* no further differences in output (e.g. the number of distinct bijections  */
/* found) occur. Thus it is certainly a positive sign that the two command   */
/* examples above (with size given as 8 and 9) produce the same results,     */
/* for the max. 7 node clause sequences.                                     */
/*                                                                           */
/* See also http://www.research.att.com/~njas/sequences/A089840p.txt         */
/* See also http://www.research.att.com/~njas/sequences/a089408.c.txt        */
/*                                                                           */
/* If you have any suggestions or questions, you can mail them to me         */
/* to my address <My firstname>.<My surname>@gmail.com                       */
/*                                                                           */
/* Cheers, Antti Karttunen                                                   */
/*                                                                           */
/*****************************************************************************/


#include "stdio.h"
#include "stdlib.h"
#include "string.h"

#define MAX_CLAUSES 20
#define MAX_CLAUSE_SIZE 20

/* With our 64 bits MAXSIZE is 31, with 32 bit machines it's only 15.
   (because we need one extra bit for the last leaf of binary trees) */

#ifdef ONLY32BITS
#define MAXSIZE 21
#define MAXSIZE_FOR_TBBS 15
#else
#define MAXSIZE 31
#define MAXSIZE_FOR_TBBS 31
#endif

typedef unsigned char BYTE;
typedef unsigned long int ULI;
typedef unsigned short int USI;

#define FILLED_BYTE ((BYTE)((~((BYTE) 0))))

#ifdef REQUIRES_LONG_LONG

typedef unsigned long long int ULLI; /* Two longs on 64-bit Suns */
typedef long long int SLLI;          /* Ditto. */

#else /* We are running on Alpha, or maybe some small 32-bit machine. */

typedef unsigned long int ULLI; /* Only one long on DEC Alpha's */
typedef long int SLLI;          /* Ditto. */
#endif

typedef ULLI TBBS; /* TBBS = totally balanced binary sequence. With 32 bits only upto size n=15, with 64 upto n=31. */
typedef SLLI RANK; /* With 32 bits we can go upto size n=19, with 64 much further. */
typedef int SIZE;

typedef USI SGRANK; /* 2 bytes for "Short Global Ranks", i.e. valid up to size n=10. */
typedef USI SLRANK; /* 2 bytes for "Short Local Ranks", i.e. valid up to size n=11. */
typedef ULI PERMRANK; /* 4 bytes for permutation ranks, valid upto size n=11, i.e. 12 leaves. */
typedef ULI NORERANK; /* Ditto for the rank of distinct bijections in A089840. */
 
typedef BYTE SSIZE; /* One byte for short size. */

typedef ULLI LRANK; /* Local RANK, semantically different from a global rank. */

#define MAX_COMPUTATION_SIZE 10
#define MAX_BINEXP 255 /* I.e. only up to clause sequences of the total size=8. */


#define add_to_checksum(OLDCHKSUM,Y) ((31*(OLDCHKSUM))+(Y))

/**********************************************************************/

int globopt_output_cycle_lists = 0;
char *globopt_list_begin = "(";
char *globopt_list_delim = "";
char *globopt_list_end   = ")\n";
char *globopt_elem_delim = ",";
char *globopt_pair_begin = "(";
char *globopt_pair_delim = " ";
char *globopt_pair_end   = ")";
char *globopt_comment_begin = ";;";
int globopt_output_invariance_indices = 0;
int globopt_compute_A153830 = 0;

FILE *fpA153826 = NULL, *fpA153827 = NULL, *fpA153828 = NULL,
     *fpA153829 = NULL, *fpA153830 = NULL, *fpA153831 = NULL;


int globopt_HTML = 0;

char *glob_author_info = "Antti Karttunen (His_Firstname.His_Surname(AT)gmail.com)";
char *glob_datestr = "Mon DD 20YY"; /* E.g. , Oct 28 2003 */

/************************************************************************/
/*                                                                      */
/* Added 14. Oct 2003: SEXP-structure (a simple planar binary tree)     */
/* because most of the Catalan automorphisms are easier to define in    */
/* such Lisp-like terms, than to work directly on the binary sequences. */
/*                                                                      */
/************************************************************************/

struct s_exp
 {
     struct s_exp *s_car; /* I.e. the left branch of the binary tree. */
     struct s_exp *s_cdr; /* I.e. the right branch of the ---- "" ---- */
 };

typedef struct s_exp SEXP_cell;
typedef SEXP_cell *SEXP;

#define NULLP(s) ((s) == NULL)
#define PAIR(s) (!NULLP(s))
#define CAR(s) ((s)->s_car)
#define CDR(s) ((s)->s_cdr)

#define SET_CAR(s,x) (((s)->s_car) = x)
#define SET_CDR(s,x) (((s)->s_cdr) = x)

long int glob_cons_cells_in_use = 0; /* For detecting possible leaks. */

SEXP cons(SEXP carside,SEXP cdrside)
{
    SEXP newcell = ((SEXP) calloc(1,sizeof(SEXP_cell)));

    if(NULL == newcell)
     {
       fprintf(stderr,
       "cons: Couldn't allocate a chunk of %u bytes to store one cons cell!\n",
                      sizeof(SEXP_cell));
       exit(1);
     }

/*  fflush(stdout); fprintf(stderr,"cons called!\n"); fflush(stderr); */

    glob_cons_cells_in_use++;

    SET_CAR(newcell,carside);
    SET_CDR(newcell,cdrside);
    return(newcell);
}



/* Taking plunge on car-side, find the first cons-cell
   with either its CAR or CDR-side NULL,
   and return that cell as a result,
   to be reused by recons
 */
SEXP degraft(SEXP *subroot)
{
    SEXP z;

    if(NULLP(CAR(*subroot)))
     {
       z = *subroot;
       *subroot = CDR(z);
       return(z);
     }

    if(NULLP(CDR(*subroot)))
     {
       z = *subroot;
       *subroot = CAR(z);
       return(z);
     }

    return(degraft(&(CAR(*subroot))));
}

/* Here an all-out (not incremental like here!) deconstruction of
   the previous S-expression  to a separate free-list
   (which just means flattening it!)
   might be faster on larger S-expressions:
 */
SEXP recons(SEXP carside,SEXP cdrside,SEXP *reused)
{
    if((NULL == reused) || NULLP(*reused))
     { return(cons(carside,cdrside)); }
    else
     {
       SEXP z = degraft(reused);
       SET_CAR(z,carside);
       SET_CDR(z,cdrside);
       return(z);
     }
}

/* Recursively free the tree allocated with cons. */
void free_cons_tree(SEXP node)
{
    if(NULLP(node)) { return; }

    if(!NULLP(CAR(node))) { free_cons_tree(CAR(node)); }
    if(!NULLP(CDR(node))) { free_cons_tree(CDR(node)); }
    free(node);
    glob_cons_cells_in_use--;

}

/* Recursively free the list allocated with cons, up to the upto_n:th node. */
void free_cons_list(SEXP node,int upto_n)
{
    int i;
    SEXP next_cdr;

    for(i=0; i < upto_n; i++)
     {
       if(!PAIR(node))
        {
          fprintf(stderr,
              "free_cons_list: Fatal error: the list to be freed is only %u elems long, shorter than expected %u.\n",
               i,upto_n);
          exit(1);
        }

       next_cdr = CDR(node);
       free(node);
       glob_cons_cells_in_use--;
       node = next_cdr;
     }
}


/* Taking first plunge on the cdr-side before car-side,
   count all leaves (NULL's), incrementing *leafpos each time,
   and when *leafpos is zero, insert a new cons(NULL,NULL) node
   at that leaf, and return 1.

   (We could use setjmp, longjmp, but now I'm too lazy.)
 */
int graft_scion_aux(SEXP s,SEXP scion,int *leafpos)
{
    SEXP z;

    if(NULLP(CDR(s)))
     {
       if(0 == *leafpos) { SET_CDR(s,scion); return(1); }
       --*leafpos;
     }
    else
     {
       if(1 == graft_scion_aux(CDR(s),scion,leafpos)) { return(1); }
     }

    if(NULLP(CAR(s)))
     {
       if(0 == *leafpos) { SET_CAR(s,scion); return(1); }
       --*leafpos;
     }
    else
     {
       if(1 == graft_scion_aux(CAR(s),scion,leafpos)) { return(1); }
     }

    return(0); /* No change made yet. */
}


/* See A153250. */

int graft_bud_at(SEXP s,int leafpos)
{
     SEXP bud = cons(NULL,NULL);

     return(graft_scion_aux(s,bud,&leafpos));
}

/* Returns 1 if the bintree t1 is wholly containd in bintree t2,
   otherwise zero.
   See A082858 */
int sexp_is_subtree(SEXP t1,SEXP t2)
{
    if(NULLP(t1)) { return(1); } /* t1 finished, succeeding at this branch. */

    if(NULLP(t2)) { return(0); } /* t2 finished, although t1 not, fail. */

    if(0 == sexp_is_subtree(CAR(t1),CAR(t2))) /* If left hand side of t1 is */
     { return(0); } /* not subtree of left side of t2 then fail immediately. */
    else  /* Check also the right hand side. */
     { return(sexp_is_subtree(CDR(t1),CDR(t2))); }
  }


/**********************************************************************/


/* Better to pass this by reference... */

struct evaluation_context
 {
   int upto_size_n;
   int vec_size;
   int bijectivity_broken_at_size_n;
   int clear_next_time_upto_size_n;
   ULLI checksum;
   SGRANK *vals_obtained;
   SGRANK *vals_obtained2; /* When we need compositions. */
   USI **all_vecs[(2*MAX_CLAUSE_SIZE)+2];
   USI **bud_vecs;
   USI **subtree_bitvecs;
 };

typedef struct evaluation_context ECOTEX;

/**********************************************************************/

#define LONG_ONE ((ULLI) 1)

#define two_to(n) (LONG_ONE << (n))

#define A000217(n) (((n)*(n+1))>>1)

#define tr2seqind(n,m) (A000217(n)+m)
#define tr2seqind11(n,m) tr2seqind(n-1,m-1)

/* tr2seqind(0,0) -> 0
   tr2seqind(1,0) -> 1
   tr2seqind(1,1) -> 2
   tr2seqind(2,0) -> 3
   tr2seqind(2,1) -> 4
   tr2seqind(2,2) -> 5
   tr2seqind(3,0) -> 6
  etc.
 */

#define ar2seqind(row,col) (((row+col)*(row+col) + (3*row) + col)>>1)
/* ar2seqind(0,0) -> 0
   ar2seqind(0,1) -> 1
   ar2seqind(1,0) -> 2
   ar2seqind(0,2) -> 3
   ar2seqind(1,1) -> 4
   ar2seqind(2,0) -> 5
   ar2seqind(0,3) -> 6
  etc.
 */


int binwidth(int n)
{
    int i=0;
    while(n != 0) { n >>= 1; i++; }
    return(i);
}

/**********************************************************************/

/* Bit-operators copied from a089408.c.txt */

#define kth_byte(n) ((int) ((n) >> 3)) /* From RANK to int */
#define kth_bit(n)  (((RANK)(n)) << 3) /* From int to RANK */
#define ith_bit_in_byte(n) ((BYTE) (1 << ((n) & 7))) /* From RANK to BYTE */

#define toggle_bit_on(B,n) (B[kth_byte(n)] |= ith_bit_in_byte(n))
#define toggle_bit_off(B,n) (B[kth_byte(n)] &= ~ith_bit_in_byte(n))

#define bit_is_zero(B,n) (0 == (B[kth_byte(n)] & ith_bit_in_byte(n)))

#define index2t(tsize,rank_s,rank_l) ((Cat(tsize+1)*rank_s)+(rank_l))

/**********************************************************************/


PERMRANK sA000142[13] = { 1,1,2,6,24,120,720,5040,40320,362880,3628800,39916800,479001600 };

#define A000142(n) (sA000142[n])

#ifdef ONLY32BITS
#define SS 20
#else
#define SS 33
#endif

RANK sA00108[SS] = {1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786,
                    208012, 742900, 2674440, 9694845, 35357670, 129644790,
                    477638700, 1767263190 /* The last value < 2^32 at n=19 */
#ifndef ONLY32BITS
                    ,6564120420, 24466267020, 91482563640, 343059613650,
                    1289904147324, 4861946401452, 18367353072152,
                    69533550916004, 263747951750360, 1002242216651368,
                    3814986502092304, 14544636039226909, 55534064877048198
#endif
                   };

#define A000108(n) (sA00108[n])
#define Cat(n) (sA00108[n])
#define A001246(n) (Cat(n)*Cat(n))

/* The last value < 2^32 at n=19 */
RANK sA014137[SS] = {1, 2, 4, 9, 23, 65, 197, 626, 2056, 6918, 23714, 82500,
                     290512, 1033412, 3707852, 13402697, 48760367, 178405157,
                     656043857, ((RANK)2423307047)
#ifndef ONLY32BITS
                     ,8987427467, 33453694487, 124936258127, 467995871777,
                     1757900019101, 6619846420553, 24987199492705,
                     94520750408709, 358268702159069, 1360510918810437,
                     5175497420902741, 19720133460129650, 75254198337177848
#endif
                    };

#define A014137(n) (sA014137[n])

#define global2local_rank(grank,size) ((grank)-A014137(size-1))

/* Note: both rows and columns start from -1 */

/* Entry at CatTriangle(r,m) = CatTriangle(r,m-1) + CatTriangle(r-1,m) */

#define CatTriangle(r,c) (tA009766[(r+2)][(c+1)])

#ifdef ONLY32BITS
#define TR 21
#else
#define TR 34
#endif

RANK tA009766[][TR+1] =  /* 34 rows in full version. */
 {
  {0},
  {0, 0},
  {0, 1, 0}, 
  {0, 1, 1, 0}, 
  {0, 1, 2, 2, 0}, 
  {0, 1, 3, 5, 5, 0},
  {0, 1, 4, 9, 14, 14, 0}, 
  {0, 1, 5, 14, 28, 42, 42, 0},    
  {0, 1, 6, 20, 48, 90, 132, 132, 0},
  {0, 1, 7, 27, 75, 165, 297, 429, 429, 0},    
  {0, 1, 8, 35, 110, 275, 572, 1001, 1430, 1430, 0},
  {0, 1, 9, 44, 154, 429, 1001, 2002, 3432, 4862, 4862, 0},    
  {0, 1, 10, 54, 208, 637, 1638, 3640, 7072, 11934, 16796, 16796, 0},
  {0, 1, 11, 65, 273, 910, 2548, 6188, 13260, 25194, 41990, 58786, 58786, 0},
  {0, 1, 12, 77, 350, 1260, 3808, 9996, 23256, 48450, 90440, 149226, 208012,
    208012, 0}, 
  {0, 1, 13, 90, 440, 1700, 5508, 15504, 38760, 87210, 177650, 326876, 534888,
    742900, 742900, 0}, 
  {0, 1, 14, 104, 544, 2244, 7752, 23256, 62016, 149226, 326876, 653752,
    1188640, 1931540, 2674440, 2674440, 0}, 
  {0, 1, 15, 119, 663, 2907, 10659, 33915, 95931, 245157, 572033, 1225785,
    2414425, 4345965, 7020405, 9694845, 9694845, 0}, 
  {0, 1, 16, 135, 798, 3705, 14364, 48279, 144210, 389367, 961400, 2187185,
    4601610, 8947575, 15967980, 25662825, 35357670, 35357670, 0}, 
  {0, 1, 17, 152, 950, 4655, 19019, 67298, 211508, 600875, 1562275, 3749460,
    8351070, 17298645, 33266625, 58929450, 94287120, 129644790, 129644790, 0}, 
  {0, 1, 18, 170, 1120, 5775, 24794, 92092, 303600, 904475, 2466750, 6216210,
    14567280, 31865925, 65132550, 124062000, 218349120, 347993910, 477638700,
    477638700, 0}, 
  {0, 1, 19, 189, 1309, 7084, 31878, 123970, 427570, 1332045, 3798795,
    10015005, 24582285, 56448210, 121580760, 245642760, 463991880, 811985790,
    1289624490, 1767263190, 1767263190, 0}
#ifndef ONLY32BITS
/* Then follows the first row with a value > 4294967295. */
  ,{0, 1, 20, 209, 1518, 8602, 40480, 164450, 592020, 1924065, 5722860,
    15737865, 40320150, 96768360, 218349120, 463991880, 927983760, 1739969550,
    3029594040, 4796857230, 6564120420, 6564120420, 0},
  {0, 1, 21, 230, 1748, 10350, 50830, 215280, 807300, 2731365, 8454225,
    24192090, 64512240, 161280600, 379629720, 843621600, 1771605360,
    3511574910, 6541168950, 11338026180, 17902146600, 24466267020,
    24466267020, 0}, 
  {0, 1, 22, 252, 2000, 12350, 63180, 278460, 1085760, 3817125, 12271350,
    36463440, 100975680, 262256280, 641886000, 1485507600, 3257112960,
    6768687870, 13309856820, 24647883000, 42550029600, 67016296620,
    91482563640, 91482563640, 0}, 
  {0, 1, 23, 275, 2275, 14625, 77805, 356265, 1442025, 5259150, 17530500,
    53993940, 154969620, 417225900, 1059111900, 2544619500, 5801732460,
    12570420330, 25880277150, 50528160150, 93078189750, 160094486370,
    251577050010, 343059613650, 343059613650, 0}, 
  {0, 1, 24, 299, 2574, 17199, 95004, 451269, 1893294, 7152444, 24682944,
    78676884, 233646504, 650872404, 1709984304, 4254603804, 10056336264,
    22626756594, 48507033744, 99035193894, 192113383644, 352207870014,
    603784920024, 946844533674, 1289904147324, 1289904147324, 0}, 
  {0, 1, 25, 324, 2898, 20097, 115101, 566370, 2459664, 9612108, 34295052,
    112971936, 346618440, 997490844, 2707475148, 6962078952, 17018415216,
    39645171810, 88152205554, 187187399448, 379300783092, 731508653106,
    1335293573130, 2282138106804, 3572042254128, 4861946401452,
    4861946401452, 0},
  {0, 1, 26, 350, 3248, 23345, 138446, 704816, 3164480, 12776588, 47071640,
    160043576, 506662016, 1504152860, 4211628008, 11173706960, 28192122176,
    67837293986, 155989499540, 343176898988, 722477682080, 1453986335186,
    2789279908316, 5071418015120, 8643460269248, 13505406670700,
    18367353072152, 18367353072152, 0}, 
  {0, 1, 27, 377, 3625, 26970, 165416, 870232, 4034712, 16811300, 63882940,
    223926516, 730588532, 2234741392, 6446369400, 17620076360, 45812198536,
    113649492522, 269638992062, 612815891050, 1335293573130, 2789279908316,
    5578559816632, 10649977831752, 19293438101000, 32798844771700,
    51166197843852, 69533550916004, 69533550916004, 0}, 
  {0, 1, 28, 405, 4030, 31000, 196416, 1066648, 5101360, 21912660, 85795600,
    309722116, 1040310648, 3275052040, 9721421440, 27341497800, 73153696336,
    186803188858, 456442180920, 1069258071970, 2404551645100, 5193831553416,
    10772391370048, 21422369201800, 40715807302800, 73514652074500,
    124680849918352, 194214400834356, 263747951750360, 263747951750360, 0}, 
  {0, 1, 29, 434, 4464, 35464, 231880, 1298528, 6399888, 28312548, 114108148,
    423830264, 1464140912, 4739192952, 14460614392, 41802112192, 114955808528,
    301758997386, 758201178306, 1827459250276, 4232010895376, 9425842448792,
    20198233818840, 41620603020640, 82336410323440, 155851062397940,
    280531912316292, 474746313150648, 738494264901008, 1002242216651368,
    1002242216651368, 0}, 
  {0, 1, 30, 464, 4928, 40392, 272272, 1570800, 7970688, 36283236, 150391384,
    574221648, 2038362560, 6777555512, 21238169904, 63040282096, 177996090624,
    479755088010, 1237956266316, 3065415516592, 7297426411968, 16723268860760,
    36921502679600, 78542105700240, 160878516023680, 316729578421620,
    597261490737912, 1072007803888560, 1810502068789568, 2812744285440936,
    3814986502092304, 3814986502092304, 0}, 
  {0, 1, 31, 495, 5423, 45815, 318087, 1888887, 9859575, 46142811, 196534195,
    770755843, 2809118403, 9586673915, 30824843819, 93865125915, 271861216539,
    751616304549, 1989572570865, 5054988087457, 12352414499425, 29075683360185,
    65997186039785, 144539291740025, 305417807763705, 622147386185325,
    1219408876923237, 2291416680811797, 4101918749601365, 6914663035042301,
    10729649537134605, 14544636039226909, 14544636039226909, 0}, 
  {0, 1, 32, 527, 5950, 51765, 369852, 2258739, 12118314, 58261125, 254795320,
    1025551163, 3834669566, 13421343481, 44246187300, 138111313215,
    409972529754, 1161588834303, 3151161405168, 8206149492625, 20558563992050,
    49634247352235, 115631433392020, 260170725132045, 565588532895750,
    1187735919081075, 2407144796004312, 4698561476816109, 8800480226417474,
    15715143261459775, 26444792798594380, 40989428837821289, 55534064877048198,
    55534064877048198, 0}
#endif
 };



USI *sA069770 = NULL;

int A069770(int n)
{
    if(NULL == sA069770)
     {
       fprintf(stderr,"A069770: Should not call this function at this time as the sequence sA069770 has not been initialized!\n");
       exit(1);
     }
    else { return(sA069770[n]); }
}


/* 
   See Frank Ruskey's thesis at:
   http://www.cs.uvic.ca/~fruskey/Publications/Thesis/Thesis.html
 */

RANK CatalanRank(SIZE n,TBBS a)
{
    int m = -1;
    int y = 0;
    LRANK r = 0;

    while(a > 0)
     {
       if(0 == (a & 1))
        {
          m++;
        }
       else
        {
          y++;
          r += CatTriangle(m,y);
        }
       a >>= 1;
     }

    return(r);
}

TBBS CatalanUnrank(SIZE n,LRANK r)
{
    int m = n-1;
    int y = n;
    TBBS a = 0;

    while(m >= 0)
     {
       LRANK c = CatTriangle(m,y);

       a <<= 1;

       if(r >= c)
        {
          y--;
          a++;
          r -= c;
        }
       else
        {
          m--;
        }
     }

    return(a);
}

static int CRS_m, CRS_y;
static LRANK CRS_r;

void CatalanRankSexpAux(SEXP node)
{
    if(NULLP(node)) { CRS_m--; }
    else
     {
       CRS_r += CatTriangle(CRS_m,CRS_y);
       CRS_y--;
       CatalanRankSexpAux(CAR(node));
       CatalanRankSexpAux(CDR(node));
     }
}


RANK CatalanRankSexp(SIZE n,SEXP node)
{
    CRS_m = n-1;
    CRS_y = n;
    CRS_r = 0;

    CatalanRankSexpAux(node);

    return(CRS_r);
}


SEXP CatalanUnrankSexp(SIZE n,LRANK r,SEXP *reused)
{
    int m = n-1;
    int y = n;
    int sp = 0;
    int rightson = 0;

    SEXP root = NULL;
    SEXP sonstack[MAXSIZE+1];

    while(m >= 0)
     {
       LRANK c = CatTriangle(m,y);

       if(r >= c)
        {
          SEXP newbranch = recons(NULL,NULL,reused);

          if(NULLP(root)) { root = newbranch; }
          else
	   {
             if(rightson) { SET_CDR(sonstack[sp],newbranch); }
             else { SET_CAR(sonstack[sp],newbranch); sp++; }
           }

          sonstack[sp] = newbranch;

          y--;
          r -= c;
          rightson = 0; /* The next one is a left son. */
        }
       else
        {
          m--;
          sp -= rightson;
          rightson = 1; /* The next one is a right son. */
        }
     }

    return(root);
}


RANK CatalanRankGlobal(SIZE n,TBBS a)
{
    if(0 == n) { return(0); }
    else { return(A014137(n-1)+CatalanRank(n,a)); }
}


RANK CatalanRankSexpGlobal(SIZE n,SEXP s)
{
    if(0 == n) { return(0); }
    else { return(A014137(n-1)+CatalanRankSexp(n,s)); }
}


void print_sexp(SEXP s)
{
    putchar('(');
    while(!NULLP(s)) { print_sexp(CAR(s)); s = CDR(s); }
    putchar(')');
}


/* See the section "Number Conversion" at the end of
   the excerpt: http://www.iki.fi/~kartturi/matikka/kl10exmp.txt
 */
int fprint_ulli(FILE *fp,ULLI x)
{
    int s = 0;
    if(x >= 10) { s = fprint_ulli(fp,(x/((ULLI)10))); }
    fputc(('0' + (x%((ULLI)10))),fp);
    return(s+1);
}


/* We could as well compute it on runtime, of course... */
void CheckTriangle(int upto_n)
{
   int r,m;

   for(r=0; r <= upto_n; r++)
    {
      for(m=0; m < r; m++)
       {
         if((CatTriangle(r,m-1) + CatTriangle(r-1,m)) != CatTriangle(r,m))
          {
            fprintf(stderr,"(CatTriangle(%d,%d) + CatTriangle(%d,%d)) = ",
		    r,(m-1),(r-1),m);
            fprint_ulli(stderr,(CatTriangle(r,m-1) + CatTriangle(r-1,m)));
            fprintf(stderr," differs from CatTriangle(%d,%d) = ",
                    r,m);
            fprint_ulli(stderr,CatTriangle(r,m));
            fprintf(stderr,"\n");

            exit(1);
          }
       }
      if((r > 0) && (CatTriangle(r,m) != CatTriangle(r,m-1)))
       {
         fprintf(stderr,"(CatTriangle(%d,%d) = ",r,m);
         fprint_ulli(stderr,CatTriangle(r,m));
         fprintf(stderr," differs from CatTriangle(%d,%d) = ",r,(m-1));
         fprint_ulli(stderr,CatTriangle(r,m-1));
         fprintf(stderr,"\n");

         exit(1);
       }
    }

/* fprintf(stderr,"Triangle OK!\n"); */
}

void CheckRankings(int upto_n) /* Well, superficially... */
{
   int n;
   RANK r,r2,uplim;

   for(n=0; n <= upto_n; n++)
    {
      uplim = Cat(n);
      for(r=0; r < uplim; r++)
       {
         TBBS tbs = CatalanUnrank(n,r);
         if(globopt_output_cycle_lists)
          {
	      fprint_ulli(stdout,tbs); printf(" ");
          }
         r2 = CatalanRank(n,tbs);
         if(r2 != r)
          {
            fflush(stdout);
            fprintf(stderr,"CatalanRank(%d,",n);
            fprint_ulli(stderr,tbs);
            fprintf(stderr,")=");
            fprint_ulli(stderr,r2);
            fprintf(stderr," != ");
            fprint_ulli(stderr,r);
            fprintf(stderr,"\n");

            exit(1);
          }
       }
      if(globopt_output_cycle_lists) { printf("\n"); }
    }

   fprintf(stdout,"Ranking & Unranking OK upto n=%d.\n", upto_n);
}

void CheckSexpRankings(int upto_n) /* Well, superficially... */
{
   int n;
   RANK r,r2,uplim;
   SEXP old_s = NULL;

   for(n=0; n <= upto_n; n++)
    {
      uplim = Cat(n);
      for(r=0; r < uplim; r++)
       {
         SEXP s = CatalanUnrankSexp(n,r,&old_s);
         if(globopt_output_cycle_lists)
          {
	    print_sexp(s); printf(" ");
          }
         r2 = CatalanRankSexp(n,s);
         if(r2 != r)
          {
            fflush(stdout);
            fprintf(stderr,"CatalanRankSexp(%d,s)=",n);
            fprint_ulli(stderr,r2);
            fprintf(stderr," != ");
            fprint_ulli(stderr,r);
            fprintf(stderr,"\n");

            exit(1);
          }
         old_s = s;
       }
      if(globopt_output_cycle_lists) { printf("\n"); }
    }

   fprintf(stdout,"Ranking & Unranking OK upto n=%d.\n", upto_n);
}

/**********************************************************************/

ULI sA127301_up_to6917[6918];
ULI sA129593_up_to6917[6918];
ULI sA153835_up_to6917[6918];


void fprint_USI_vector(FILE *fp,USI *vec,int veclen)
{
    int i;

    fprintf(fp,"%s",globopt_list_begin);
    for(i=0; i < veclen; i++)
     {
       if(i>0) { fprintf(fp,"%s",globopt_elem_delim); }
       fprintf(fp,"%u",*(vec+i));
     }
    fprintf(fp,"%s",globopt_list_end);
}

void fprint_vector_of_USI_vectors(FILE *fp,USI **vec,int veclen)
{
    while(NULL != *vec)
     {
       fprint_USI_vector(fp,*vec++,veclen);
     }
}


void fprint_ULI_vector(FILE *fp,ULI *vec,int veclen)
{
    int i;

    fprintf(fp,"%s",globopt_list_begin);
    for(i=0; i < veclen; i++)
     {
       if(i>0) { fprintf(fp,"%s",globopt_elem_delim); }
       fprintf(fp,"%lu",*(vec+i));
     }
    fprintf(fp,"%s",globopt_list_end);
}


#define NA_SENTINEL ((ULI) -1) /* I.e. 4294967295 with 32 bits. */

void fprint_ULI_vector_with_NA_SENTINELs(FILE *fp,ULI *vec,int veclen)
{
    int i;

    fprintf(fp,"%s",globopt_list_begin);
    for(i=0; i < veclen; i++)
     {
       if(i>0) { fprintf(fp,"%s",globopt_elem_delim); }
       if(NA_SENTINEL == *(vec+i)) { fprintf(fp,"NA"); }
       else { fprintf(fp,"%lu",*(vec+i)); }
     }
    fprintf(fp,"%s",globopt_list_end);
}


void fprint_ULLI_vector(FILE *fp,ULLI *vec,int veclen)
{
    int i;

    fprintf(fp,"%s",globopt_list_begin);
    for(i=0; i < veclen; i++)
     {
       if(i>0) { fprintf(fp,"%s",globopt_elem_delim); }
       fprint_ulli(fp,*(vec+i));
     }
    fprintf(fp,"%s",globopt_list_end);
}


void fprint_ULLI_vector_up_to_first_0(FILE *fp,ULLI *vec,int veclen)
{
    int i;

    fprintf(fp,"%s",globopt_list_begin);
    for(i=0; (i < veclen) && (0 != *(vec+i)); i++)
     {
       if(i>0) { fprintf(fp,"%s",globopt_elem_delim); }
       fprint_ulli(fp,*(vec+i));
     }
    fprintf(fp,"%s",globopt_list_end);
}



char *w6d(char *tb,int n)
{
    sprintf(tb,"%06u",n);
    return(tb);
}

void output_HTML_Alink(FILE *fp,int Anum)
{
    char tb[81] = { 'A' };
    char *Astr = (w6d(tb+1,Anum)-1);
    fprintf(fp,"<A HREF=\"http://www.research.att.com/projects/OEIS?Anum=%s\">%s</A>",Astr,Astr);
}


void output_n_chars(int i, char c)
{
     while(i--) { putchar(c); }
}

void output_n_spaces(int i) { output_n_chars(i,' '); }

/* How about templates? */
int USIvec_find_pos_of_1st_larger_than_one(USI *vec,int veclen)
{
    int pos_of_1st_term_gte_2 = 0;

    while((pos_of_1st_term_gte_2 < veclen)
            && (*(vec+pos_of_1st_term_gte_2) < 2))
     { pos_of_1st_term_gte_2++; }

    if(pos_of_1st_term_gte_2 >= veclen) { pos_of_1st_term_gte_2 = 1; } /* Not found, use 1. */
    else { pos_of_1st_term_gte_2++; } /* Because One-based. */

    return(pos_of_1st_term_gte_2);
}

int ULIvec_find_pos_of_1st_larger_than_one(ULI *vec,int veclen)
{
    int pos_of_1st_term_gte_2 = 0;

    while((pos_of_1st_term_gte_2 < veclen)
            && (*(vec+pos_of_1st_term_gte_2) < 2))
     { pos_of_1st_term_gte_2++; }

    if(pos_of_1st_term_gte_2 >= veclen) { pos_of_1st_term_gte_2 = 1; } /* Not found, use 1. */
    else { pos_of_1st_term_gte_2++; } /* Because One-based. */

    return(pos_of_1st_term_gte_2);
}


int ULLIvec_find_pos_of_1st_larger_than_one(ULLI *vec,int veclen)
{
    int pos_of_1st_term_gte_2 = 0;

    while((pos_of_1st_term_gte_2 < veclen)
            && (*(vec+pos_of_1st_term_gte_2) < 2))
     { pos_of_1st_term_gte_2++; }

    if(pos_of_1st_term_gte_2 >= veclen) { pos_of_1st_term_gte_2 = 1; } /* Not found, use 1. */
    else { pos_of_1st_term_gte_2++; } /* Because One-based. */

    return(pos_of_1st_term_gte_2);
}


#define VECTYPE_USI  16
#define VECTYPE_ULI  32
#define VECTYPE_ULLI 64

#define OEIS_SEQ     0
#define OEIS_TABLE   1


#define VECTYPE_NORERANK VECTYPE_ULI
#define fprint_NORERANK_vector_with_NA_SENTINELs fprint_ULI_vector_with_NA_SENTINELs

typedef void (*PF_VEC_OUT)(FILE *,void *,int);

void output_OEIS_sequence(FILE *fp,int Anum,
                          void *vec,int veclen,
                          int vectype,
                          PF_VEC_OUT fprintvecfun,
                          int offset,
                          int seqtype,
                          char *name
                         )
{
    char tb[81] = { 'A' };
    char *Astr = (w6d(tb+1,Anum)-1);
    int pos_of_1st_term_gte_2
           = ((VECTYPE_ULLI == vectype)
                 ? ULLIvec_find_pos_of_1st_larger_than_one(vec,veclen)
                 : ((VECTYPE_USI == vectype)
                    ? USIvec_find_pos_of_1st_larger_than_one(vec,veclen)
                    : ULIvec_find_pos_of_1st_larger_than_one(vec,veclen)
                   )
             );

/*
    PF_VEC_OUT fprintvecfun = ((VECTYPE_ULLI == vectype)
                                  ? fprint_ULLI_vector
                                  : ((VECTYPE_USI == vectype)
                                          ? fprint_USI_vector
                                          : fprint_ULI_vector
                                    )
                              );
 */

    char *save_globopt_list_begin = globopt_list_begin;
    char *save_globopt_list_end   = globopt_list_end;
    char *save_globopt_elem_delim = globopt_elem_delim;

    /* Set these for fprint_vector: */
    globopt_list_begin = "";
    globopt_list_end = "";
    globopt_elem_delim = ",";


    fprintf(fp,"%%I %s\n",Astr);

    if(globopt_HTML)
     {
       fprintf(fp,"%%S ");
       output_HTML_Alink(fp,Anum);

       fprintf(fp," <A HREF=\"http://www.research.att.com/cgi-bin/access.cgi/as/njas/sequences/eishis.cgi?sequence=");
       fprintvecfun(fp,vec,veclen); /* Skip two terms from the start when searching. */
       fprintf(fp, "\">");
       fprintvecfun(fp,vec,veclen);
       fprintf(fp, "</A>");
     }
    else
     {
       fprintf(fp,"%%S %s ",Astr);
       fprintvecfun(fp,vec,veclen);
     }
    fprintf(fp,"\n");

    fprintf(fp,"%%N %s %s\n",Astr,name); /* Name should end with period. */

    fprintf(fp,"%%H %s A. Karttunen, <a href=\"http://www.research.att.com/~njas/sequences/a089839.c.txt\">C-program for computing the initial terms of this sequence</a>\n",
            Astr);

    fprintf(fp,"%%K %s nonn%s\n",Astr,((OEIS_TABLE == seqtype) ? ",tabl" : ""));
    fprintf(fp,"%%O %s %u,%u\n",Astr,offset,pos_of_1st_term_gte_2);
    fprintf(fp,"%%A %s %s, %s\n",  Astr, glob_author_info, glob_datestr); /* E.g. Antti Karttunen (Firstname.Surname@gmail.com), Oct XX 2006 */
    fprintf(fp,"\n");
    fflush(fp);

    globopt_list_begin = save_globopt_list_begin;
    globopt_list_end   = save_globopt_list_end;
    save_globopt_elem_delim = save_globopt_elem_delim;
}


/**********************************************************************/



int sexp_length(SEXP s)
{
    int i = 0;

    while(PAIR(s)) { i++; s = CDR(s); }
    return(i);
}


/* Place the subtrees of t1 extending past the tips of t2
   into the SEXP-vector subtrees.
   The positions in the constructed list correspond to the
   tips (leaves) of t2 in preorder.
   This version returns back immediately if
   A082858(t1,t2) != t2, that is, if t1 is not a super-tree of t2.

   An example how to write re-entrant code by using doubly
   indirect pointing, i.e. we do not increment p_to_subtrees
   itself, but a SEXP pointer to which it points at!
 */
int sexp_bintree_difference_aux(SEXP t1,SEXP t2,SEXP **p_to_subtrees)
{
    if(!PAIR(t2)) { **p_to_subtrees = t1; ++*p_to_subtrees; return(1); }
    else if(!PAIR(t1)) { return(0); } /* In this order! */
    else
     {
       if(0 == sexp_bintree_difference_aux(CAR(t1),CAR(t2),p_to_subtrees))
        { return(0); }
       else
        { return(sexp_bintree_difference_aux(CDR(t1),CDR(t2),p_to_subtrees)); }
     }
}


int sexp_bintree_difference(SEXP t1,SEXP t2,SEXP *subtrees)
{
    SEXP *copy_of_subtree_pointer = subtrees; /* With which we can safely play! */
    return(sexp_bintree_difference_aux(t1,t2,&copy_of_subtree_pointer));
}


/*
   Transform an arbitrarily shaped tree t1 to a "right comb",
   provided that A082858(t1,t2) = t2.

  1  2                                 2  3
 0 \/                                 1 \/
  \/ 3       -->                     0 \/
   \/                                 \/

                           7  8
 1 2 3  4                 6 \/
  \/  \/                 5 \/
   \  /                 4 \/
  0 \/6  7             3 \/
   \/5 \/     -->     2 \/
    \ \/ 8           1 \/
     \ \/           0 \/
      \/             \/

 NOTE: It's the responsibility of the caller also to
 free the main stem (tree_size cons cells) of the
 tree new_tree possibly constructed here!

 */


SEXP sexp_transform1(SEXP t1,SEXP t2,const int t2_size)
{
    int i;
    SEXP tmp;
    SEXP stem[MAX_CLAUSE_SIZE+1];
    SEXP new_tree;

    if(0 == sexp_bintree_difference(t1,t2,stem)) { return(NULL); }

    new_tree = stem[t2_size];

    for(i=t2_size-1; (i >= 0); i--)
     {
       new_tree = cons(stem[i],new_tree);
     }

    return(new_tree);
}


/*
   Transform a right comb "t1" into an arbitrarily shaped tree new_tree
   guided by the "guiding tree" t2.
   Do this by destructively modifying t2, by overwriting the NILs
   at its tips by the corresponding subtrees of t1.

   I.e. we will have A082858(new_tree,t2) = t2.
   This is an inverse transform of sexp_transform1,
   i.e. we should have sexp_transform2(sexp_transform1(t1,t2),t2) = t1
   provided that A082858(t1,t2) = t2.

   One SHOULD NOT call this if length(t1) < t2_size

   2  3               1  2
  1 \/               0 \/
 0 \/      -->        \/ 3
  \/                   \/
                    
        7  8
       6 \/          1 2 3  4
      5 \/            \/  \/ 
     4 \/              \  /  
    3 \/              0 \/6  7
   2 \/    -->         \/5 \/
  1 \/                  \ \/ 8
 0 \/                    \ \/
  \/                      \/


  Think that some people advocate programming languages with no POINTERS!

 */

void sexp_transform2_aux(SEXP *t1,SEXP *t2,int *n_nodes_left)
{
    if(!PAIR(*t1))
     {
       fprintf(stderr,"sexp_transform2_aux: length(t1) < size(t2), premature end!\n");
       exit(1);
     }
    if(!PAIR(*t2)) /* Reached one of the tips of t2. */
     {
       if(0 == *n_nodes_left) { *t2 = CDR(*t1); }
       else
        {
          *t2 = CAR(*t1);
          if(0 != --*n_nodes_left) { *t1 = CDR(*t1); }
        }
     }
    else
     {
       sexp_transform2_aux(t1,&(CAR(*t2)),n_nodes_left);
       sexp_transform2_aux(t1,&(CDR(*t2)),n_nodes_left);
     }
}


/* This should protect the variables in the original caller: */
void sexp_transform2(SEXP t1,SEXP t2,int t2_size) /* <= t1_length */
{
    sexp_transform2_aux(&t1,&t2,&t2_size);
}


/*
   We swap the tp1:th and tp2:th subtree (zero-based)
   sprouting leftward from the main stem, unless tp2
   is tree_size, in which case it is the (tp2-1):th cdr
   from the root.

    2  3                                            0  3
   1 \/                                            1 \/
  0 \/    transposition (tp1=0, tp2=2) results    2 \/
   \/                                              \/

  transposition (tp1=1, tp2=3) results:

    2  1
   3 \/
  0 \/
   \/


  0  1
   \/

 Note that tp1 < tp2 is required!

 */
int sexp_transpose(SEXP sexp,const int tree_size,const int tp1,const int tp2)
{
    int i;
    SEXP tmp;
    SEXP stem[MAX_CLAUSE_SIZE+1]; /* "stem" or "spine" of the tree. */

    for(i=0; (i < tree_size) && PAIR(sexp); )
     {
       stem[i++] = sexp;
       sexp = CDR(sexp);
     }

    /* Can't do it on this tree because its main stem is not long enough.
       So return zero as a sign of failure. */
    if(i < tree_size) { return(0); }

    /* No-op "transposition", return immediately with success: */
    if(tp1 == tp2) { return(1); }

    if(tree_size == tp2)
     {
       tmp = CDR(stem[tp2-1]);
       SET_CDR(stem[tp2-1],CAR(stem[tp1]));
     }
    else /* tp2 < tree_size, swap two leftward leaning subtrees. */
     {
       tmp = CAR(stem[tp2]);
       SET_CAR(stem[tp2],CAR(stem[tp1]));
     }
    SET_CAR(stem[tp1],tmp);

    return(1);
}


void precompute_transform1(SGRANK *vec,int upto_n,int t2_size,LRANK t2_lrank)
{
    int t1_size; /* The size of the trees for which we are computing this
                    transformation in the inner loop. */
    LRANK t1_lrank;
    SEXP t1 = NULL;
    SEXP t2 = CatalanUnrankSexp(t2_size,t2_lrank,NULL);
    SEXP new_tree = NULL;
    int i = 0;

    vec[i++] = 0; /* NIL to NIL, always! */

/* t2 is the "guiding" tree, against which we compare every tree t1 generated
   in the loop below: */

    for(t1_size=1; t1_size <= upto_n; t1_size++)
     {
       for(t1_lrank = 0; t1_lrank < Cat(t1_size); t1_lrank++)
        {
          if(t1_size < t2_size) /* The subtree does not fit yet. */
           { vec[i++] = 0; }
          else /* Our left-comb of tree_size nodes could be a subtree of */
           {   /* this sexp, at least in principle. */
             t1 = CatalanUnrankSexp(t1_size,t1_lrank,&t1);

             new_tree = sexp_transform1(t1,t2,t2_size);

             if(NULLP(new_tree)) { vec[i++] = 0; } /* A082858(t1,t2) != t2 */
             else /* t1 is a super-tree of t2. */
              {
                vec[i++] = CatalanRankSexpGlobal(t1_size,new_tree);
                free_cons_list(new_tree,t2_size);
              }
           }
        }
     }

    free_cons_tree(t1);
    free_cons_tree(t2);
}


/* Could be faster if we coded a modified variant of CatalanUnrankSexp
   that used the subtrees of t1 as its leaf-nodes.
   Here we do some extra unranking of t2, because it is physically modified.
   However, as the time taken by these precomputing routines is minimal
   to the run proper, we don't care now.
 */
void precompute_transform2(SGRANK *vec,int upto_n,int t2_size,LRANK t2_lrank)
{
    int t1_size; /* The size of the trees for which we are computing this
                    transformation in the inner loop. */
    LRANK t1_lrank;
    SEXP t1 = NULL;
    SEXP t2 = NULL;
    SEXP old_t2 = NULL;
    int i = 0;

    vec[i++] = 0; /* NIL to NIL, always! */

    for(t1_size=1; t1_size <= upto_n; t1_size++)
     {
       for(t1_lrank = 0; t1_lrank < Cat(t1_size); t1_lrank++)
        {
          if(t1_size < t2_size) /* The subtree does not fit yet. */
           { vec[i++] = 0; }
          else
           {
             t1 = CatalanUnrankSexp(t1_size,t1_lrank,&t1);

             if(sexp_length(t1) < t2_size) { vec[i++] = 0; }
             else
              {
                t2 = CatalanUnrankSexp(t2_size,t2_lrank,&old_t2);
                free_cons_tree(old_t2); /* If any residues left... */

                /* Modifies t2 by overwriting its NILs with t1's subtrees. */
                sexp_transform2(t1,t2,t2_size);
                vec[i++] = CatalanRankSexpGlobal(t1_size,t2);
/* Free the main stem of t1. The other nodes of t1 have been passed to t2,
   so their time will come later, when t2 is eventually recycled: */
                free_cons_list(t1,t2_size);
                t1 = NULL; /* Avoid double deallocations. */
                old_t2 = t2;
              }
           }
        }
     }

    free_cons_tree(t1);
    free_cons_tree(t2);
}


/* The tree on which we do these subtree transpositions is
   the right-leaning "comb", i.e. the lexicographically first
   tree of size tree_size.

   Note that tp1 < tp2 is required!

   I.e. we compute the A014486-indices for each tree in
   range [0..A014138(tree_size-1)], after (tp1 tp2) leaf-transposition
   has been applied to it, or place zero into the corresponding
   place in the vector, if it is not possible to do that kind
   of leaf-transposition for the binary tree in question.
 */
void precompute_subtree_transposition(SGRANK *vec,int upto_n,int tree_size,
                                      int tp1,int tp2)
{
    int t_size; /* The size of the trees for which we are computing this subtree
              transposition in the inner loop. */
    SEXP sexp = NULL;
    LRANK r;
    int i = 0;

    vec[i++] = 0; /* NIL to NIL, always! */

    for(t_size=1; t_size <= upto_n; t_size++)
     {
       for(r = 0; r < Cat(t_size); r++)
        {
          if(t_size < tree_size) /* The subtree does not fit yet. */
           { vec[i++] = 0; }
          else /* Our left-comb of tree_size nodes could be a subtree of */
           {   /* this sexp, at least in principle. */
             sexp = CatalanUnrankSexp(t_size,r,&sexp);
             if(sexp_transpose(sexp,tree_size,tp1,tp2))
              { vec[i++] = CatalanRankSexpGlobal(t_size,sexp); }
             else { vec[i++] = 0; }
           }
        }
     }

    free_cons_tree(sexp);
}


/* Precompute transpositions <1,0>; <2,1>, <2,0>; <3,2>, <3,1>, <3,0>;
                             <4,3>, <4,2>, <4,1>, <4,0>; ....
                             <tree_size,tree_size-1>, <tree_size,tree_size-2>, ...
                               <tree_size,0>
   to the vectors that are allocated on the fly, and stored into vec_ptrs.
 */

USI **precompute_transposition_vectors(int tree_size,int upto_n,int vec_size)
{
    USI **org_vec_ptrs;
    USI **vec_ptrs = ((USI **) calloc(A000217(tree_size),sizeof(USI *)));
    int i,j;

    if(NULL == vec_ptrs)
     {
       fprintf(stderr,
              "precompute_transposition_vectors(tree_size=%u): Couldn't allocate a vector of %u pointers where to store the transposition vectors!\n",
              tree_size,A000217(tree_size));
       exit(1);
     }
    else { org_vec_ptrs = vec_ptrs; }

    for(i=1; i <= tree_size; i++)
     {
       for(j=i; j > 0; j--)
        {
          USI *new_vec = ((USI *) calloc(vec_size,sizeof(USI)));

          *vec_ptrs++ = new_vec;
          if(NULL == new_vec)
           {
             fprintf(stderr,
                     "precompute_transposition_vectors(tree_size=%u): Couldn't allocate a %uth vector of %u short integers! i=%u, j=%u\n",
                      tree_size,(vec_ptrs-org_vec_ptrs),vec_size,i,j);
             exit(1);
           }

          precompute_subtree_transposition(new_vec,upto_n,tree_size,j-1,i);
        }
     }

     {
       fprintf(stderr,"precompute_transposition_vectors: precomputed %u vectors for the clause trees of size %u\n",
               (vec_ptrs-org_vec_ptrs),tree_size
              );
     }

    if(0 != glob_cons_cells_in_use)
     {
       fprintf(stderr,"precompute_transposition_vectors(tree_size=%u): glob_cons_cells_in_use=%lu\n",
               tree_size,glob_cons_cells_in_use
              );
     }

    return(org_vec_ptrs);
}


USI **precompute_transform_vectors(int tree_size,int upto_n,int vec_size)
{
    USI **org_vec_ptrs;
    USI **vec_ptrs = ((USI **) calloc(2*Cat(tree_size),sizeof(USI *)));
    int tree_lrank;

    if(NULL == vec_ptrs)
     {
       fprintf(stderr,
              "precompute_transform_vectors(tree_size=%u): Couldn't allocate a vector of %lu pointers where to store the transposition vectors!\n",
              tree_size,2*Cat(tree_size));
       exit(1);
     }
    else { org_vec_ptrs = vec_ptrs; }

    for(tree_lrank = 0; tree_lrank < Cat(tree_size); tree_lrank++)
     {
       USI *vec1 = ((USI *) calloc(vec_size,sizeof(USI)));
       USI *vec2;
       int i;

       *vec_ptrs++ = vec1;
       if(NULL == vec1)
        {
          fprintf(stderr,
                  "precompute_transform_vectors(tree_size=%u): Couldn't allocate a %uth vector of %u short integers! tree_lrank=%u\n",
                   tree_size,(vec_ptrs-org_vec_ptrs),vec_size,tree_lrank);
          exit(1);
        }

       vec2 = ((USI *) calloc(vec_size,sizeof(USI)));

       *vec_ptrs++ = vec2;
       if(NULL == vec2)
        {
          fprintf(stderr,
                  "precompute_transform_vectors(tree_size=%u): Couldn't allocate a %uth vector of %u short integers! tree_lrank=%u\n",
                   tree_size,(vec_ptrs-org_vec_ptrs),vec_size,tree_lrank);
          exit(1);
        }

       precompute_transform1(vec1,upto_n,tree_size,tree_lrank);

       precompute_transform2(vec2,upto_n,tree_size,tree_lrank);

       for(i=0; i< vec_size; i++)
        {
          if(((0 != vec1[i]) && (vec2[vec1[i]] != i))
             ||
             ((0 != vec2[i]) && (vec1[vec2[i]] != i))
            )
           {
             fprintf(stderr,
                     "precompute_transform_vectors(tree_size=%u): Fatal error: precompute_transform1 and _transform2 didn't produce inverses of each other! Offending terms at i=%u. tree_lrank=%u. The vec1 and vec2 are printed below:\n",
                     tree_size,i,tree_lrank
                    );
             fflush(stderr);
             fprint_USI_vector(stderr,vec1,vec_size);
             fprint_USI_vector(stderr,vec2,vec_size);

             exit(1);
           }
        }
     }

     {
       fprintf(stderr,"precompute_transform_vectors: precomputed %u vectors for the clause trees of size %u\n",
               (vec_ptrs-org_vec_ptrs),tree_size
              );
     }

    if(0 != glob_cons_cells_in_use)
     {
       fprintf(stderr,"precompute_transform_vectors(tree_size=%u): glob_cons_cells_in_use=%lu\n",
               tree_size,glob_cons_cells_in_use
              );
     }

    return(org_vec_ptrs);
}


/****************  Additions Jan 4 2009  ******************/

/* See A153250. */

/*
   We compute the A014486-indices for each tree in
   range [0..A014138(tree_size-1)], after a bud \/ has been
   inserted into the leaf-position leafpos
   (which can range from 0 to tree_size).
   If the tree in question has less than leafpos+1 leaves,
   then zero is stored into the corresponding
   place in the vector.
 */
void precompute_bud_insertions_at_leaf(SGRANK *vec,int upto_treesize_n,
                                       int leafpos)
{
    int t_size; /* The size of the trees. */
    SEXP sexp = NULL;
    LRANK r;
    int i = 0;

    vec[i++] = (!leafpos ? 1 : 0); /* () to (()) when leafpos=0. */

    for(t_size=1; t_size <= upto_treesize_n; t_size++)
     {
       for(r = 0; r < Cat(t_size); r++)
        {
          if(leafpos > t_size) /* Trees of this size have no leaf leafpos */
           { vec[i++] = 0; }
          else
           {
             sexp = CatalanUnrankSexp(t_size,r,NULL);

             graft_bud_at(sexp,leafpos);
             vec[i++] = CatalanRankSexpGlobal((t_size+1),sexp);

             free_cons_tree(sexp);
           }
        }
     }
}


/* Precompute (A072643(n)+1)*A014137(tree_size)
            = (tree_size+1)*A014137(tree_size)
   trees, where a new \/ bud has been inserted to (tree_size+1) possible
   leaves in each of Cat(tree_size) trees.
   Store A014486-indices of these trees to the vectors that are
   allocated on the fly, and stored into vec_ptrs.
 */

USI **precompute_bud_vectors(int tree_size,int vec_size)
{
    USI **org_vec_ptrs;
    USI **vec_ptrs = ((USI **) calloc((tree_size+1),sizeof(USI *)));
    int leafpos;

    if(NULL == vec_ptrs)
     {
       fprintf(stderr,
              "precompute_bud_vectors(tree_size=%u): Couldn't allocate a vector of %lu pointers where to store the vectors!\n",
              tree_size,(tree_size+1));
       exit(1);
     }
    else { org_vec_ptrs = vec_ptrs; }

    for(leafpos=0; leafpos <= tree_size; leafpos++)
     {
       USI *new_vec = ((USI *) calloc(vec_size,sizeof(USI)));

       *vec_ptrs++ = new_vec;
       if(NULL == new_vec)
        {
          fprintf(stderr,
            "precompute_bud_vectors(tree_size=%u): Couldn't allocate the %uth vector of %u short integers! leafpos=%u\n",
            tree_size,(vec_ptrs-org_vec_ptrs),vec_size,leafpos);
          exit(1);
        }
/*
       else
        {
          fprintf(stderr,
            "precompute_bud_vectors(tree_size=%u): Allocated the %uth vector of %u short integers! Leaf position=%u\n",
            tree_size,(vec_ptrs-org_vec_ptrs),vec_size,leafpos);
          fflush(stderr);
        }
 */

       precompute_bud_insertions_at_leaf(new_vec,tree_size,leafpos);

/*
        {
          fprintf(stderr,"precompute_bud_vectors: precomputed the %uth vector for the leaf position %u. Vector contents follow:\n",
                         (vec_ptrs-org_vec_ptrs),leafpos
                 );
          fflush(stderr);
          fprint_USI_vector(stdout,new_vec,vec_size);
          printf("\n\n");
          fflush(stdout);
        }
 */
     }

     {
       fprintf(stderr,"precompute_bud_vectors: precomputed %u vectors for the clause trees of size %u\n",
               (vec_ptrs-org_vec_ptrs),tree_size
              );
     }

    if(0 != glob_cons_cells_in_use)
     {
       fprintf(stderr,"precompute_bud_vectors(tree_size=%u): glob_cons_cells_in_use=%lu\n",
               tree_size,glob_cons_cells_in_use
              );
     }

    return(org_vec_ptrs);
}


/* See A082858 */

USI **precompute_subtree_bitvectors(int upto_size)
{
    USI **org_vec_ptrs;
    USI **vec_ptrs = ((USI **) calloc((upto_size+1),sizeof(USI *)));
    int t_size, tree_lrank_s, tree_lrank_l;

    if(NULL == vec_ptrs)
     {
       fprintf(stderr,
              "precompute_subtree_bitvectors(upto_size=%u): Couldn't allocate a vector of %lu pointers where to store the transposition vectors!\n",
              upto_size,(upto_size+1));
       exit(1);
     }
    else { org_vec_ptrs = vec_ptrs; }

    *vec_ptrs++ = NULL; /* Dummy vector for t_size=0. */

    for(t_size=1; t_size <= upto_size; t_size++)
     {
       int uplim = Cat(t_size)*Cat(t_size+1);
       int vec_size = (((int)(uplim >> 3))/(sizeof(USI)/sizeof(BYTE)))+1;
       USI *vec1 = ((USI *) calloc(vec_size,sizeof(USI)));
       int i;

       *vec_ptrs++ = vec1;

       if(NULL == vec1)
        {
          fprintf(stderr,
                 "precompute_subtree_bitvectors(upto_size=%u): Couldn't allocate the %uth vector of %u short integers!\n",
                  upto_size,(vec_ptrs-org_vec_ptrs),vec_size);
          exit(1);
        }
/*
       else
        {
          fprintf(stderr,
                 "precompute_subtree_bitvectors(upto_size=%u): Allocated the %uth vector of %u short integers!\n",
                 upto_size,(vec_ptrs-org_vec_ptrs),vec_size);
          fflush(stderr);
        }
 */

       for(tree_lrank_s = 0; tree_lrank_s < Cat(t_size); tree_lrank_s++)
        {
          SEXP tree_s = CatalanUnrankSexp(t_size,tree_lrank_s,NULL);

          for(tree_lrank_l = 0; tree_lrank_l < Cat(t_size+1); tree_lrank_l++)
           {
             SEXP tree_l = CatalanUnrankSexp(t_size+1,tree_lrank_l,NULL);
             int bit_index = index2t(t_size,tree_lrank_s,tree_lrank_l);

             if(sexp_is_subtree(tree_s,tree_l))
              {
                toggle_bit_on(((BYTE *)vec1),bit_index);
              }
             else
              {
                toggle_bit_off(((BYTE *)vec1),bit_index);
              }

             free_cons_tree(tree_l);
           }
          free_cons_tree(tree_s);
	}
/*
        {
          fprintf(stderr,"precompute_subtree_bitvectors: precomputed the %uth bitvector. Vector contents follow:\n",
                         (vec_ptrs-org_vec_ptrs),i
                 );
          fflush(stderr);
          fprint_USI_vector(stdout,vec1,vec_size);
          printf("\n\n");
          fflush(stdout);
        }
 */
     }

     {
       fprintf(stderr,"precompute_subtree_bitvectors: precomputed %u vectors for trees up to size %u\n",
               (vec_ptrs-org_vec_ptrs),upto_size
              );
     }

    if(0 != glob_cons_cells_in_use)
     {
       fprintf(stderr,"precompute_subtree_bitvectors(upto_size=%u): glob_cons_cells_in_use=%lu\n",
               upto_size,glob_cons_cells_in_use
              );
     }

    return(org_vec_ptrs);
}


int check_invariance(ULI *invariant_seq,ECOTEX *ep)
{
    int t_size;
    LRANK t_lrank;
    SGRANK x;
    SGRANK y;

    for(t_size=1, x=1; t_size <= ep->upto_size_n; t_size++)
     {
       for(t_lrank = 0; t_lrank < Cat(t_size); t_lrank++, x++)
        { /* We have a cached copy of the latest sigperm, so let's use it! */
          y = ep->vals_obtained[x];
          if(invariant_seq[y] != invariant_seq[x]) { return(x); }
	}
     }

    return(0);
}

int check_budding_invariance(ECOTEX *ep)
{
    int t_size, leafpos;
    LRANK t_lrank;
    SGRANK x,x2;
    SGRANK y,y2;
    SLRANK y_l, y2_l;

    /* Check trees of all sizes, except the largest ones. */
    for(t_size=1, x=1; t_size < ep->upto_size_n; t_size++)
     {
       USI *subtree_bitvec = ep->subtree_bitvecs[t_size];

       /* And all the Cat(t_size) trees of each size. */
       for(t_lrank = 0; t_lrank < Cat(t_size); t_lrank++, x++)
        {
          y = ep->vals_obtained[x]; /* Get CatBij(x) from the cache. */
          y_l = global2local_rank(y,t_size);

          if((0 != x) && (0 == y))
           {
             fprintf(stderr,"\ncheck_budding_invariance: fatal error: y=%u! x=%u, t_size=%u, t_lrank=%u\n",
                     y,x,t_size,t_lrank);
             exit(1);
           }

          /* And for each tree, check for each leafpos (0..t_size), whether
             CatBij(x) is a subtree of CatBij(x+extra_leaft_at__leafpos):
           */
          for(leafpos = 0; leafpos <= t_size; leafpos++)
           {
             USI *budvec = ep->bud_vecs[leafpos];
             int x2;
             int bit_index;

             if(NULL == budvec)
              {
                fprintf(stderr,"\ncheck_budding_invariance: ep->bud_vecs[%u]=NULL, fatal error!\n",
                        leafpos);
                exit(1);
              }

             x2 = budvec[x];

             if(0 == x2)
              {
                fprintf(stderr,"\ncheck_budding_invariance: ep->bud_vecs[leafpos=%u][x=%u]=0, fatal error! t_size=%u, t_lrank=%u\n",
                        leafpos,x,t_size,t_lrank);
                exit(1);
              }

             y2 = ep->vals_obtained[x2];
             y2_l = global2local_rank(y2,(t_size+1));
             bit_index = index2t(t_size,y_l,y2_l);

             if(bit_is_zero(((BYTE *)subtree_bitvec),bit_index))
              {
/*
                fprintf(stdout,"\ncheck_budding_invariance: ep->bud_vecs[leafpos=%u][x=%u], t_size=%u, t_lrank=%u, x2=%u, y=%u, y2=%u, y_l=%u, y2_l=%u, bit_index=%u\n",
                        leafpos,x,t_size,t_lrank,
                        x2,y,y2,y_l,y2_l,bit_index);
                fflush(stdout);
 */
                return(x); /* Not a subtree, return immediately. */
              }
           }

	}
     }

    return(0); /* Otherwise, it is invariant vis-a-viz to budding. */
}


/**********************************************************************/

#ifdef DEBUG
#define ECOTEX_CLEAR_vals_obtained(ep)\
  printf("Clearing up to size %u, %u bytes...\n",ep->clear_next_time_upto_size_n,(sizeof(SGRANK)*A014137(ep->clear_next_time_upto_size_n)));\
  memset(((BYTE *)ep->vals_obtained),0,(sizeof(SGRANK)*A014137(ep->clear_next_time_upto_size_n)))
#else
#define ECOTEX_CLEAR_vals_obtained(ep)\
  memset(((BYTE *)ep->vals_obtained),0,(sizeof(SGRANK)*A014137(ep->clear_next_time_upto_size_n)))
#endif

#define ECOTEX_CLEAR_all_vals_obtained(ep)\
  memset(((BYTE *)ep->vals_obtained),0,(sizeof(SGRANK)*ep->vec_size))


/* Was: memset(((BYTE *)ep->vals_obtained),0,(sizeof(SGRANK)*A014137(ep->upto_size_n))) */

typedef int (*CLAUSESEQ_COMPFUN)(USI ***,int,ECOTEX *);

ECOTEX *new_ecotex(int upto_size_n)
{
    int tree_size,i;

    ECOTEX *ep = ((ECOTEX *) calloc(1,sizeof(ECOTEX)));

    if(NULL == ep)
     {
       fprintf(stderr,
                "new_ecotex: Couldn't allocate a new structure of %u bytes!\n",
                sizeof(ECOTEX)
              );
       exit(1);
     }

    ep->upto_size_n = upto_size_n;
    ep->vec_size = A014137(upto_size_n);

    ep->bijectivity_broken_at_size_n = 0;
    ep->clear_next_time_upto_size_n = 0;

    ep->vals_obtained  = ((SGRANK *) calloc(ep->vec_size,sizeof(SGRANK)));
    if(NULL == ep->vals_obtained)
     {
       fprintf(stderr,
                "new_ecotex: Couldn't allocate a value table vals_obtained of %u short integers (%u bytes). upto_size_n=%u\n",
	        ep->vec_size,ep->vec_size*sizeof(SGRANK),upto_size_n
              );
       exit(1);
     }

    ep->vals_obtained2 = ((SGRANK *) calloc(ep->vec_size,sizeof(SGRANK)));
    if(NULL == ep->vals_obtained2)
     {
       fprintf(stderr,
                "new_ecotex: Couldn't allocate a value table vals_obtained2 of %u short integers (%u bytes). upto_size_n=%u\n",
	        ep->vec_size,ep->vec_size*sizeof(SGRANK),upto_size_n
              );
       exit(1);
     }

    for(i=0, tree_size = 1; tree_size <= upto_size_n; tree_size++)
     {
       ep->all_vecs[i++] = precompute_transposition_vectors(tree_size,upto_size_n,ep->vec_size);
       ep->all_vecs[i++] = precompute_transform_vectors(tree_size,upto_size_n,ep->vec_size);
     }

    if(globopt_compute_A153830)
     {
       ep->bud_vecs = precompute_bud_vectors(upto_size_n,ep->vec_size);
       ep->subtree_bitvecs = precompute_subtree_bitvectors(upto_size_n-1);
     }
    else
     {
       ep->bud_vecs = NULL;
       ep->subtree_bitvecs = NULL;
     }

    return(ep);
}

/**********************************************************************/


#define globrank(tree_size,lrank) ((0 == (tree_size)) ? 0 : A014137(tree_size-1)+(lrank))

/* Size = 2+2+4+1 = 9 bytes. */
struct s_raw_clause
 {
     SSIZE  s_size;
     SLRANK s_lrank;
     SLRANK d_lrank;
     PERMRANK p_rank;
 };

/* Size = 4+4+1+1 = 10 bytes in 32-bit machines, 8+4+1+1 = 14 bytes if 64-bit pointers. */
struct s_raw_clauseseq_header
 {
     SSIZE n_clauses;
     BYTE binexp; /* Only upto binexp=255, but even that is enough! */
     struct s_clause *next_clauseseq; /* In the hash table bucket, NULL if last one. */
     NORERANK nth_distinct_bijection; /* Zero-based position in A089840. */
 };


/* Clause sequence is essentially a vector of clauses (CLAUSE *)
   where the first allocated clause structure is however interpreted
   as struct_raw_clauseseq_header, instead of s_raw_clause:
 */

struct s_clause
 {
   union
    {
      struct s_raw_clause cl;             /* In this order, so the explicit initializations think they initialize clauses, not headers. */
      struct s_raw_clauseseq_header hd;
    } u;
 };


typedef struct s_clause CLAUSE;
typedef CLAUSE *CLAUSESEQ;

#define CLAUSESEQ_next_clauseseq(CS) ((&CS[0])->u.hd.next_clauseseq) /* In the hash bucket. */
#define CLAUSESEQ_n_clauses(CS)      ((&CS[0])->u.hd.n_clauses) /* The number of clauses that follow. */
#define CLAUSESEQ_binexp(CS)         ((&CS[0])->u.hd.binexp)    /* The integer n whose binexp's runcounts are used for the composition of binwidth(n). */
#define CLAUSESEQ_norerank(CS)       ((&CS[0])->u.hd.nth_distinct_bijection)

#define SET_CLAUSESEQ_norerank(CS,NTH) (CLAUSESEQ_norerank(CS) = (NTH)) /* We should check for overflows > 4294967295 */

/* For explicit initializations. More than slightly dangerous!
   For now we have to omit binexp, because only the very first members,
   s_size and n_clauses of the structures s_raw_clause and
   s_raw_clauseseq_header are of the same size.
 */
#define CLAUSESEQ_begin(binexp,n_clauses) { (n_clauses),0,0,0 }

#define CLAUSESEQ_nthclause(CS,n) (CS[n])




#define CLAUSE_size(c) ((unsigned int)((c).u.cl.s_size))
#define SET_CLAUSE_size(c,s) (((c).u.cl.s_size) = ((SSIZE) (s)))
#define CLAUSE_s_lrank(c) ((c).u.cl.s_lrank)
#define CLAUSE_d_lrank(c) ((c).u.cl.d_lrank)
#define CLAUSE_p_rank(c)  ((c).u.cl.p_rank)
#define SET_CLAUSE_s_lrank(c,r) (((c).u.cl.s_lrank) = (r))
#define SET_CLAUSE_d_lrank(c,r) (((c).u.cl.d_lrank) = (r))
#define SET_CLAUSE_p_rank(c,r)  (((c).u.cl.p_rank) = (r))

#define CLAUSE_s_grank(c) globrank(CLAUSE_size(c),CLAUSE_s_lrank(c))
#define CLAUSE_d_grank(c) globrank(CLAUSE_size(c),CLAUSE_d_lrank(c))


void fprint_clause_seq(FILE *fp,CLAUSESEQ clause_seq)
{
    int cs_length = CLAUSESEQ_n_clauses(clause_seq);
    int i;

    fprintf(fp,"c%u",CLAUSESEQ_binexp(clause_seq));

    for(i=1; i <= cs_length; i++)
     {
       fprintf(fp,"__%u_%u_%u_%u",
               CLAUSE_size(CLAUSESEQ_nthclause(clause_seq,i)),
               CLAUSE_s_lrank(CLAUSESEQ_nthclause(clause_seq,i)),
               CLAUSE_d_lrank(CLAUSESEQ_nthclause(clause_seq,i)),
               CLAUSE_p_rank(CLAUSESEQ_nthclause(clause_seq,i))
              );
     }
}



CLAUSESEQ clause_seq_copy(CLAUSESEQ dst_clause_seq,CLAUSESEQ src_clause_seq,int max_clauses)
{
    int cs_size = (1+CLAUSESEQ_n_clauses(src_clause_seq));

    if(cs_size >= max_clauses)
     {
       fprintf(stderr,
                "clause_seq_copy: The size of src_clause_seq (%u) >= max_clauses (%u)\n",
                cs_size,max_clauses
              );
       fprint_clause_seq(stderr,src_clause_seq);
       fprintf(stderr,"\n");
       exit(1);
     }
    else
     {
       memcpy(dst_clause_seq,src_clause_seq,(sizeof(CLAUSE)*cs_size));
       return(dst_clause_seq);
     }
  }


CLAUSESEQ clause_seq_dup(CLAUSESEQ clause_seq)
{
    int cs_size = (1+CLAUSESEQ_n_clauses(clause_seq));

    CLAUSESEQ dup_seq = ((CLAUSESEQ) calloc(cs_size,sizeof(CLAUSE)));

    if(NULL == dup_seq)
     {
       fprintf(stderr,
                "clause_seq_dup: couldn't allocate %u bytes for duplicating the clause:\n",
                (cs_size*sizeof(CLAUSE))
              );
       fprint_clause_seq(stderr,clause_seq);
       fprintf(stderr,"\n");
       exit(1);
     }
    else
     {
       memcpy(dup_seq,clause_seq,(sizeof(CLAUSE)*cs_size));
       return(dup_seq);
     }
}


/* A057548(n) = A069770(A072795(n)).   A072795(n) = n + A000108(A072643(n)) = n + A000108(size) */
/* A072795's complement is A081291. */
/* A086433(n) = A082853(A085169(A081291(n))). */

/* Note that:
   grank(lrank) = 0, if size=0, otherwise
   grank(lrank) = lrank+A014137(size-1)

   lrank(grank) = 0, if size=0, otherwise
   lrank(grank) = grank-A014137(size-1)

   What expression
    A069770((gloff1+lrank)+A000108(size)) - gloff2
   essentially does, is to cons a () to the front
   of S-expr tree (i.e. graft the original binary tree
   as a right-hand-side of a new \/ root), and
   then swap the sides, so that the original tree
   ends at the the left side.
 */

int compute_new_lrank_for_A123694(SSIZE size,SLRANK lrank)
{
    if(0 == size) { return(0); }
    else
     {
       int gloff1 = A014137(size-1); /* Glob.offset for the orig size tree */
       int gloff2 = A014137(size);   /* and for one vertex larger one. */
       return(A069770((gloff1+lrank)+A000108(size)) - gloff2);
     }
}


CLAUSESEQ clause_seq_A123694(CLAUSESEQ clause_seq)
{
    CLAUSESEQ dup_seq = clause_seq_dup(clause_seq);

    int cs_length = CLAUSESEQ_n_clauses(dup_seq);
    int i;

    for(i=1; i <= cs_length; i++)
     {
       CLAUSE *cp = &(CLAUSESEQ_nthclause(dup_seq,i));
       SSIZE sz = CLAUSE_size(*cp);
       SET_CLAUSE_size(*cp,sz+1);
       SET_CLAUSE_s_lrank(*cp,compute_new_lrank_for_A123694(sz,CLAUSE_s_lrank(*cp)));
       SET_CLAUSE_d_lrank(*cp,compute_new_lrank_for_A123694(sz,CLAUSE_d_lrank(*cp)));
       /* CLAUSE_p_rank(*cp) stays same. */
     }

    return(dup_seq);
}


PERMRANK A153880(PERMRANK n) /* Shift factorial expansion one digit left. */
{
   PERMRANK z,i;

   for(i=2, z=0; (0 != n); i++)
    {
      z += A000142(i)*(n%i);
      n /= i;
    }

   return(z);
}

/* For the cdr-case the new src tree and dst tree ranks stay same,
   and we need just to recompute the new permutation rank:
 */
CLAUSESEQ clause_seq_A153834(CLAUSESEQ clause_seq)
{
    CLAUSESEQ dup_seq = clause_seq_dup(clause_seq);

    int cs_length = CLAUSESEQ_n_clauses(dup_seq);
    int i;

    for(i=1; i <= cs_length; i++)
     {
       CLAUSE *cp = &(CLAUSESEQ_nthclause(dup_seq,i));
       SSIZE sz = CLAUSE_size(*cp);
       SET_CLAUSE_size(*cp,sz+1);
       /* CLAUSE_s_lrank(*cp) and CLAUSE_d_lrank(*cp) stay same. */
       SET_CLAUSE_p_rank(*cp,A153880(CLAUSE_p_rank(*cp)));
     }

    return(dup_seq);
}


/*
%
%  Clause-representation of a non-recursive Catalan automorphism is a
%  sequence of zero or more "clauses" followed by a default clause.
%
%
%  Viewed combinatorially, a clause of n opening conses consists of
%  a pair of rooted plane binary trees (both with n internal nodes),
%  of which the other one is unlabeled, and the other one's terminal
%  nodes are labeled. The sequence A089835(n) = (A000108(n)^2)*(n+1)!
%  gives the number of such clauses.
%
%  For each non-recursive Catalan automorphism there exists
%  the unique minimal clause-representation, which from all
%  the possible clause-representations of that automorphism
%  is the "least" clause sequence, where the total order
%  of clause sequences is defined by the following rules:
%
%   A) All the clause sequences have an associated integer
%      (see the macro CLAUSESEQ_binexp), whose binary expansion's
%      run lengths determine the number of clauses and their sizes.
%      Of two clause sequences with differing values for this
%      integer, the one with smaller value, is also "less than"
%      in this context. The run lenghs of the least significant
%      end of the binary expansion correspond to the sizes of
%      the most significant clauses, and vice versa.
%
%      E.g. from 103, whose binary expansion is 1100111
%      we get clauses of sizes 3, 2 and 2, from the most
%      significant to the least signicant clause.
%      Similarly, from 124, whose binary expansion is 1111100,
%      we get two clauses, the more significant, with
%      binary trees of 2 internal nodes, and the less
%      significant, with binary trees of 5 internal nodes.
%
%   B) The "most distinguishing clause" of a clause sequence
%      in relation to the other clause sequence of the same
%      size, is the most significant clause, which differs from
%      the corresponding clause in the other clause sequence.
%      Here the most significant clause means the clause which is
%      executed first, the least significant being the one which
%      is applied last, before the default identity clause,
%      in case none of the previous, "more significant" clauses
%      matched. If there is no such dinstinguishing clause,
%      then the two clause sequences are identical.
%
%   C) If the above conditions cannot determine the relation
%      of two clause sequences (in this total order)
%      then the "lesser" clause sequence is the one where the
%      source binary tree used in the most distinguishing clause
%      is nearer to the beginning of the sequence A014486.
%      (I.e. lexicographically less by as determined by the
%       established ordering of unlabeled rooted plane binary trees).
%
%   D) If the above conditions cannot determine the relation
%      of two clause sequences in this total order
%      then the "lesser" clause sequence is the one where the
%      destination binary tree of the most distinguishing clause
%      is lexicographically "less", as determined by the sequence A014486.
%
%   E) If the above conditions cannot determine the relation
%      of two clause sequences in this total order
%      then the "lesser" clause sequence is the one where the
%      the permutation used in the destination binary tree
%      of the most distinguishing clause is the least one as
%      ordered by the sequence A060118.
%      (Note that this differs from the established "lexicographic"
%       orderings of permutations, like used in A030299 and A055089).

%
%  Note added January 3 2009 by AK:
%
%   Most of the times each clause in a minimal clause-representation is
%   an element of Thompson's group V.
%   However, there are cases where some of the non-ultimate clauses
%   will not correspond to an element of Thompson's V in its _minimal_ form.
%   (E.g. consider a non-recursive automorphism (*A154126) which swaps the left
%    and right hand side of the tree only if the other one is ().
%    In that case the first clause is a "non-minimal fixer".)
%
%   For more info, see:
%    J. W. Cannon, W. J. Floyd, and W. R. Parry,
%    Introductory notes on Richard Thompson's groups,
%    L'Enseignement Mathematique, Vol. 42 (1996), pp. 215--256.
%

 */

typedef ULLI FILTERMASK;

#define FILTER_IF_NONULTIMATE_1S   two_to(0)
#define FILTER_LONE_NONSTANDALONES two_to(1)

#define contains(mask,bit) ((mask) & (bit))

/* Tries to increment clause's field one by one,
   and returns 0 if it wrapped around back to zero.
 */
int increment_clause(CLAUSE *cp)
{
    int s = CLAUSE_size(*cp);

    if((++(CLAUSE_p_rank(*cp))) < A000142(s+1)) { return(1); }
    SET_CLAUSE_p_rank(*cp,0);

    if((++(CLAUSE_d_lrank(*cp))) < A000108(s)) { return(1); }
    SET_CLAUSE_d_lrank(*cp,0);

    if((++(CLAUSE_s_lrank(*cp))) < A000108(s)) { return(1); }
    SET_CLAUSE_s_lrank(*cp,0);

    return(0);
}


/* Note that this should be used only on clause sequences with enough extra
   CLAUSE-structures reserved in the end, because the clause sequence
   can here effectively grow in length.
   (e.g when binexp changes from 15 to 16,
    it grows in length from 1 to 2 clauses.)
 */
int clause_seq_next_composition(CLAUSESEQ clause_seq,FILTERMASK filmask)
{
    int org_binexp,binexp,i,c,prevbit;

do_it_again:
    org_binexp = binexp = ++(CLAUSESEQ_binexp(clause_seq));
    i=0;
    c=0;
    prevbit = (binexp & 1);

    /* Compute the runcounts of new binexp, to get another
       composition (an ordered partition):
     */
    while(0 != binexp)
     {
       c++;
       binexp >>= 1;
       if((binexp & 1) != prevbit)
        {
          if(contains(filmask,FILTER_IF_NONULTIMATE_1S) && (0 != binexp) && (1 != org_binexp) && (1 == c))
           { goto do_it_again; }

          SET_CLAUSE_size(CLAUSESEQ_nthclause(clause_seq,++i),c);     
          SET_CLAUSE_s_lrank(CLAUSESEQ_nthclause(clause_seq,i),0);
          SET_CLAUSE_d_lrank(CLAUSESEQ_nthclause(clause_seq,i),0);
          SET_CLAUSE_p_rank(CLAUSESEQ_nthclause(clause_seq,i),0);
          c = 0;
          prevbit = (1-prevbit);
        }
     }

    CLAUSESEQ_n_clauses(clause_seq) = i;

    return(i);
}

/* Increment clauses with an odometer-principle, from right to left: */

int clause_seq_next(CLAUSESEQ clause_seq,FILTERMASK filmask)
{
    int cs_length = CLAUSESEQ_n_clauses(clause_seq);
    int i;

    for(i= cs_length; i > 0; i--)
     {
       CLAUSE *cp = &(CLAUSESEQ_nthclause(clause_seq,i));
       if(increment_clause(cp))
        {
          if(contains(filmask,FILTER_LONE_NONSTANDALONES) && (1 == cs_length)
              && (CLAUSE_s_lrank(*cp) != CLAUSE_d_lrank(*cp))
            )
           {
/* When d_rank has incremented past s_rank (means p_rank is 0),
   then set s_rank to be equal to d_rank, if we are filtering off
   lone nonstandalones already at this stage:
 */
             CLAUSE_s_lrank(*cp) = CLAUSE_d_lrank(*cp);
           }

          return(i);
	}
       /* Otherwise, a clause wrapped around, so let's continue
          incrementing clauses to the left. */
     }

    /* If we fall from the above loop, it means that ALL clauses
       have wrapped around to zero, so now it's time to
       get the next composition, i.e. to increment the binexp
       of the clause sequence:
     */
    clause_seq_next_composition(clause_seq,filmask);

    return(i);
}


/**********************************************************************/
/**********************************************************************/

/* 
;; The following algorithm is a slight modification of unrank1
;; algorithm as presented by W. Myrvold and F. Ruskey, in
;; Ranking and Unranking Permutations in Linear Time,
;; Inform. Process. Lett. 79 (2001), no. 6, 281-284.
;; Available on-line: http://www.cs.uvic.ca/~fruskey/Publications/RankPerm.html


(define (permute-A060118 elems size permrank)
  (let ((p (vector-head elems size)))
    (let unrankA060118 ((r permrank)
                        (i 1)
                       )
          (cond ((zero? r) p)
                (else
                   (let* ((j (1+ i))
                          (m (modulo r j))
                         )
                      (cond ((not (zero? m)) ;; Swap at i and (i-(r mod (i+1)))
                                (let ((org-i (vector-ref p i)))
                                   (vector-set! p i (vector-ref p (- i m)))
                                   (vector-set! p (- i m) org-i)
                                )
                            )
                      )
                      (unrankA060118 (/ (- r m) j) j)
                   )
                )
          )
    )
  )
)
 */

void reverse_n_vectors(USI **vecs,int n_vecs)
{
    int i,j;

    for(i=0,j=n_vecs-1; i < j; i++, j--)
     {
       USI *tmp = vecs[i];
       vecs[i] = vecs[j];
       vecs[j] = tmp;
     }
}

/*

The following in effect uses the same algorithm A060118.
Note that in the loop we set m to be the ith least significant digit (1-based)
in original permrank's factorial expansion.

 */

int select_transposition_vectors(USI **res,USI **transp_vecs,int permrank)
{
    int vecs_needed=0;
    int i,m;

    for(i=1; (permrank != 0); transp_vecs += i, i++)
     {
       m = (permrank % (i+1));
       if(0 != m) { res[vecs_needed++] = transp_vecs[m-1]; }
       permrank = (permrank - m)/(i+1);
     }

    return(vecs_needed);
}


/* The maximum number of vectors that we might be selected here is tree_size+2.
   Thus there must be at least tree_size+3 pointers of space in res.
   Note that clause's tree_size cannot be more than upto_size_n
   (the second parameter of the command line), otherwise the references
   to all_vecs will overflow.
 */

int select_vectors_needed(USI **res,USI ***all_vecs,int tree_size,LRANK s_rank,LRANK d_rank,int permrank)
{
    int vecs_needed=0;

    USI **transp_vecs = all_vecs[2*(tree_size-1)];
    USI **transform_vecs = all_vecs[(2*(tree_size-1))+1];

/*  The first optimization: use transform1 only when
    either s_rank is not zero,
    OR when ALL ranks are zeroes.
    The latter because we need in that case at least
    one vector reference to know whether the computed
    tree is a super-tree of the tree corresponding
    to s_rank and d_rank, i.e. the right comb:
 */
    if((0 != s_rank)
       ||
       ((0 == permrank) && (0 == d_rank))
      )
     {
       res[vecs_needed++] = transform_vecs[(2*s_rank)]; /* transform1 vectors on even indices. */
     }

    vecs_needed += select_transposition_vectors(res+vecs_needed,transp_vecs,permrank);
 /* The second "optimization":
    We don't need transform2 when destination tree is the right comb.
  */
    if(0 != d_rank)
     {
       res[vecs_needed++] = transform_vecs[(2*d_rank)+1]; /* transform2 vectors on odd indices. */
     }

    res[vecs_needed++] = NULL; /* As an end marker. */

    return(vecs_needed); /* Return one more than the number of vecs needed, because of ending NULL. */
}



/* In essence, the inverse of the clause sequence
    ((s1,d1,p1), (s2,d2,p2), ..., (sn,dn,pn))
   is the clause sequence:
    ((d1,s1,A060125(p1)), (d2,s2,A060125(p2)), ..., (dn,sn,A060125(pn)))

   (where the triplet (si,di,pi) indicates the source tree, destination tree
   and permutation ranks of the ith clause)

   but because I don't care to code A060125 in C
   (unless I find a more elegant algorithm for it)
   I instead here simply swap s and d, and reverse the
   order of transposition vectors selected:

 */

int select_vectors_for_inverse(USI **res,USI ***all_vecs,int tree_size,LRANK d_rank,LRANK s_rank,int permrank)
{
    int vecs_needed=0, t_vecs_needed;

    USI **transp_vecs = all_vecs[2*(tree_size-1)];
    USI **transform_vecs = all_vecs[(2*(tree_size-1))+1];

    if((0 != s_rank)
       ||
       ((0 == permrank) && (0 == d_rank))
      )
     {
       res[vecs_needed++] = transform_vecs[(2*s_rank)]; /* transform1 vectors on even indices. */
     }

    t_vecs_needed = select_transposition_vectors(res+vecs_needed,transp_vecs,permrank);
    reverse_n_vectors(res+vecs_needed,t_vecs_needed);

    vecs_needed += t_vecs_needed;

    if(0 != d_rank)
     {
       res[vecs_needed++] = transform_vecs[(2*d_rank)+1]; /* transform2 vectors on odd indices. */
     }

    res[vecs_needed++] = NULL; /* As an end marker. */

    return(vecs_needed); /* Return one more than the number of vecs needed, because of ending NULL. */
}

/* For maximum performance:
   Unroll the loops here, and inline this to a calling function.

   Note: when n_clauses is 0, then it doesn't matter what is the contents
   of clauseseqs_selected_vectors, but instead this will return x intact back,
   as an empty set of clauses correspond to a single default clause,
   that is, an identity function A001477.
 */
SGRANK apply_clauses_to_x(SGRANK x,USI ***clauseseqs_selected_vectors,int n_clauses)
{
    int i=0;
    SGRANK y;
    USI **selected_vectors;

    do
     {
       if(i == n_clauses) /* No clause matched, return x back as a default. */
        {
          return(x);
        }
       selected_vectors = clauseseqs_selected_vectors[i++];
       y = (*selected_vectors)[x]; /* Apply the first vector (transform 1) to x. */
     } while(0 == y);              /* until we find a clause that matches. */

/* Then apply the rest of vecs selected for this (the first matching) clause */
    while(NULL != *++selected_vectors)
     {
       y = (*selected_vectors)[y];
     }

    return(y);
}

/* This compares the the clause_seqs results to another one's results
   (computed with the next one, to_obtain_signature_perm, and placed
   by it to ep->vals_obtained)
   and returns the first point (x) where their values differ
   (Note: x=0 is not checked, as it is assumed to stay always zero).
   and zero if they are equal.
 */
int to_compare_to_another_signature_perm(USI ***clauseseqs_selected_vectors,int n_clauses,ECOTEX *ep)
{
    int t_size;
    LRANK t_lrank;
    SGRANK x;
    SGRANK y;

    for(t_size=1, x=1; t_size <= ep->upto_size_n; t_size++)
     {
       for(t_lrank = 0; t_lrank < Cat(t_size); t_lrank++, x++)
        {
          y = apply_clauses_to_x(x,clauseseqs_selected_vectors,n_clauses);
          if(y != ep->vals_obtained[x]) { return(x); }
	}
     }

    return(0);
}


int to_obtain_signature_perm(USI ***clauseseqs_selected_vectors,int n_clauses,ECOTEX *ep)
{
    int t_size;
    LRANK t_lrank;
    SGRANK x;
    SGRANK y;
    ULLI checksum = 0;

    ep->vals_obtained[0] = 0;

    for(t_size=1, x=1; t_size <= ep->upto_size_n; t_size++)
     {
       for(t_lrank = 0; t_lrank < Cat(t_size); t_lrank++, x++)
        {
          y = apply_clauses_to_x(x,clauseseqs_selected_vectors,n_clauses);
          ep->vals_obtained[x] = y;

          checksum = add_to_checksum(checksum,y);
	}
     }

    ep->checksum = checksum;
    return(1);
}

/* We use this one for the latter, when we want to compute the composition of two clauseseqs,
   as this applies its automorphism onto *the old* values of ep->vals_obtained vector,
   instead of x directly.
 */
int to_obtain_composite_signature_perm(USI ***clauseseqs_selected_vectors,int n_clauses,ECOTEX *ep)
{
    int t_size;
    LRANK t_lrank;
    SGRANK x;
    SGRANK y;
    ULLI checksum = 0;

/* Make a safe copy of the previously computed ep->vals_obtained vector: */
    memcpy(ep->vals_obtained2,ep->vals_obtained,(sizeof(SGRANK)*ep->vec_size));

    ep->vals_obtained[0] = 0;

    for(t_size=1, x=1; t_size <= ep->upto_size_n; t_size++)
     {
       for(t_lrank = 0; t_lrank < Cat(t_size); t_lrank++, x++)
        {
          y = apply_clauses_to_x(ep->vals_obtained2[x],clauseseqs_selected_vectors,n_clauses);
          ep->vals_obtained[x] = y;

          checksum = add_to_checksum(checksum,y);
	}
     }

    ep->checksum = checksum;
    return(1);
}


int to_check_bijectivity(USI ***clauseseqs_selected_vectors,int n_clauses,ECOTEX *ep)
{
    int t_size;
    LRANK t_lrank;
    SGRANK x;
    SGRANK y;
    ULLI checksum = 0;
    SGRANK *vals_obtained = ep->vals_obtained;

    ECOTEX_CLEAR_vals_obtained(ep);

    for(t_size=1, x=1; t_size <= ep->upto_size_n; t_size++)
     {
       for(t_lrank = 0; t_lrank < Cat(t_size); t_lrank++, x++)
        {
          y = apply_clauses_to_x(x,clauseseqs_selected_vectors,n_clauses);
          if(0 == y)
           {
             fprintf(stderr,"to_check_bijectivity: Bad internal error: y=0 for x=%u\n",x);
             exit(1);
           }

          if(0 != (vals_obtained[y])++) /* Not the first time for this value y? */
           {
             ep->bijectivity_broken_at_size_n = t_size; /* Because not injective. */
             ep->clear_next_time_upto_size_n = t_size;
             return(0);
           }

          checksum = add_to_checksum(checksum,y);
	}
     }

    ep->clear_next_time_upto_size_n = ep->upto_size_n;
    ep->checksum = checksum;
    return(1);
}



/* This function obtains the required precomputed vectors from ep->all_vecs
   for each clause in clause_seq,
   and then calls one of the above functions
     to_compare_to_another_signature_perm, to_obtain_signature_perm,
     to_obtain_composite_signature_perm or to_check_bijectivity
   to compute signature permutation values (for various purposes)
   using those selected precomputed vectors.
 */
int compute_clause_seq(CLAUSESEQ_COMPFUN for_what,CLAUSESEQ clause_seq,ECOTEX *ep)
{
    USI *space_for_selected_vectors[MAX_CLAUSES*(MAX_CLAUSE_SIZE+3)]; /* Vector of vectors. */
    USI **ssp = space_for_selected_vectors; /* Pointer to above. */
    USI **clauseseqs_selected_vectors[MAX_CLAUSES+1]; /* Vector of vector of vectors */

    int n_clauses = CLAUSESEQ_n_clauses(clause_seq);
    int i;

    for(i=1; i <= n_clauses; i++)
     {
       clauseseqs_selected_vectors[i-1] = ssp;
       ssp += select_vectors_needed(ssp,ep->all_vecs,
                        CLAUSE_size(CLAUSESEQ_nthclause(clause_seq,i)),
                        CLAUSE_s_lrank(CLAUSESEQ_nthclause(clause_seq,i)),
                        CLAUSE_d_lrank(CLAUSESEQ_nthclause(clause_seq,i)),
                        CLAUSE_p_rank(CLAUSESEQ_nthclause(clause_seq,i))
                                   );
#ifdef DEBUG
       fprint_vector_of_USI_vectors(stdout,clauseseqs_selected_vectors[i-1],A014137(ep->upto_size_n));
#endif
     }

    return(for_what(clauseseqs_selected_vectors,n_clauses,ep));
}


int compute_inverse_of_clause_seq(CLAUSESEQ_COMPFUN for_what,CLAUSESEQ clause_seq,ECOTEX *ep)
{
    USI *space_for_selected_vectors[MAX_CLAUSES*(MAX_CLAUSE_SIZE+3)]; /* Vector of vectors. */
    USI **ssp = space_for_selected_vectors; /* Pointer to above. */
    USI **clauseseqs_selected_vectors[MAX_CLAUSES+1]; /* Vector of vector of vectors */

    int n_clauses = CLAUSESEQ_n_clauses(clause_seq);
    int i;

    for(i=1; i <= n_clauses; i++)
     {
       clauseseqs_selected_vectors[i-1] = ssp;
       ssp += select_vectors_for_inverse(ssp,ep->all_vecs,
                        CLAUSE_size(CLAUSESEQ_nthclause(clause_seq,i)),
                        CLAUSE_s_lrank(CLAUSESEQ_nthclause(clause_seq,i)),
                        CLAUSE_d_lrank(CLAUSESEQ_nthclause(clause_seq,i)),
                        CLAUSE_p_rank(CLAUSESEQ_nthclause(clause_seq,i))
                                        );
#ifdef DEBUG
       fprint_vector_of_USI_vectors(stdout,clauseseqs_selected_vectors[i-1],A014137(ep->upto_size_n));
#endif
     }

    return(for_what(clauseseqs_selected_vectors,n_clauses,ep));
}



/**********************************************************************/

CLAUSESEQ clauseseq_found_in_bucket(CLAUSESEQ clauseseqs_with_same_checksum,CLAUSESEQ *p_to_last,ECOTEX *ep)
{
    static int max_bucklen=0;
    int bucklen=1;

    while(NULL != clauseseqs_with_same_checksum)
     {
       if(0 == compute_clause_seq(to_compare_to_another_signature_perm,clauseseqs_with_same_checksum,ep))
        { return(clauseseqs_with_same_checksum); }

       *p_to_last = clauseseqs_with_same_checksum;
       clauseseqs_with_same_checksum = CLAUSESEQ_next_clauseseq(clauseseqs_with_same_checksum);
       bucklen++;
     }
/* This message is not printed until after we get the first automorphism
   with the same hash table index as a previously encountered,
   but different automorphism:
 */
    if(bucklen > max_bucklen)
     {
       max_bucklen = bucklen;
       fprintf(stderr,"clauseseq_found_in_bucket: maximum bucket length of the hash table will/might soon be: %u\n", max_bucklen);
     }

    return(NULL); /* Didn't find it! */
}


/* Returns the first previously encountered CLAUSESEQ of which
   clause_seq is a duplicate of, or if it is so far unique,
   then add it to a hash table, and return NULL.
 */
CLAUSESEQ duplicate_found_in_hashtable(CLAUSESEQ clause_seq,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep,CLAUSESEQ *p_to_stored_one,int compute_signature_perm_in_any_case)
{
    int hindex;
    CLAUSESEQ dup,last_in_bucket;

    if(compute_signature_perm_in_any_case)
     {
       compute_clause_seq(to_obtain_signature_perm,clause_seq,ep);
     }

    hindex = (ep->checksum % hashsize);
    if(NULL == hashtable[hindex]) /* The very first one for this index. */
     {
       CLAUSESEQ_next_clauseseq(clause_seq) = NULL; /* Should be already! */
       hashtable[hindex] = clause_seq_dup(clause_seq);
       if(NULL != p_to_stored_one) { *p_to_stored_one = hashtable[hindex]; }
       return(NULL);
     }

/* Else, we have to check whether it produces *really* the same sequence
   as one of the clause sequences in this bucket.
   So, first, obtain the signature permutation for this
   clause sequence (in case it has not already been computed above,
   and stored in ep->vals_obtained):
 */
    if(!compute_signature_perm_in_any_case)
     {
       compute_clause_seq(to_obtain_signature_perm,clause_seq,ep);
     }

    dup = clauseseq_found_in_bucket(hashtable[hindex],&last_in_bucket,ep);

/* Didn't find a duplicate, so add this new one to the end of the list: */
    if(NULL == dup)
     {
       CLAUSESEQ tmp;

       CLAUSESEQ_next_clauseseq(clause_seq) = NULL; /* Should be already! */
       CLAUSESEQ_next_clauseseq(last_in_bucket) = tmp = clause_seq_dup(clause_seq);
       if(NULL != p_to_stored_one) { *p_to_stored_one = tmp; }
     }

    return(dup);
}

CLAUSESEQ composition_found_in_hashtable(CLAUSESEQ clause_seq1,CLAUSESEQ clause_seq2,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep)
{
    int hindex;
    CLAUSESEQ last_in_bucket; /* Not used here, but clauseseq_found_in_bucket expects it anyway. */

    compute_clause_seq(to_obtain_signature_perm,clause_seq1,ep);
    compute_clause_seq(to_obtain_composite_signature_perm,clause_seq2,ep);

    hindex  = (ep->checksum % hashsize);

    if(NULL == hashtable[hindex]) /* The very first one for this index? So composition is not among the so-far computed. */
     {
       return(NULL);
     }

/* Else, we check whether the compositions produces really
   the same sequence as one of the clause sequences in this bucket:
 */

    return(clauseseq_found_in_bucket(hashtable[hindex],&last_in_bucket,ep));
}


CLAUSESEQ inverse_found_in_hashtable(CLAUSESEQ clause_seq1,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep)
{
    int hindex;
    CLAUSESEQ last_in_bucket; /* Not used here, but clauseseq_found_in_bucket expects it anyway. */

    compute_inverse_of_clause_seq(to_obtain_signature_perm,clause_seq1,ep);

    hindex  = (ep->checksum % hashsize);

    if(NULL == hashtable[hindex]) /* The very first one for this index? So the inverse is not among the so-far computed. */
     {
       return(NULL);
     }

/* Else, we check that the inverse produces really
   the same sequence as one of the clause sequences in this bucket:
 */
    return(clauseseq_found_in_bucket(hashtable[hindex],&last_in_bucket,ep));
}



/* The main loop is here!
   We start from an identity automorphism of no clauses but the implicit default.

   Here are the 50 A-numbers you requested: 89831 --- 89880.

 */
int check_upto_binexp_n(int upto_binexp_n,ECOTEX *ep,
                        int hashsize,CLAUSESEQ *hashtable,CLAUSESEQ *first_clauseseqs,FILTERMASK filmask,
                        int misc_seq_size,int misc_table_size,int max_order_tested_to,
                        int search_nondecomposables_upto_n,
                        ULLI *A089832,ULLI *A089831,
                        NORERANK *A089839,SGRANK *A089840,NORERANK *misc_seq_vec,
                        CLAUSESEQ front_clause_searched)
{
    int max_bijectivity_broken_at_size_n=0;
    int prev_binexp = 0, prev_n_clauses = 0, prev_tot_size = 0;
    int row,i;
    ULLI bijections=0, distinct_bijections_among_this_size=0, distinct_bijections=0, duplicates=0;
    CLAUSE clause_seq[MAX_CLAUSES+1];
    CLAUSE last_distinct_clauseseq[MAX_CLAUSES+1] = {0};
    CLAUSESEQ dupe = NULL;

    int counterA153826=0, counterA153827=0, counterA153828=0,
        counterA153829=0, counterA153830=0, counterA153831=0;

    prev_binexp = CLAUSESEQ_n_clauses(clause_seq) = CLAUSESEQ_binexp(clause_seq) = 0;

    ECOTEX_CLEAR_all_vals_obtained(ep);

    do
     {
/*     fprint_clause_seq(stdout,clause_seq); printf(" in the top of the loop!\n"); fflush(stdout); */

       if(compute_clause_seq(to_check_bijectivity,clause_seq,ep))
        {
          CLAUSESEQ copied_one = NULL;

/*        fprint_clause_seq(stdout,clause_seq); printf(" is a bijection\n"); fflush(stdout); */

          bijections++;
          dupe = duplicate_found_in_hashtable(clause_seq,hashtable,hashsize,ep,
                                              &copied_one, /* If was not duplicate, i.e. if dupe is NULL. */
                                              0); /* No need for signature perm, as long as the bucket is empty. */
          if(NULL == dupe) /* equal to: (NULL != copied_one) */
           {

             if(distinct_bijections < misc_seq_size)
              {
                first_clauseseqs[distinct_bijections] = copied_one;
	      }

             SET_CLAUSESEQ_norerank(copied_one,distinct_bijections); /* Set its rank in A089840. */

             clause_seq_copy(last_distinct_clauseseq,copied_one,MAX_CLAUSES);


             if(globopt_output_invariance_indices)
              {
                /* Get the sigperm to ep->vals_obtained: */
                compute_clause_seq(to_obtain_signature_perm,clause_seq,ep);

                if(0 == check_invariance(sA127301_up_to6917,ep))
                 {
                   fprintf(fpA153826,"# A089840[%u]: ",distinct_bijections);
                   fprint_clause_seq(fpA153826,copied_one);
                   fprintf(fpA153826,"\n%u %u\n",
                           counterA153826,distinct_bijections);
                   fflush(fpA153826);
                   counterA153826++;
                 }

                if(0 == check_invariance(sA129593_up_to6917,ep))
                 {
                   fprintf(fpA153827,"# A089840[%u]: ",distinct_bijections);
                   fprint_clause_seq(fpA153827,copied_one);
                   fprintf(fpA153827,"\n%u %u\n",
                           counterA153827,distinct_bijections);
                   fflush(fpA153827);
                   counterA153827++;
                 }

                /* Set-wise difference of the above two: */
                if((0 == check_invariance(sA129593_up_to6917,ep))
                   &&
                   (0 != check_invariance(sA127301_up_to6917,ep))
                  )
                 {
                   fprintf(fpA153828,"# A089840[%u]: ",distinct_bijections);
                   fprint_clause_seq(fpA153828,copied_one);
                   fprintf(fpA153828,"\n%u %u\n",
                           counterA153828,distinct_bijections);
                   fflush(fpA153828);
                   counterA153828++;
                 }

                if(0 == check_invariance(sA153835_up_to6917,ep))
                 {
                   fprintf(fpA153829,"# A089840[%u]: ",distinct_bijections);
                   fprint_clause_seq(fpA153829,copied_one);
                   fprintf(fpA153829,"\n%u %u\n",
                           counterA153829,distinct_bijections);
                   fflush(fpA153829);
                   counterA153829++;
                 }

                if(0 == check_budding_invariance(ep))
                 {
                   fprintf(fpA153830,"# A089840[%u]: ",distinct_bijections);
                   fprint_clause_seq(fpA153830,copied_one);
                   fprintf(fpA153830,"\n%u %u\n",
                           counterA153830,distinct_bijections);
                   fflush(fpA153830);
                   counterA153830++;
                 }

                /* Set-wise difference of the above two: */
                if((0 == check_invariance(sA153835_up_to6917,ep))
                  &&
                   (0 != check_budding_invariance(ep))
                  )
                 {
                   fprintf(fpA153831,"# A089840[%u]: ",distinct_bijections);
                   fprint_clause_seq(fpA153831,copied_one);
                   fprintf(fpA153831,"\n%u %u\n",
                           counterA153831,distinct_bijections);
                   fflush(fpA153831);
                   counterA153831++;
                 }

              }


 /* This if used for searching clause seqs with a particular user-supplied
    front clause: */
             if((NULL != front_clause_searched) && (distinct_bijections > 0))
              {
                CLAUSE cl1 = CLAUSESEQ_nthclause(front_clause_searched,0);
                CLAUSE cl2 = CLAUSESEQ_nthclause(copied_one,1);

                if((CLAUSE_size(cl1) == CLAUSE_size(cl2))
                    &&
                   (CLAUSE_s_lrank(cl1) == CLAUSE_s_lrank(cl2))
                    &&
                   (CLAUSE_d_lrank(cl1) == CLAUSE_d_lrank(cl2))
                    &&
                   (CLAUSE_p_rank(cl1) == CLAUSE_p_rank(cl2))
                  )
                 {
                   fprintf(stdout,"Front-clause matches (A089840[%u]): ",
                                  distinct_bijections);
                   fprint_clause_seq(stdout,copied_one);
                   fprintf(stdout,"\n");
                   fflush(stdout);
                 }
              }

/* If the fourth argument misc_table_size was specified on the command line,
   then we are collecting  from the first misc_table_size distinct bijections
   their signature permutations, to the square array A089840:
 */
             if((NULL != A089840) && (distinct_bijections < misc_table_size))
              {
                compute_clause_seq(to_obtain_signature_perm,copied_one,ep);

                for(i=0; i < (misc_table_size-distinct_bijections); i++)
                 {
                   A089840[ar2seqind(distinct_bijections,i)] = (SGRANK) ep->vals_obtained[i];
                 }

                ECOTEX_CLEAR_all_vals_obtained(ep);
              }


             distinct_bijections_among_this_size++;
             distinct_bijections++; /* In total. */
           }
          else
           {
             duplicates++;
#ifdef DEBUG
             fprint_clause_seq(stdout,clause_seq);
             fprintf(stdout," (%lx -> %u) is a duplicate of ",ep->checksum,(ep->checksum % hashsize));
             fprint_clause_seq(stdout,dupe);
             fprintf(stdout,"\n");
#endif
           }
        }

       if(ep->bijectivity_broken_at_size_n > max_bijectivity_broken_at_size_n)
        {
          fprintf(stdout,"New record for bijectivity_broken_at (%u) occurred with the clause seq: ",
		 ep->bijectivity_broken_at_size_n);
          fprint_clause_seq(stdout,clause_seq);
          fprintf(stdout,"\n");
          max_bijectivity_broken_at_size_n = ep->bijectivity_broken_at_size_n;
        }

       clause_seq_next(clause_seq,filmask);
/*
       fprint_clause_seq(stdout,clause_seq); printf(" is the next clause seq.\n"); fflush(stdout);
 */

       if(CLAUSESEQ_binexp(clause_seq) != prev_binexp)
        {
          int i;
          int tot_size = binwidth(prev_binexp);
          printf("c%u*: ",prev_binexp);
          fprint_ulli(stdout,bijections);
          printf(" ");
          fprint_ulli(stdout,distinct_bijections_among_this_size);
          printf("\n"); fflush(stdout);

          A089832[tot_size] += distinct_bijections_among_this_size;

          if(tot_size > 0)
           {
             A089831[tr2seqind11(tot_size,prev_n_clauses)]
                 += distinct_bijections_among_this_size;
           }

          if(tot_size != prev_tot_size)
           {
             printf("A089832[%u]=",prev_tot_size); fflush(stdout);
             fprint_ulli(stdout,A089832[prev_tot_size]);
             printf(": "); fflush(stdout);
             for(i=1; i <= prev_tot_size; i++)
              {
                printf(" ");
                fprint_ulli(stdout,A089831[tr2seqind11(prev_tot_size,i)]);
              }
             printf("\nduplicates so far: ");
             fprint_ulli(stdout,duplicates);
             printf("\n"); fflush(stdout);

             prev_tot_size = tot_size;
           }

          distinct_bijections_among_this_size = bijections = 0;
          prev_binexp = CLAUSESEQ_binexp(clause_seq);
          prev_n_clauses = CLAUSESEQ_n_clauses(clause_seq);
        }
     } while(CLAUSESEQ_binexp(clause_seq) <= upto_binexp_n); /* End of the main loop. */

    for(row=1; row <= binwidth(upto_binexp_n); row++)
     {
       printf("A089832[%u]=",row);
       fprint_ulli(stdout,A089832[row]);
       printf(": ");
       for(i=1; i <= row; i++)
        {
          if(i > 1) { printf(","); }
          fprint_ulli(stdout,A089831[tr2seqind11(row,i)]);
        }
       printf("\n");
     }

    globopt_list_begin = "";
    globopt_list_end   = "\n";

    printf("max_bijectivity_broken_at_size_n=%u\n",
            max_bijectivity_broken_at_size_n);

    printf("duplicates in total: ");
    fprint_ulli(stdout,duplicates);
    printf("\n"); fflush(stdout);

    printf("Last distinct clause sequence found at the index %lu\n", CLAUSESEQ_norerank(last_distinct_clauseseq));
    fprint_clause_seq(stdout,last_distinct_clauseseq);
    printf("\n"); fflush(stdout);


    output_OEIS_sequence(stdout,89831,A089831,A000217(binwidth(upto_binexp_n)),
                         VECTYPE_ULLI,(PF_VEC_OUT)fprint_ULLI_vector,1,OEIS_TABLE,
                         "The triangle T(n,m) read as T(1,1); T(2,1), T(2,2); T(3,1), T(3,2), T(3,3); ... Number of distinct non-recursive Catalan automorphisms of total n opened nodes, divided into m non-default clauses.");

    output_OEIS_sequence(stdout,89832,A089832,binwidth(upto_binexp_n)+1,
                         VECTYPE_ULLI,(PF_VEC_OUT)fprint_ULLI_vector,0,OEIS_SEQ,
                         "Number of distinct non-recursive Catalan automorphisms of total n opened nodes. Row sums of A089831.");

/*
    The first column of A089831: A089833 =  (Cat(n)*((n+1)!-1)) = A001813[n]-A000108[n]
    0,1,10,115,1666,30198,665148,17296851,518916970,... (not in OEIS)

    A089834 = A089832-A089833, the row sums of A089831 excluding the first column.

    A089835= Cat(n)*Cat(n)*(n+1)! (= A001246[n]*A000142[n+1] = A001813[n]*A000108[n])
    1,2,24,600,23520,1270080,87816960,7420533120,742053312000 (not in EIS)
    = number of clauses of tree size n. (Offset 0).

    A089836 = INVERT(A089835) = INVERT([seq(Cat(n)*Cat(n)*(n+1)!,n=1..9)]);
    [2,28,704,26800,1404416,94890112,7887853568,779773444864,89407927009280,...]


 */

    if(misc_table_size > 0) /* E.g. (NULL != A089840) */
     {
       int antidiagonal,other;

       output_OEIS_sequence(stdout,89840,A089840,A000217(misc_table_size),
                            VECTYPE_USI,(PF_VEC_OUT)fprint_USI_vector,0,OEIS_TABLE,
 "The signature permutations of non-recursive Catalan automorphisms, sorted according to the minimum number of opening nodes needed in their defining clauses."
                           );


       for(antidiagonal=0, i=0; antidiagonal < misc_table_size; antidiagonal++)
        {
          for(other=0; other <= antidiagonal; other++)
           {
/*           printf("Composition A089840[%u] o A089840[%u] = ",other,(antidiagonal-other)); */
             CLAUSESEQ comp = composition_found_in_hashtable(first_clauseseqs[(antidiagonal-other)],first_clauseseqs[other],hashtable,hashsize,ep);
             A089839[i++] = ((NULL == comp) ? NA_SENTINEL : CLAUSESEQ_norerank(comp));
           }
        }
       
       output_OEIS_sequence(stdout,89839,A089839,A000217(misc_table_size),
                            VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,0,OEIS_TABLE,
 "The composition table T(n,m): ... of the nth and mth automorphisms in the table A089840."
                           );
     }

/* Compute the involutions A089837 & A089838. */
    if(misc_seq_size > 1)
     {
       int i,j,n;
       for(i=0; i < misc_seq_size; i++)
        {
          CLAUSESEQ comp = composition_found_in_hashtable(first_clauseseqs[i],first_clauseseqs[1],hashtable,hashsize,ep);
          misc_seq_vec[i] = ((NULL == comp) ? NA_SENTINEL : CLAUSESEQ_norerank(comp));
        }
       output_OEIS_sequence(stdout,89838,misc_seq_vec,misc_seq_size,
                            VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,0,OEIS_SEQ,
                           "The row 1 of A089839."
                           );

       for(i=0; i < misc_seq_size; i++)
        {
          CLAUSESEQ comp = composition_found_in_hashtable(first_clauseseqs[1],first_clauseseqs[i],hashtable,hashsize,ep);
          misc_seq_vec[i] = ((NULL == comp) ? NA_SENTINEL : CLAUSESEQ_norerank(comp));
        }
       output_OEIS_sequence(stdout,89837,misc_seq_vec,misc_seq_size,
                            VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,0,OEIS_SEQ,
                           "The column 1 of A089839."
                           );

       for(i=0; i < misc_seq_size; i++)
        {
          CLAUSESEQ comp = composition_found_in_hashtable(first_clauseseqs[i],first_clauseseqs[i],hashtable,hashsize,ep);
          misc_seq_vec[i] = ((NULL == comp) ? NA_SENTINEL : CLAUSESEQ_norerank(comp));
        }
       output_OEIS_sequence(stdout,89841,misc_seq_vec,misc_seq_size,
                            VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,0,OEIS_SEQ,
                            "The main diagonal of A089839." /* Should be A089839(A089837(n),A089838(n)) or vice versa? */
                           );

/*
   We could compute the position of each one's A057163-conjugate, in similar way:
 */
       for(i=0; i < misc_seq_size; i++)
        {
          CLAUSESEQ comp = inverse_found_in_hashtable(first_clauseseqs[i],hashtable,hashsize,ep);
          misc_seq_vec[i] = ((NULL == comp) ? NA_SENTINEL : CLAUSESEQ_norerank(comp));
        }
       output_OEIS_sequence(stdout,89843,misc_seq_vec,misc_seq_size,
                            VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,0,OEIS_SEQ,
                            "Involution of natural numbers which shows the position of the inverse of each non-recursive Catalan automorphism in table A089840"
                           );


       for(i=0; i < misc_seq_size; i++)
        {
          int order=1;
          CLAUSESEQ comp = first_clauseseqs[i];

          do {
               if(comp == first_clauseseqs[0]) { break; }
               comp = composition_found_in_hashtable(comp,first_clauseseqs[i],hashtable,hashsize,ep);
             } while((NULL != comp) && (++order <= max_order_tested_to));

/*        misc_seq_vec[i] = (NORERANK) ((NULL == comp) ? NA_SENTINEL : ((first_clauseseqs[0] == comp) ? order : 0)); */
          misc_seq_vec[i] = (NORERANK) ((first_clauseseqs[0] == comp) ? order : 0);
        }

/* Note: The order of the 15th and 21st elements (A089859 & A089863), should be 4, not infinite!
   I.e. we must compute this with high enough value of upto_binexp_n (127 is recommended).
 */

       output_OEIS_sequence(stdout,89842,misc_seq_vec,misc_seq_size,
                            VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,0,OEIS_SEQ,
                            "The order of each element in A089840, 0 if not finite."
                           );

/* This loop is not very robust. First of all, search_nondecomposables_upto_n should be set
   to some value like 136, 1941 or 34709 (with -s option), i.e. a partial sum of A089832
   starting from offset 1: 1, 10, 125, 1805, 32768, 713930, 18334997, ...
   otherwise the program will crash.
 */

       for(n=0; n <= search_nondecomposables_upto_n; n++)
        {
          int this_size = binwidth(CLAUSESEQ_binexp(first_clauseseqs[n]));
          if(CLAUSESEQ_n_clauses(first_clauseseqs[n]) < 2) { continue; }

/* Why this works? Because the inverse of a nonrecursive automorphism has
   clause sequence of the same size. */
          for(i=1; binwidth(CLAUSESEQ_binexp(first_clauseseqs[i])) < this_size; i++)
           {
             CLAUSESEQ comp = composition_found_in_hashtable(first_clauseseqs[i],first_clauseseqs[n],hashtable,hashsize,ep);
             if(comp && (binwidth(CLAUSESEQ_binexp(comp)) < this_size))
              {
                printf("A089840[%u] = A089840[%u] o A089840[%u] = ",CLAUSESEQ_norerank(comp),n,i);
                fprint_clause_seq(stdout,comp); printf(" = ");
                fprint_clause_seq(stdout,first_clauseseqs[n]); printf(" o ");
                fprint_clause_seq(stdout,first_clauseseqs[i]); printf("\n");
                goto try_next;
              }
/*
             CLAUSESEQ comp = composition_found_in_hashtable(first_clauseseqs[n],first_clauseseqs[i],hashtable,hashsize,ep);
             if(comp && (binwidth(CLAUSESEQ_binexp(comp)) < this_size))
              {
                printf("A089840[%u] = A089840[%u] o A089840[%u] = ",CLAUSESEQ_norerank(comp),i,n);
                fprint_clause_seq(stdout,comp); printf(" = ");
                fprint_clause_seq(stdout,first_clauseseqs[i]); printf(" o ");
                fprint_clause_seq(stdout,first_clauseseqs[n]); printf("\n");
                goto try_next;
              }
 */
           }
          /* If we fall from those two loops here, we have found a "nondecomposable" automorphism.
             (i.e. not composable of two automorphisms of the same or smaller size).
           */
          printf("NONDECOMPOSABLE MULTICLAUSE: A089840[%u] = ",n);
          fprint_clause_seq(stdout,first_clauseseqs[n]); printf("\n");
          fflush(stdout);
try_next: ;
        }
       
       output_OEIS_sequence(stdout,89839,A089839,A000217(misc_table_size),
                            VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,0,OEIS_TABLE,
 "The composition table T(n,m): ... of the nth and mth automorphisms in the table A089840."
                           );

     }

    return(distinct_bijections);
}


/* The first 212 multiclause automorphisms that cannot be represented as
   a composition of two smaller nonrecursive automorphisms,
   as output by above loop:
 A089840[253] = c12__2_0_0_1__2_1_1_1
 A089840[254] = c12__2_0_0_2__2_1_1_1
 A089840[255] = c12__2_0_0_3__2_1_1_1
 A089840[256] = c12__2_0_0_4__2_1_1_1
 A089840[257] = c12__2_0_0_5__2_1_1_1
 A089840[258] = c12__2_0_1_0__2_1_0_4
 A089840[259] = c12__2_0_1_1__2_1_0_4
 A089840[260] = c12__2_0_1_2__2_1_0_4
 A089840[262] = c12__2_0_1_4__2_1_0_4
 A089840[263] = c12__2_0_1_5__2_1_0_4
 A089840[264] = c12__2_1_0_0__2_0_1_4
 A089840[265] = c12__2_1_0_1__2_0_1_4
 A089840[266] = c12__2_1_0_2__2_0_1_4
 A089840[267] = c12__2_1_0_3__2_0_1_4
 A089840[268] = c12__2_1_0_4__2_0_1_4
 A089840[271] = c12__2_1_1_1__2_0_0_2
 A089840[272] = c12__2_1_1_2__2_0_0_2
 A089840[273] = c12__2_1_1_3__2_0_0_2
 A089840[274] = c12__2_1_1_4__2_0_0_2
 A089840[275] = c12__2_1_1_5__2_0_0_2
 A089840[3610] = c24__3_0_0_1__2_1_1_1
 A089840[3612] = c24__3_0_0_2__2_1_1_1
 A089840[3614] = c24__3_0_0_3__2_1_1_1
 A089840[3616] = c24__3_0_0_4__2_1_1_1
 A089840[3618] = c24__3_0_0_5__2_1_1_1
 A089840[3620] = c24__3_0_0_6__2_1_1_1
 A089840[3622] = c24__3_0_0_7__2_1_1_1
 A089840[3624] = c24__3_0_0_8__2_1_1_1
 A089840[3626] = c24__3_0_0_9__2_1_1_1
 A089840[3628] = c24__3_0_0_10__2_1_1_1
 A089840[3630] = c24__3_0_0_11__2_1_1_1
 A089840[3632] = c24__3_0_0_12__2_1_1_1
 A089840[3634] = c24__3_0_0_13__2_1_1_1
 A089840[3636] = c24__3_0_0_14__2_1_1_1
 A089840[3638] = c24__3_0_0_15__2_1_1_1
 A089840[3640] = c24__3_0_0_16__2_1_1_1
 A089840[3642] = c24__3_0_0_17__2_1_1_1
 A089840[3644] = c24__3_0_0_18__2_1_1_1
 A089840[3646] = c24__3_0_0_19__2_1_1_1
 A089840[3648] = c24__3_0_0_20__2_1_1_1
 A089840[3650] = c24__3_0_0_21__2_1_1_1
 A089840[3652] = c24__3_0_0_22__2_1_1_1
 A089840[3654] = c24__3_0_0_23__2_1_1_1
 A089840[3796] = c24__3_1_1_1__2_1_1_1
 A089840[3798] = c24__3_1_1_2__2_1_1_1
 A089840[3800] = c24__3_1_1_3__2_1_1_1
 A089840[3802] = c24__3_1_1_4__2_1_1_1
 A089840[3804] = c24__3_1_1_5__2_1_1_1
 A089840[3806] = c24__3_1_1_6__2_1_1_1
 A089840[3808] = c24__3_1_1_7__2_1_1_1
 A089840[3810] = c24__3_1_1_8__2_1_1_1
 A089840[3812] = c24__3_1_1_9__2_1_1_1
 A089840[3814] = c24__3_1_1_10__2_1_1_1
 A089840[3816] = c24__3_1_1_11__2_1_1_1
 A089840[3818] = c24__3_1_1_12__2_1_1_1
 A089840[3820] = c24__3_1_1_13__2_1_1_1
 A089840[3822] = c24__3_1_1_14__2_1_1_1
 A089840[3824] = c24__3_1_1_15__2_1_1_1
 A089840[3826] = c24__3_1_1_16__2_1_1_1
 A089840[3828] = c24__3_1_1_17__2_1_1_1
 A089840[3829] = c24__3_1_1_18__2_1_1_1
 A089840[3831] = c24__3_1_1_19__2_1_1_1
 A089840[3833] = c24__3_1_1_20__2_1_1_1
 A089840[3835] = c24__3_1_1_21__2_1_1_1
 A089840[3837] = c24__3_1_1_22__2_1_1_1
 A089840[3839] = c24__3_1_1_23__2_1_1_1
 A089840[4162] = c24__3_3_3_1__2_0_0_2
 A089840[4164] = c24__3_3_3_2__2_0_0_2
 A089840[4166] = c24__3_3_3_3__2_0_0_2
 A089840[4168] = c24__3_3_3_4__2_0_0_2
 A089840[4170] = c24__3_3_3_5__2_0_0_2
 A089840[4172] = c24__3_3_3_6__2_0_0_2
 A089840[4174] = c24__3_3_3_7__2_0_0_2
 A089840[4176] = c24__3_3_3_8__2_0_0_2
 A089840[4178] = c24__3_3_3_9__2_0_0_2
 A089840[4180] = c24__3_3_3_10__2_0_0_2
 A089840[4182] = c24__3_3_3_11__2_0_0_2
 A089840[4184] = c24__3_3_3_12__2_0_0_2
 A089840[4186] = c24__3_3_3_13__2_0_0_2
 A089840[4188] = c24__3_3_3_14__2_0_0_2
 A089840[4190] = c24__3_3_3_15__2_0_0_2
 A089840[4192] = c24__3_3_3_16__2_0_0_2
 A089840[4194] = c24__3_3_3_17__2_0_0_2
 A089840[4196] = c24__3_3_3_18__2_0_0_2
 A089840[4197] = c24__3_3_3_19__2_0_0_2
 A089840[4199] = c24__3_3_3_20__2_0_0_2
 A089840[4201] = c24__3_3_3_21__2_0_0_2
 A089840[4203] = c24__3_3_3_22__2_0_0_2
 A089840[4205] = c24__3_3_3_23__2_0_0_2
 A089840[4347] = c24__3_4_4_1__2_0_0_2
 A089840[4349] = c24__3_4_4_2__2_0_0_2
 A089840[4351] = c24__3_4_4_3__2_0_0_2
 A089840[4353] = c24__3_4_4_4__2_0_0_2
 A089840[4355] = c24__3_4_4_5__2_0_0_2
 A089840[4357] = c24__3_4_4_6__2_0_0_2
 A089840[4358] = c24__3_4_4_7__2_0_0_2
 A089840[4360] = c24__3_4_4_8__2_0_0_2
 A089840[4362] = c24__3_4_4_9__2_0_0_2
 A089840[4364] = c24__3_4_4_10__2_0_0_2
 A089840[4366] = c24__3_4_4_11__2_0_0_2
 A089840[4368] = c24__3_4_4_12__2_0_0_2
 A089840[4370] = c24__3_4_4_13__2_0_0_2
 A089840[4372] = c24__3_4_4_14__2_0_0_2
 A089840[4374] = c24__3_4_4_15__2_0_0_2
 A089840[4376] = c24__3_4_4_16__2_0_0_2
 A089840[4378] = c24__3_4_4_17__2_0_0_2
 A089840[4380] = c24__3_4_4_18__2_0_0_2
 A089840[4382] = c24__3_4_4_19__2_0_0_2
 A089840[4384] = c24__3_4_4_20__2_0_0_2
 A089840[4386] = c24__3_4_4_21__2_0_0_2
 A089840[4388] = c24__3_4_4_22__2_0_0_2
 A089840[4390] = c24__3_4_4_23__2_0_0_2
 A089840[4402] = c28__2_0_0_1__3_3_3_1
 A089840[4403] = c28__2_0_0_1__3_3_3_2
 A089840[4404] = c28__2_0_0_1__3_3_3_3
 A089840[4405] = c28__2_0_0_1__3_3_3_4
 A089840[4406] = c28__2_0_0_1__3_3_3_5
 A089840[4407] = c28__2_0_0_1__3_4_4_1
 A089840[4408] = c28__2_0_0_1__3_4_4_2
 A089840[4409] = c28__2_0_0_1__3_4_4_3
 A089840[4410] = c28__2_0_0_1__3_4_4_4
 A089840[4411] = c28__2_0_0_1__3_4_4_5
 A089840[4412] = c28__2_0_0_2__3_3_3_1
 A089840[4413] = c28__2_0_0_2__3_3_3_2
 A089840[4414] = c28__2_0_0_2__3_3_3_3
 A089840[4415] = c28__2_0_0_2__3_3_3_4
 A089840[4416] = c28__2_0_0_2__3_3_3_5
 A089840[4417] = c28__2_0_0_2__3_4_4_1
 A089840[4418] = c28__2_0_0_2__3_4_4_2
 A089840[4419] = c28__2_0_0_2__3_4_4_3
 A089840[4420] = c28__2_0_0_2__3_4_4_4
 A089840[4421] = c28__2_0_0_2__3_4_4_5
 A089840[4422] = c28__2_0_0_3__3_3_3_1
 A089840[4423] = c28__2_0_0_3__3_3_3_2
 A089840[4424] = c28__2_0_0_3__3_3_3_3
 A089840[4425] = c28__2_0_0_3__3_3_3_4
 A089840[4426] = c28__2_0_0_3__3_3_3_5
 A089840[4427] = c28__2_0_0_3__3_4_4_1
 A089840[4428] = c28__2_0_0_3__3_4_4_2
 A089840[4429] = c28__2_0_0_3__3_4_4_3
 A089840[4430] = c28__2_0_0_3__3_4_4_4
 A089840[4431] = c28__2_0_0_3__3_4_4_5
 A089840[4432] = c28__2_0_0_4__3_3_3_1
 A089840[4433] = c28__2_0_0_4__3_3_3_2
 A089840[4434] = c28__2_0_0_4__3_3_3_3
 A089840[4435] = c28__2_0_0_4__3_3_3_4
 A089840[4436] = c28__2_0_0_4__3_3_3_5
 A089840[4437] = c28__2_0_0_4__3_4_4_1
 A089840[4438] = c28__2_0_0_4__3_4_4_2
 A089840[4439] = c28__2_0_0_4__3_4_4_3
 A089840[4440] = c28__2_0_0_4__3_4_4_4
 A089840[4441] = c28__2_0_0_4__3_4_4_5
 A089840[4442] = c28__2_0_0_5__3_3_3_1
 A089840[4443] = c28__2_0_0_5__3_3_3_2
 A089840[4444] = c28__2_0_0_5__3_3_3_3
 A089840[4445] = c28__2_0_0_5__3_3_3_4
 A089840[4446] = c28__2_0_0_5__3_3_3_5
 A089840[4447] = c28__2_0_0_5__3_4_4_1
 A089840[4448] = c28__2_0_0_5__3_4_4_2
 A089840[4449] = c28__2_0_0_5__3_4_4_3
 A089840[4450] = c28__2_0_0_5__3_4_4_4
 A089840[4451] = c28__2_0_0_5__3_4_4_5
 A089840[4462] = c28__2_1_1_1__3_0_0_2
 A089840[4463] = c28__2_1_1_1__3_0_0_6
 A089840[4464] = c28__2_1_1_1__3_0_0_8
 A089840[4465] = c28__2_1_1_1__3_0_0_12
 A089840[4466] = c28__2_1_1_1__3_0_0_14
 A089840[4467] = c28__2_1_1_1__3_1_1_2
 A089840[4468] = c28__2_1_1_1__3_1_1_6
 A089840[4469] = c28__2_1_1_1__3_1_1_8
 A089840[4470] = c28__2_1_1_1__3_1_1_12
 A089840[4471] = c28__2_1_1_1__3_1_1_14
 A089840[4472] = c28__2_1_1_2__3_0_0_2
 A089840[4473] = c28__2_1_1_2__3_0_0_6
 A089840[4474] = c28__2_1_1_2__3_0_0_8
 A089840[4475] = c28__2_1_1_2__3_0_0_12
 A089840[4476] = c28__2_1_1_2__3_0_0_14
 A089840[4477] = c28__2_1_1_2__3_1_1_2
 A089840[4478] = c28__2_1_1_2__3_1_1_6
 A089840[4479] = c28__2_1_1_2__3_1_1_8
 A089840[4480] = c28__2_1_1_2__3_1_1_12
 A089840[4481] = c28__2_1_1_2__3_1_1_14
 A089840[4482] = c28__2_1_1_3__3_0_0_2
 A089840[4483] = c28__2_1_1_3__3_0_0_6
 A089840[4484] = c28__2_1_1_3__3_0_0_8
 A089840[4485] = c28__2_1_1_3__3_0_0_12
 A089840[4486] = c28__2_1_1_3__3_0_0_14
 A089840[4487] = c28__2_1_1_3__3_1_1_2
 A089840[4488] = c28__2_1_1_3__3_1_1_6
 A089840[4489] = c28__2_1_1_3__3_1_1_8
 A089840[4490] = c28__2_1_1_3__3_1_1_12
 A089840[4491] = c28__2_1_1_3__3_1_1_14
 A089840[4492] = c28__2_1_1_4__3_0_0_2
 A089840[4493] = c28__2_1_1_4__3_0_0_6
 A089840[4494] = c28__2_1_1_4__3_0_0_8
 A089840[4495] = c28__2_1_1_4__3_0_0_12
 A089840[4496] = c28__2_1_1_4__3_0_0_14
 A089840[4497] = c28__2_1_1_4__3_1_1_2
 A089840[4498] = c28__2_1_1_4__3_1_1_6
 A089840[4499] = c28__2_1_1_4__3_1_1_8
 A089840[4500] = c28__2_1_1_4__3_1_1_12
 A089840[4501] = c28__2_1_1_4__3_1_1_14
 A089840[4502] = c28__2_1_1_5__3_0_0_2
 A089840[4503] = c28__2_1_1_5__3_0_0_6
 A089840[4504] = c28__2_1_1_5__3_0_0_8
 A089840[4505] = c28__2_1_1_5__3_0_0_12
 A089840[4506] = c28__2_1_1_5__3_0_0_14
 A089840[4507] = c28__2_1_1_5__3_1_1_2
 A089840[4508] = c28__2_1_1_5__3_1_1_6
 A089840[4509] = c28__2_1_1_5__3_1_1_8
 A089840[4510] = c28__2_1_1_5__3_1_1_12
 A089840[4511] = c28__2_1_1_5__3_1_1_14
 */

/**********************************************************************/

/* See notes at the definition of CLAUSESEQ_begin macro ! */

CLAUSE gmA001477[] = { CLAUSESEQ_begin(0,0) };                /* A089840[0] */
CLAUSE gmA069770[] = { CLAUSESEQ_begin(1,1), { 1, 0, 0, 1 } };/* A089840[1] */
CLAUSE gmA072796[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 1 } };/* A089840[2] */
CLAUSE gmA089850[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 2 } };/* A089840[3] */
CLAUSE gmA089851[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 3 } };/* A089840[4] */
CLAUSE gmA089852[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 4 } };/* A089840[5] */
CLAUSE gmA089853[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 5 } };/* A089840[6] */
CLAUSE gmA089854[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 1 } };/* A089840[7] */
CLAUSE gmA072797[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 2 } };/* A089840[8] */
CLAUSE gmA089855[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 3 } };/* A089840[9] */
CLAUSE gmA089856[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 4 } };/* A089840[10] */
CLAUSE gmA089857[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 5 } };/* A089840[11] */
CLAUSE gmA074679[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 0,}, { 1, 0, 0, 1 } }; /* A089840[12] */
CLAUSE gmA089858[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 1,}, { 1, 0, 0, 1 } }; /* A089840[13] */
CLAUSE gmA073269[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 2,}, { 1, 0, 0, 1 } }; /* A089840[14] */
CLAUSE gmA089859[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 4,}, { 1, 0, 0, 1 } }; /* A089840[15] */
CLAUSE gmA089860[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 5,}, { 1, 0, 0, 1 } }; /* A089840[16] */
CLAUSE gmA074680[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 0 }, { 1, 0, 0, 1 } }; /* A089840[17] */
CLAUSE gmA089861[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 1,}, { 1, 0, 0, 1 } }; /* A089840[18] */
CLAUSE gmA073270[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 2,}, { 1, 0, 0, 1 } }; /* A089840[19] */
CLAUSE gmA089862[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 3,}, { 1, 0, 0, 1 } }; /* A089840[20] */
CLAUSE gmA089863[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 4,}, { 1, 0, 0, 1 } }; /* A089840[21] */

CLAUSE gmA123503[] = { CLAUSESEQ_begin(12,2), { 2, 0, 0, 1,}, { 2, 1, 1, 1 } }; /* A089840[253] */


CLAUSE gmA123499[] = { CLAUSESEQ_begin(12,2), { 2, 0, 1, 0,}, { 2, 1, 0, 4 } }; /* A089840[258] */
CLAUSE gmA123500[] = { CLAUSESEQ_begin(12,2), { 2, 1, 0, 0,}, { 2, 0, 1, 4 } }; /* A089840[264] */

CLAUSE gmA073281[] = { CLAUSESEQ_begin(103,3), { 3, 1, 1, 7,}, { 2, 0, 1, 2 }, { 2, 1, 0, 2 } }; /* A089840[1654023] */

CLAUSE gmA089864[] = { CLAUSESEQ_begin(103,3), { 3, 2, 2, 7,}, { 2, 0, 0, 2 }, { 2, 1, 1, 1 } }; /* A089840[1654694] */
CLAUSE gmA089864b[] = { CLAUSESEQ_begin(103,3), { 3, 2, 2, 7,}, { 2, 1, 1, 1 }, { 2, 0, 0, 2 }  }; /* The last two clauses in either order. */

CLAUSE gmA154121[] = { CLAUSESEQ_begin(24,2), { 3, 0, 1, 0 }, { 2, 0, 0, 2 } }; /* A089840[3655] */
CLAUSE gmA154122[] = { CLAUSESEQ_begin(24,2), { 3, 1, 0, 0 }, { 2, 0, 0, 2 } }; /* A089840[3747] */

CLAUSE gmA154123[] = { CLAUSESEQ_begin(24,2), { 3, 0, 1, 0 }, { 2, 0, 0, 3 } }; /* A089840[3656] */
CLAUSE gmA154124[] = { CLAUSESEQ_begin(24,2), { 3, 1, 0, 0 }, { 2, 0, 0, 5 } }; /* A089840[3748] */

CLAUSE gmA154125[] = { CLAUSESEQ_begin(7,1), { 3, 2, 2, 16 } }; /* A089840[83] */

CLAUSE gmA154126[] = { CLAUSESEQ_begin(8,2), { 3, 2, 2, 0 }, { 1, 0, 0, 1 } }; /* A089840[183] */


CLAUSE gmA089865[] = { CLAUSESEQ_begin(24,2), { 3, 3, 4, 0 }, { 2, 1, 1, 1 } }; /* A089840[4207] */
CLAUSE gmA089866[] = { CLAUSESEQ_begin(24,2), { 3, 4, 3, 0 }, { 2, 1, 1, 1 } }; /* A089840[4299] */

CLAUSE gmA082351[] = { CLAUSESEQ_begin(24,2), { 3, 2, 4, 0 }, { 2, 1, 1, 5 } }; /* A089840[4069] */
CLAUSE gmA082352[] = { CLAUSESEQ_begin(24,2), { 3, 4, 2, 0 }, { 2, 1, 1, 3 } }; /* A089840[4253] */

CLAUSE gmA082353[] = { CLAUSESEQ_begin(24,2), { 3, 2, 0, 0 }, { 2, 0, 0, 3 } }; /* A089840[3886] A057163-conjugates of the above ones. */
CLAUSE gmA082354[] = { CLAUSESEQ_begin(24,2), { 3, 0, 2, 0 }, { 2, 0, 0, 5 } }; /* A089840[3702] */


CLAUSE gmA129604[] = { CLAUSESEQ_begin(103,3), { 3, 2, 2, 20,}, { 2, 0, 1, 4 }, { 2, 1, 0, 4 } }; /* A089840[1654720] */

CLAUSE gmA129605[] = { CLAUSESEQ_begin(24,2), { 3, 0, 0, 3,}, { 2, 0, 0, 1 } }; /* A089840[3613] */
CLAUSE gmA129606[] = { CLAUSESEQ_begin(24,2), { 3, 0, 0, 5,}, { 2, 0, 0, 1 } }; /* A089840[3617] */

CLAUSE gmA129607[] = { CLAUSESEQ_begin(24,2), { 3, 0, 0, 0,}, { 2, 0, 0, 1 } }; /* A089840[3608] */

CLAUSE gmA129609[] = { CLAUSESEQ_begin(39,3), { 3, 1, 2, 0,}, { 2, 0, 1, 2 }, { 1, 0, 0, 1 } }; /* A089840[65167] */
CLAUSE gmA129610[] = { CLAUSESEQ_begin(39,3), { 3, 2, 1, 0,}, { 2, 1, 0, 2 }, { 1, 0, 0, 1 } }; /* A089840[65352] */

CLAUSE gmA129611[] = { CLAUSESEQ_begin(8,2), { 3, 1, 4, 10,}, { 1, 0, 0, 1 } }; /* A089840[169] */
CLAUSE gmA129612[] = { CLAUSESEQ_begin(8,2), { 3, 4, 1, 22,}, { 1, 0, 0, 1 } }; /* A089840[251] */


CLAUSE gmA123492[] = { CLAUSESEQ_begin(56,2), { 3, 1, 4, 9 }, { 3, 4, 1, 23 } }; /* A089840[79361] */
CLAUSE gmA123492b[] = { CLAUSESEQ_begin(56,2), { 3, 4, 1, 23 }, { 3, 1, 4, 9 } }; /* Clauses in either order. */
CLAUSE gmA123495[] = { CLAUSESEQ_begin(39,3), { 3, 2, 4, 16 }, { 2, 0, 1, 0 }, { 1, 0, 0, 1 } }; /* A089840[65518] */
CLAUSE gmA123496[] = { CLAUSESEQ_begin(39,3), { 3, 4, 2, 16 }, { 2, 1, 0, 0 }, { 1, 0, 0, 1 } }; /* A089840[65796] */
CLAUSE gmA123497[] = { CLAUSESEQ_begin(103,3), { 3, 3, 1, 6,}, { 2, 1, 1, 2 }, { 2, 0, 0, 1 } }; /* A089840[1655089] */
CLAUSE gmA123498[] = { CLAUSESEQ_begin(103,3), { 3, 1, 3, 6,}, { 2, 0, 0, 1 }, { 2, 1, 1, 2 } }; /* A089840[1654249] */
CLAUSE gmA123695[] = { CLAUSESEQ_begin(99,3), { 2, 0, 1, 0,}, { 3, 3, 1, 23,}, { 2, 1, 0, 3 } }; /* A089840[1653002] */
CLAUSE gmA123695b[] = { CLAUSESEQ_begin(99,3), { 2, 0, 1, 0,}, { 3, 3, 1, 23,}, { 2, 1, 0, 4 } }; /* The last clause different. */
CLAUSE gmA123696[] = { CLAUSESEQ_begin(99,3), { 2, 1, 0, 0,}, { 3, 1, 3, 9,}, { 2, 0, 1, 4 } }; /* A089840[1653063] */

CLAUSE gmA123713[] = { CLAUSESEQ_begin(124,2), { 2, 1, 1, 3,}, { 5, 13, 13, 152 } }; /* A089840[1783367] */
CLAUSE gmA123714[] = { CLAUSESEQ_begin(124,2), { 2, 1, 1, 5,}, { 5, 13, 13, 566 } }; /* A089840[1786785] */

/* Note that: Sum_{i=1..7} A089832(i) =  (+ 1  10  125  1805  32768  713930  18334997) = 19083636
   A089831(7,1)=17296851 and 19083636-17296851 = 1786785
   Thus A123714 is the last nonrecursive multiclause automorphism of 7 opening nodes
   before the single-clause standalone 7-node automorphisms. (The first one of them, A089840[1786786]
   swaps the two first elements of a list, if it's length is at least seven, otherwise
   keeps the S-expression intact.)
 */


struct clauses_and_Anum
 {
   CLAUSESEQ clauses;
   int Anum;
 };

struct clauses_and_Anum Submitted_nr_automorphisms[] =
 {
   { gmA001477,     1477 }, { gmA069770,    69770 }, { gmA072796,    72796 },
   { gmA089850,    89850 }, { gmA089851,    89851 }, { gmA089852,    89852 },
   { gmA089853,    89853 }, { gmA089854,    89854 }, { gmA072797,    72797 },
   { gmA089855,    89855 }, { gmA089856,    89856 }, { gmA089857,    89857 },
   { gmA074679,    74679 }, { gmA089858,    89858 }, { gmA073269,    73269 },
   { gmA089859,    89859 }, { gmA089860,    89860 }, { gmA074680,    74680 },
   { gmA089861,    89861 }, { gmA073270,    73270 }, { gmA089862,    89862 },
   { gmA089863,    89863 },
   { gmA123503,   123503 }, { gmA123499,   123499 }, { gmA123500,   123500 },
   { gmA082351,    82351 }, { gmA082352,    82352 },
   { gmA082353,    82353 }, { gmA082354,    82354 },
   { gmA073281,    73281 },
   { gmA089864,    89864 }, { gmA089864b,   89864 },
   { gmA089865,    89865 }, { gmA089866,    89866 },
   { gmA123492,   123492 },
   { gmA123495,   123495 }, { gmA123496,   123496 },
   { gmA123497,   123497 }, { gmA123498,   123498 },
   { gmA123695,   123695 }, { gmA123696,   123696 },
   { gmA123713,   123713 }, { gmA123714,   123714 },
   { gmA129604,   129604 },
   { gmA129605,   129605 }, { gmA129606,   129606 }, { gmA129607,   129607 },
   { gmA129609,   129609 }, { gmA129610,   129610 },
   { gmA129611,   129611 }, { gmA129612,   129612 },
   { gmA154121,   154121 }, { gmA154122,   154122 },
   { gmA154123,   154123 }, { gmA154124,   154124 },
   { gmA154125,   154125 }, { gmA154126,   154126 },
   { NULL, 0 }
 };

/* This is now global. */
CLAUSESEQ *first_clauseseqs;


void fprint_submitted_nr_automorphism(FILE *fp,struct clauses_and_Anum *gmn,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep)
{
    int Anum = gmn->Anum;
    CLAUSESEQ clause_seq = gmn->clauses;
    CLAUSESEQ dupe = NULL;
    char indbuf[81];
    char name[81];

    dupe = duplicate_found_in_hashtable(clause_seq,hashtable,hashsize,ep,NULL,1);

    if(NULL == dupe) { strcpy(indbuf,"NOT-FOUND-WITH-GIVEN-LIMITS"); } 
    else
     {
       sprintf(indbuf,"%u",CLAUSESEQ_norerank(dupe));

       if(1 == CLAUSESEQ_norerank(dupe)) /* We have A069770. */
        {
          int i;
          sA069770  = ((SGRANK *) calloc(ep->vec_size,sizeof(SGRANK)));
       
          if(NULL == sA069770)
           {
             fprintf(stderr,
                      "Couldn't allocate a vector sA069770 of %u short integers (%u bytes).\n",
                      ep->vec_size,ep->vec_size*sizeof(SGRANK)
                    );
             /* exit(1); */
           }

          for(i=0; i < ep->vec_size; i++) { sA069770[i] = (SGRANK) ep->vals_obtained[i]; }
        }
     }

    sprintf(name,"Non-recursive Catalan automorphism A089840[%s]",indbuf);

    if(NULL != dupe)
     { fprintf(fp,"CLAUSESEQ="); fprint_clause_seq(fp,dupe); fprintf(fp,"\n"); fflush(fp); }

    output_OEIS_sequence(fp,Anum,ep->vals_obtained,ep->vec_size,
                         VECTYPE_USI,(PF_VEC_OUT)fprint_USI_vector,0,OEIS_SEQ,
                         name
                        );

}


void fprint_all_submitted_nr_automorphisms(FILE *fp,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep)
{
    int i=0;
    struct clauses_and_Anum *gmn;

    while((gmn = &(Submitted_nr_automorphisms[i++])) && (NULL != gmn->clauses))
     {
       fprint_submitted_nr_automorphism(fp,gmn,hashtable,hashsize,ep);
     }
}

void fprint_A123694(FILE *fp,CLAUSESEQ *first_clauseseqs,int misc_seq_size,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep)
{
    int i=0;
    NORERANK *sA123694;

    if(NULL == (sA123694 = ((NORERANK *) calloc(misc_seq_size+1,sizeof(NORERANK)))))
     {
       fprintf(stderr,
                "Couldn't allocate a vector sA123694 of %u long integers (%u bytes).\n",
                 misc_seq_size,misc_seq_size*sizeof(NORERANK)
                    );
       exit(1);
     }

    for(i=0; i < misc_seq_size; i++)
     {
       CLAUSESEQ clause_seq = clause_seq_A123694(first_clauseseqs[i]);
       CLAUSESEQ dupe = duplicate_found_in_hashtable(clause_seq,hashtable,hashsize,ep,NULL,1);

       if(NULL == dupe) { sA123694[i] = NA_SENTINEL; }
       else { sA123694[i] = CLAUSESEQ_norerank(dupe); }
     }

    output_OEIS_sequence(stdout,123694,sA123694,misc_seq_size,
                         VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,
                         0,OEIS_SEQ,
                         "The position of A089840[n] after apply_to_left_subtree_only transformation."
                        );

}


void fprint_A153834(FILE *fp,CLAUSESEQ *first_clauseseqs,int misc_seq_size,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep)
{
    int i=0;
    NORERANK *sA153834;

    if(NULL == (sA153834 = ((NORERANK *) calloc(misc_seq_size+1,sizeof(NORERANK)))))
     {
       fprintf(stderr,
                "Couldn't allocate a vector sA153834 of %u long integers (%u bytes).\n",
                 misc_seq_size,misc_seq_size*sizeof(NORERANK)
                    );
       exit(1);
     }

    for(i=0; i < misc_seq_size; i++)
     {
       CLAUSESEQ clause_seq = clause_seq_A153834(first_clauseseqs[i]);
       CLAUSESEQ dupe = duplicate_found_in_hashtable(clause_seq,hashtable,hashsize,ep,NULL,1);

       if(NULL == dupe) { sA153834[i] = NA_SENTINEL; }
       else { sA153834[i] = CLAUSESEQ_norerank(dupe); }
     }

    output_OEIS_sequence(stdout,153834,sA153834,misc_seq_size,
                         VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,
                         0,OEIS_SEQ,
                         "The position of A089840[n] after apply_to_right_subtree_only transformation."
                        );

}

/* The Atavistic Index Sequence for ENIPS should be (f o (f^-1)_cdr)
   and for SPINE it should be  ((f^-1)_cdr o f)

A089839(n,A153834(A089843(n)))
and
A089839(A153834(A089843(n)),n)

 */

/* This is for ENIPS: */
void fprint_A153832(FILE *fp,CLAUSESEQ *first_clauseseqs,int misc_seq_size,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep)
{
    int i=0;
    NORERANK *seq_vec;

    if(NULL == (seq_vec = ((NORERANK *) calloc(misc_seq_size+1,sizeof(NORERANK)))))
     {
       fprintf(stderr,
                "Couldn't allocate a vector seq_vec of %u long integers (%u bytes).\n",
                 misc_seq_size,misc_seq_size*sizeof(NORERANK)
                    );
       exit(1);
     }


    for(i=0; i < misc_seq_size; i++)
     {
       CLAUSESEQ clause1, clause2, comp;

       clause1 = inverse_found_in_hashtable(first_clauseseqs[i],
                                            hashtable,hashsize,ep);
       if(NULL == clause1) { seq_vec[i] = NA_SENTINEL; }
       else
        {
          clause2 = clause_seq_A153834(clause1);
          if(NULL == clause2) { seq_vec[i] = NA_SENTINEL; }
          else
           {
             comp = composition_found_in_hashtable(clause2,first_clauseseqs[i],
                                                   hashtable,hashsize,ep);
             seq_vec[i] = ((NULL == comp) ? NA_SENTINEL
                                           : CLAUSESEQ_norerank(comp));
           }
        }
     }


    output_OEIS_sequence(stdout,153832,seq_vec,misc_seq_size,
                         VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,
                         0,OEIS_SEQ,
                         "Atavistic Index Sequence to A089840 computed for ENIPS."
                        );
}

/* This is for SPINE: */
void fprint_A153833(FILE *fp,CLAUSESEQ *first_clauseseqs,int misc_seq_size,CLAUSESEQ *hashtable,int hashsize,ECOTEX *ep)
{
    int i=0;
    NORERANK *seq_vec;

    if(NULL == (seq_vec = ((NORERANK *) calloc(misc_seq_size+1,sizeof(NORERANK)))))
     {
       fprintf(stderr,
                "Couldn't allocate a vector seq_vec of %u long integers (%u bytes).\n",
                 misc_seq_size,misc_seq_size*sizeof(NORERANK)
                    );
       exit(1);
     }


    for(i=0; i < misc_seq_size; i++)
     {
       CLAUSESEQ clause1, clause2, comp;

       clause1 = inverse_found_in_hashtable(first_clauseseqs[i],
                                            hashtable,hashsize,ep);
       if(NULL == clause1) { seq_vec[i] = NA_SENTINEL; }
       else
        {
          clause2 = clause_seq_A153834(clause1);
          if(NULL == clause2) { seq_vec[i] = NA_SENTINEL; }
          else
           {
             comp = composition_found_in_hashtable(first_clauseseqs[i],clause2,
                                                   hashtable,hashsize,ep);
             seq_vec[i] = ((NULL == comp) ? NA_SENTINEL
                                           : CLAUSESEQ_norerank(comp));
           }
        }
     }


    output_OEIS_sequence(stdout,153833,seq_vec,misc_seq_size,
                         VECTYPE_NORERANK,(PF_VEC_OUT)fprint_NORERANK_vector_with_NA_SENTINELs,
                         0,OEIS_SEQ,
                         "Atavistic Index Sequence to A089840 computed for SPINE."
                        );
}


FILE *checkfopen(char *filename,char *mode)
{
    FILE *fp;

    if(NULL == (fp = fopen(filename,mode)))
     {
       fprintf(stderr,"\nCannot open file \"%s\" in mode \"%s\"!. Exiting.\n",
               filename,mode);
       exit(1);
     }

    return(fp);
}

int main(int argc, char **argv)
{
    ULLI x = (ULLI) (((SLLI) -1));
    char *progname = *argv;
    char *tharg;
    int upto_binexp_n,upto_size_n;
    char *count_or_check = NULL;
    ECOTEX *ep;
    CLAUSESEQ *hashtable;
    CLAUSESEQ front_clause_searched = NULL;
    int hashsize,misc_table_size=15,misc_seq_size=120,max_order_tested_to=21;
    int search_nondecomposables_upto_n = 0;
    ULLI *A089832,*A089831;
    SGRANK *A089840 = NULL; /* An array of signature-permutations. */
    NORERANK *A089839 = NULL; /* A table of their compositions. */
    NORERANK *misc_seq_vec = NULL;
    FILTERMASK filmask = FILTER_IF_NONULTIMATE_1S+FILTER_LONE_NONSTANDALONES;
    int opt_print_all_submitted_nr_automorphisms = 0;
    int i=0;

    CheckTriangle(19);

/* First handle the options: */
    while((tharg = *++argv) && ('-' == *tharg))
     {
       char c;

       argc--;

       while(c=*++tharg)
        {
          switch(c)
           {
             case 'G':
              {
                opt_print_all_submitted_nr_automorphisms++;
                break;
              }

             case 'I':
              {
                globopt_output_invariance_indices++;
                globopt_compute_A153830++;
                break;
              }

             case 'c':
              {
                int i;
                int numargs[5];
                char *narg;

                for(i=0; i<4; i++)
                 {
                   narg = *++argv; /* The next argument, hopefully not NULL. */
                   argc--;
                   if((NULL == narg) || ('\0' == *narg) || !isdigit(*narg))
                    {
                      fprintf(stderr,
   "Option -c requires four numeric arguments. Example: -c 3 3 4 0\n");
                      exit(1);
                    }

                   numargs[i] = atoi(narg);
                 }

                front_clause_searched = ((CLAUSESEQ) calloc(1,sizeof(CLAUSE)));

                if(NULL == front_clause_searched)
                 {
                   fprintf(stderr,
                     "Couldn't allocate %u bytes for a clause.\n",
                       (1*sizeof(CLAUSE)));
                   exit(1);
                 }
                else
                 {
                   CLAUSE *cl = &CLAUSESEQ_nthclause(front_clause_searched,0);

                   SET_CLAUSE_size(*cl,numargs[0]);
                   SET_CLAUSE_s_lrank(*cl,numargs[1]);
                   SET_CLAUSE_d_lrank(*cl,numargs[2]);
                   SET_CLAUSE_p_rank(*cl,numargs[3]);
                 }
                goto big_wheels_keep_on_rolling;
                break;
              }

             case 'S':
              {
                char *narg = ++tharg; /* Pointing to character after S */
                if('\0' == *narg)
                 {
                   narg = *++argv; /* The next argument, hopefully not NULL. */
                   argc--;
                 }

                if((NULL == narg) || ('\0' == *narg) || !isdigit(*narg) || ('0' == *narg))
                 {
                   fprintf(stderr,"Option -S requires a numeric, non-zero argument. Example: -S 240\n");
                   exit(1);
                 }

                misc_seq_size = atoi(narg);

                goto big_wheels_keep_on_rolling;
                break;
              }

             case 'T':
              {
                char *narg = ++tharg; /* Pointing to character after T */
                if('\0' == *narg)
                 {
                   narg = *++argv; /* The next argument, hopefully not NULL. */
                   argc--;
                 }

                if((NULL == narg) || ('\0' == *narg) || !isdigit(*narg) || ('0' == *narg))
                 {
                   fprintf(stderr,"Option -T requires a numeric, non-zero argument. Example: -T 45\n");
                   exit(1);
                 }

                misc_table_size = atoi(narg);

                goto big_wheels_keep_on_rolling;
                break;
              }

             case 'm':
              {
                char *narg = ++tharg; /* Pointing to character after m */
                if('\0' == *narg)
                 {
                   narg = *++argv; /* The next argument, hopefully not NULL. */
                   argc--;
                 }

                if((NULL == narg) || ('\0' == *narg) || !isdigit(*narg) || ('0' == *narg))
                 {
                   fprintf(stderr,"Option -m requires a numeric, non-zero argument. Example: -m 36\n");
                   exit(1);
                 }

                max_order_tested_to = atoi(narg);

                goto big_wheels_keep_on_rolling;
                break;
              }

             case 's':
              {
                char *narg = ++tharg; /* Pointing to character after s */
                if('\0' == *narg)
                 {
                   narg = *++argv; /* The next argument, hopefully not NULL. */
                   argc--;
                 }

                if((NULL == narg) || ('\0' == *narg) || !isdigit(*narg) || ('0' == *narg))
                 {
                   fprintf(stderr,
               "Option -s requires a numeric, non-zero argument. Example: -s 136, 1941 or 34709\n");
                   exit(1);
                 }

                search_nondecomposables_upto_n = atoi(narg);

                goto big_wheels_keep_on_rolling;
                break;
              }

             case 'l':
              {
                globopt_output_cycle_lists++;
                break;
              }
             case 'H':
              {
                globopt_HTML = 1;
                break;
              }
             case 'M': /* Maple-output and Haskell/Prolog-output. */
              {
                globopt_list_begin = "[";
                globopt_list_delim = ",";
                globopt_list_end   = "]";
                globopt_elem_delim = ",";
                globopt_pair_begin = "[";
                globopt_pair_delim = ",";
                globopt_pair_end   = "]";
                globopt_comment_begin = "#";
                break;
              }
             case 'R':
              {
                CheckRankings(upto_size_n);
                CheckSexpRankings(upto_size_n);
                exit(0);
                break;
              }
             default:
              {
                fprintf(stderr,"Unknown option %s !\n",tharg);
                goto usage;
              }
           }
        }
big_wheels_keep_on_rolling: ;
     }


    if(argc < 4)
     {
usage:
       fprintf(stderr,"usage: %s upto_binexp_n upto_size_n hashtable_size\n", progname);
       exit(1);
     }

    upto_binexp_n = atoi(*(argv+0));

    if(upto_binexp_n > MAX_BINEXP)
     {
       fprintf(stderr,
               "%s: upto_binexp_n (%d) was specified greater than MAX_BINEXP=%u\n",
               progname,upto_binexp_n,MAX_BINEXP
              );
       exit(1);
     }

    upto_size_n = atoi(*(argv+1));

    if((upto_size_n < binwidth(upto_binexp_n)) || (upto_size_n > MAX_COMPUTATION_SIZE))
     {
       fprintf(stderr,
               "%s: upto_size_n (%d) was specified either less than binwidth(%u) (= %u, the maximum clause tree size), or more than MAX_COMPUTATION_SIZE=%u\n",
               progname,upto_size_n,upto_binexp_n,binwidth(upto_binexp_n),MAX_COMPUTATION_SIZE
              );
       exit(1);
     }

    if(globopt_output_invariance_indices)
     {
       if(upto_size_n > 9)
        {
          fprintf(stderr,"%s: Sorry, the max tree size with option -I is 9.\n",
                         progname
                 );
          exit(1);
        }
       else
        {
          fpA153826 = checkfopen("b153826.txt","w");
          fpA153827 = checkfopen("b153827.txt","w");
          fpA153828 = checkfopen("b153828.txt","w");
          fpA153829 = checkfopen("b153829.txt","w");
          fpA153830 = checkfopen("b153830.txt","w");
          fpA153831 = checkfopen("b153831.txt","w");
        }
     }




    hashsize = atoi(*(argv+2));

    if(NULL == (hashtable = ((CLAUSESEQ *) calloc(hashsize,sizeof(CLAUSESEQ)))))
     {
       fprintf(stderr,
                "%s: Couldn't allocate a hash table of %u buckets (%u bytes).\n",
	       progname,hashsize,(hashsize*sizeof(CLAUSESEQ))
              );
       exit(1);
     }

    ep = new_ecotex(upto_size_n);

    printf("glob_cons_cells_in_use=%lu\n",glob_cons_cells_in_use);

     {
       int i = (binwidth(upto_binexp_n)+1);

       if(NULL == (A089832 = ((ULLI *) calloc(i,sizeof(ULLI)))))
        {
          fprintf(stderr,
                  "%s: Couldn't allocate a A089832 table of %u longlong integers (%u bytes).\n",
	          progname,(i),(i*sizeof(ULLI))
                 );
          exit(1);
        }

       i = tr2seqind(i,i)+1;

       if(NULL == (A089831 = ((ULLI *) calloc(i,sizeof(ULLI)))))
        {
          fprintf(stderr,
                  "%s: Couldn't allocate a A089831 table of %u longlong integers (%u bytes).\n",
	          progname,(i),(i*sizeof(ULLI))
                 );
          exit(1);
        }

     }

      {

        int i = tr2seqind(misc_table_size+1,misc_table_size+1)+1;

        if((misc_table_size < 1) || (misc_table_size > ep->vec_size))
         {
           fprintf(stderr,
                   "%s: misc_table_size (%d) was specified either less than 1, or more than A014137(%u)=%lu\n",
	           progname,misc_table_size,upto_size_n,A014137(upto_size_n)
                  );
           exit(1);
         }
    
        if(NULL == (A089839 = ((NORERANK *) calloc(i,sizeof(NORERANK)))))
         {
           fprintf(stderr,
                   "%s: Couldn't allocate a triangular table of %u short integers (%u bytes) for A089839.\n",
	           progname,(i),(i*sizeof(NORERANK))
                  );
           exit(1);
         }
    
        if(NULL == (A089840 = ((SGRANK *) calloc(i,sizeof(SGRANK)))))
         {
           fprintf(stderr,
                   "%s: Couldn't allocate a triangular table of %u short integers (%u bytes) for A089840.\n",
	           progname,(i),(i*sizeof(SGRANK))
                  );
           exit(1);
         }

        if(misc_seq_size < search_nondecomposables_upto_n)
         {
           misc_seq_size = search_nondecomposables_upto_n + 2;
           fprintf(stderr,"%s: misc_seq_size set to search_nondecomposables_upto_n+2 (%u)\n",
                          progname,search_nondecomposables_upto_n+2);
         }

        if(misc_seq_size < misc_table_size)
         {
           fprintf(stderr,"%s: You can't specify misc_seq_size (%u) < misc_table_size (%u)!\n",
                          progname,misc_seq_size,misc_table_size);
           exit(1);
         }

        if(NULL == (first_clauseseqs = ((CLAUSESEQ *) calloc(misc_seq_size,sizeof(CLAUSESEQ)))))
         {
           fprintf(stderr,
                   "%s: Couldn't allocate a first_clauseseqs table of %u clause sequences (%u bytes).\n",
	           progname,misc_seq_size,(misc_seq_size*sizeof(CLAUSESEQ))
                  );
           exit(1);
         }

        if(NULL == (misc_seq_vec = ((NORERANK *) calloc(misc_seq_size,sizeof(NORERANK)))))
         {
           fprintf(stderr,
                   "%s: Couldn't allocate a misc_seq_vec of %u NORERANKs (%u bytes).\n",
	           progname,misc_seq_size,(misc_seq_size*sizeof(NORERANK))
                  );
           exit(1);
         }

      }

    check_upto_binexp_n(upto_binexp_n,ep,hashsize,hashtable,first_clauseseqs,filmask,
                        misc_seq_size,misc_table_size,max_order_tested_to,
                        search_nondecomposables_upto_n,
                        A089832,A089831,A089839,A089840,misc_seq_vec,
                        front_clause_searched);

    if(opt_print_all_submitted_nr_automorphisms)
     {
       fprint_all_submitted_nr_automorphisms(stdout,hashtable,hashsize,ep);
       fprint_A123694(stdout,first_clauseseqs,misc_seq_size,hashtable,hashsize,ep);
       fprint_A153832(stdout,first_clauseseqs,misc_seq_size,hashtable,hashsize,ep);

       fprint_A153833(stdout,first_clauseseqs,misc_seq_size,hashtable,hashsize,ep);

       fprint_A153834(stdout,first_clauseseqs,misc_seq_size,hashtable,hashsize,ep);
     }

    exit(0);
}


/*************** A few longish precomputed sequences follow. *********/


ULI sA127301_up_to6917[6918] =
{1,2,4,3,8,6,6,7,5,16,12,12,14,10,12,9,14,19,13,10,13,17,11,32,24,24,28,
20,24,18,28,38,26,20,26,34,22,24,18,18,21,15,28,21,38,53,37,26,37,43,
29,20,15,26,37,23,34,43,67,41,22,29,41,59,31,64,48,48,56,40,48,36,56,
76,52,40,52,68,44,48,36,36,42,30,56,42,76,106,74,52,74,86,58,40,30,52,
74,46,68,86,134,82,44,58,82,118,62,48,36,36,42,30,36,27,42,57,39,30,39,
51,33,56,42,42,49,35,76,57,106,131,89,74,89,107,71,52,39,74,89,61,86,
107,163,101,58,71,101,139,79,40,30,30,35,25,52,39,74,89,61,46,61,73,47,
68,51,86,107,73,134,163,241,157,82,101,157,191,109,44,33,58,71,47,82,
101,157,83,118,139,191,331,179,62,79,109,179,277,127,128,96,96,112,80,
96,72,112,152,104,80,104,136,88,96,72,72,84,60,112,84,152,212,148,104,
148,172,116,80,60,104,148,92,136,172,268,164,88,116,164,236,124,96,72,
72,84,60,72,54,84,114,78,60,78,102,66,112,84,84,98,70,152,114,212,262,
178,148,178,214,142,104,78,148,178,122,172,214,326,202,116,142,202,278,
158,80,60,60,70,50,104,78,148,178,122,92,122,146,94,136,102,172,214,
146,268,326,482,314,164,202,314,382,218,88,66,116,142,94,164,202,314,
166,236,278,382,662,358,124,158,218,358,554,254,96,72,72,84,60,72,54,
84,114,78,60,78,102,66,72,54,54,63,45,84,63,114,159,111,78,111,129,87,
60,45,78,111,69,102,129,201,123,66,87,123,177,93,112,84,84,98,70,84,63,
98,133,91,70,91,119,77,152,114,114,133,95,212,159,262,311,223,178,223,
263,173,148,111,178,223,151,214,263,383,239,142,173,239,337,193,104,78,
78,91,65,148,111,178,223,151,122,151,181,113,172,129,214,263,181,326,
383,577,373,202,239,373,443,271,116,87,142,173,113,202,239,373,199,278,
337,443,757,421,158,193,271,421,647,293,80,60,60,70,50,60,45,70,95,65,
50,65,85,55,104,78,78,91,65,148,111,178,223,151,122,151,181,113,92,69,
122,151,103,146,181,269,167,94,113,167,233,137,136,102,102,119,85,172,
129,214,263,181,146,181,227,149,268,201,326,383,269,482,577,739,461,
314,373,461,587,353,164,123,202,239,167,314,373,461,283,382,443,587,
967,547,218,271,353,547,797,401,88,66,66,77,55,116,87,142,173,113,94,
113,149,97,164,123,202,239,167,314,373,461,283,166,199,283,367,211,236,
177,278,337,233,382,443,587,367,662,757,967,1523,919,358,421,547,919,
1153,599,124,93,158,193,137,218,271,353,211,358,421,547,919,431,554,
647,797,1153,2221,1063,254,293,401,599,1063,1787,709,256,192,192,224,
160,192,144,224,304,208,160,208,272,176,192,144,144,168,120,224,168,
304,424,296,208,296,344,232,160,120,208,296,184,272,344,536,328,176,
232,328,472,248,192,144,144,168,120,144,108,168,228,156,120,156,204,
132,224,168,168,196,140,304,228,424,524,356,296,356,428,284,208,156,
296,356,244,344,428,652,404,232,284,404,556,316,160,120,120,140,100,
208,156,296,356,244,184,244,292,188,272,204,344,428,292,536,652,964,
628,328,404,628,764,436,176,132,232,284,188,328,404,628,332,472,556,
764,1324,716,248,316,436,716,1108,508,192,144,144,168,120,144,108,168,
228,156,120,156,204,132,144,108,108,126,90,168,126,228,318,222,156,222,
258,174,120,90,156,222,138,204,258,402,246,132,174,246,354,186,224,168,
168,196,140,168,126,196,266,182,140,182,238,154,304,228,228,266,190,
424,318,524,622,446,356,446,526,346,296,222,356,446,302,428,526,766,
478,284,346,478,674,386,208,156,156,182,130,296,222,356,446,302,244,
302,362,226,344,258,428,526,362,652,766,1154,746,404,478,746,886,542,
232,174,284,346,226,404,478,746,398,556,674,886,1514,842,316,386,542,
842,1294,586,160,120,120,140,100,120,90,140,190,130,100,130,170,110,
208,156,156,182,130,296,222,356,446,302,244,302,362,226,184,138,244,
302,206,292,362,538,334,188,226,334,466,274,272,204,204,238,170,344,
258,428,526,362,292,362,454,298,536,402,652,766,538,964,1154,1478,922,
628,746,922,1174,706,328,246,404,478,334,628,746,922,566,764,886,1174,
1934,1094,436,542,706,1094,1594,802,176,132,132,154,110,232,174,284,
346,226,188,226,298,194,328,246,404,478,334,628,746,922,566,332,398,
566,734,422,472,354,556,674,466,764,886,1174,734,1324,1514,1934,3046,
1838,716,842,1094,1838,2306,1198,248,186,316,386,274,436,542,706,422,
716,842,1094,1838,862,1108,1294,1594,2306,4442,2126,508,586,802,1198,
2126,3574,1418,192,144,144,168,120,144,108,168,228,156,120,156,204,132,
144,108,108,126,90,168,126,228,318,222,156,222,258,174,120,90,156,222,
138,204,258,402,246,132,174,246,354,186,144,108,108,126,90,108,81,126,
171,117,90,117,153,99,168,126,126,147,105,228,171,318,393,267,222,267,
321,213,156,117,222,267,183,258,321,489,303,174,213,303,417,237,120,90,
90,105,75,156,117,222,267,183,138,183,219,141,204,153,258,321,219,402,
489,723,471,246,303,471,573,327,132,99,174,213,141,246,303,471,249,354,
417,573,993,537,186,237,327,537,831,381,224,168,168,196,140,168,126,
196,266,182,140,182,238,154,168,126,126,147,105,196,147,266,371,259,
182,259,301,203,140,105,182,259,161,238,301,469,287,154,203,287,413,
217,304,228,228,266,190,228,171,266,361,247,190,247,323,209,424,318,
318,371,265,524,393,622,719,503,446,503,613,409,356,267,446,503,359,
526,613,881,569,346,409,569,769,457,296,222,222,259,185,356,267,446,
503,359,302,359,433,281,428,321,526,613,433,766,881,1301,857,478,569,
857,1021,641,284,213,346,409,281,478,569,857,479,674,769,1021,1721,971,
386,457,641,971,1487,683,208,156,156,182,130,156,117,182,247,169,130,
169,221,143,296,222,222,259,185,356,267,446,503,359,302,359,433,281,
244,183,302,359,251,362,433,619,397,226,281,397,557,317,344,258,258,
301,215,428,321,526,613,433,362,433,521,349,652,489,766,881,619,1154,
1301,1667,1061,746,857,1061,1307,821,404,303,478,569,397,746,857,1061,
673,886,1021,1307,2161,1231,542,641,821,1231,1789,929,232,174,174,203,
145,284,213,346,409,281,226,281,349,229,404,303,478,569,397,746,857,
1061,673,398,479,673,839,491,556,417,674,769,557,886,1021,1307,839,
1514,1721,2161,3449,2083,842,971,1231,2083,2633,1361,316,237,386,457,
317,542,641,821,491,842,971,1231,2083,983,1294,1487,1789,2633,4951,
2411,586,683,929,1361,2411,4013,1609,160,120,120,140,100,120,90,140,
190,130,100,130,170,110,120,90,90,105,75,140,105,190,265,185,130,185,
215,145,100,75,130,185,115,170,215,335,205,110,145,205,295,155,208,156,
156,182,130,156,117,182,247,169,130,169,221,143,296,222,222,259,185,
356,267,446,503,359,302,359,433,281,244,183,302,359,251,362,433,619,
397,226,281,397,557,317,184,138,138,161,115,244,183,302,359,251,206,
251,307,197,292,219,362,433,307,538,619,937,607,334,397,607,727,449,
188,141,226,281,197,334,397,607,347,466,557,727,1229,677,274,317,449,
677,1051,487,272,204,204,238,170,204,153,238,323,221,170,221,289,187,
344,258,258,301,215,428,321,526,613,433,362,433,521,349,292,219,362,
433,307,454,521,751,467,298,349,467,653,389,536,402,402,469,335,652,
489,766,881,619,538,619,751,499,964,723,1154,1301,937,1478,1667,2063,
1409,922,1061,1409,1669,1031,628,471,746,857,607,922,1061,1409,877,
1174,1307,1669,2647,1499,706,821,1031,1499,2269,1171,328,246,246,287,
205,404,303,478,569,397,334,397,467,313,628,471,746,857,607,922,1061,
1409,877,566,673,877,1087,617,764,573,886,1021,727,1174,1307,1669,1087,
1934,2161,2647,4217,2549,1094,1231,1499,2549,3109,1741,436,327,542,641,
449,706,821,1031,617,1094,1231,1499,2549,1217,1594,1789,2269,3109,5749,
2909,802,929,1171,1741,2909,4801,1913,176,132,132,154,110,132,99,154,
209,143,110,143,187,121,232,174,174,203,145,284,213,346,409,281,226,
281,349,229,188,141,226,281,197,298,349,499,313,194,229,313,439,257,
328,246,246,287,205,404,303,478,569,397,334,397,467,313,628,471,746,
857,607,922,1061,1409,877,566,673,877,1087,617,332,249,398,479,347,566,
673,877,563,734,839,1087,1723,991,422,491,617,991,1471,773,472,354,354,
413,295,556,417,674,769,557,466,557,653,439,764,573,886,1021,727,1174,
1307,1669,1087,734,839,1087,1433,859,1324,993,1514,1721,1229,1934,2161,
2647,1723,3046,3449,4217,5623,3259,1838,2083,2549,3259,4273,2381,716,
537,842,971,677,1094,1231,1499,991,1838,2083,2549,3259,1847,2306,2633,
3109,4273,7607,3943,1198,1361,1741,2381,3943,6113,2749,248,186,186,217,
155,316,237,386,457,317,274,317,389,257,436,327,542,641,449,706,821,
1031,617,422,491,617,859,509,716,537,842,971,677,1094,1231,1499,991,
1838,2083,2549,3259,1847,862,983,1217,1847,2477,1297,1108,831,1294,
1487,1051,1594,1789,2269,1471,2306,2633,3109,4273,2477,4442,4951,5749,
7607,12763,7193,2126,2411,2909,3943,7193,9319,4397,508,381,586,683,487,
802,929,1171,773,1198,1361,1741,2381,1297,2126,2411,2909,3943,7193,
3001,3574,4013,4801,6113,9319,19577,8527,1418,1609,1913,2749,4397,8527,
15299,5381,512,384,384,448,320,384,288,448,608,416,320,416,544,352,384,
288,288,336,240,448,336,608,848,592,416,592,688,464,320,240,416,592,
368,544,688,1072,656,352,464,656,944,496,384,288,288,336,240,288,216,
336,456,312,240,312,408,264,448,336,336,392,280,608,456,848,1048,712,
592,712,856,568,416,312,592,712,488,688,856,1304,808,464,568,808,1112,
632,320,240,240,280,200,416,312,592,712,488,368,488,584,376,544,408,
688,856,584,1072,1304,1928,1256,656,808,1256,1528,872,352,264,464,568,
376,656,808,1256,664,944,1112,1528,2648,1432,496,632,872,1432,2216,
1016,384,288,288,336,240,288,216,336,456,312,240,312,408,264,288,216,
216,252,180,336,252,456,636,444,312,444,516,348,240,180,312,444,276,
408,516,804,492,264,348,492,708,372,448,336,336,392,280,336,252,392,
532,364,280,364,476,308,608,456,456,532,380,848,636,1048,1244,892,712,
892,1052,692,592,444,712,892,604,856,1052,1532,956,568,692,956,1348,
772,416,312,312,364,260,592,444,712,892,604,488,604,724,452,688,516,
856,1052,724,1304,1532,2308,1492,808,956,1492,1772,1084,464,348,568,
692,452,808,956,1492,796,1112,1348,1772,3028,1684,632,772,1084,1684,
2588,1172,320,240,240,280,200,240,180,280,380,260,200,260,340,220,416,
312,312,364,260,592,444,712,892,604,488,604,724,452,368,276,488,604,
412,584,724,1076,668,376,452,668,932,548,544,408,408,476,340,688,516,
856,1052,724,584,724,908,596,1072,804,1304,1532,1076,1928,2308,2956,
1844,1256,1492,1844,2348,1412,656,492,808,956,668,1256,1492,1844,1132,
1528,1772,2348,3868,2188,872,1084,1412,2188,3188,1604,352,264,264,308,
220,464,348,568,692,452,376,452,596,388,656,492,808,956,668,1256,1492,
1844,1132,664,796,1132,1468,844,944,708,1112,1348,932,1528,1772,2348,
1468,2648,3028,3868,6092,3676,1432,1684,2188,3676,4612,2396,496,372,
632,772,548,872,1084,1412,844,1432,1684,2188,3676,1724,2216,2588,3188,
4612,8884,4252,1016,1172,1604,2396,4252,7148,2836,384,288,288,336,240,
288,216,336,456,312,240,312,408,264,288,216,216,252,180,336,252,456,
636,444,312,444,516,348,240,180,312,444,276,408,516,804,492,264,348,
492,708,372,288,216,216,252,180,216,162,252,342,234,180,234,306,198,
336,252,252,294,210,456,342,636,786,534,444,534,642,426,312,234,444,
534,366,516,642,978,606,348,426,606,834,474,240,180,180,210,150,312,
234,444,534,366,276,366,438,282,408,306,516,642,438,804,978,1446,942,
492,606,942,1146,654,264,198,348,426,282,492,606,942,498,708,834,1146,
1986,1074,372,474,654,1074,1662,762,448,336,336,392,280,336,252,392,
532,364,280,364,476,308,336,252,252,294,210,392,294,532,742,518,364,
518,602,406,280,210,364,518,322,476,602,938,574,308,406,574,826,434,
608,456,456,532,380,456,342,532,722,494,380,494,646,418,848,636,636,
742,530,1048,786,1244,1438,1006,892,1006,1226,818,712,534,892,1006,718,
1052,1226,1762,1138,692,818,1138,1538,914,592,444,444,518,370,712,534,
892,1006,718,604,718,866,562,856,642,1052,1226,866,1532,1762,2602,1714,
956,1138,1714,2042,1282,568,426,692,818,562,956,1138,1714,958,1348,
1538,2042,3442,1942,772,914,1282,1942,2974,1366,416,312,312,364,260,
312,234,364,494,338,260,338,442,286,592,444,444,518,370,712,534,892,
1006,718,604,718,866,562,488,366,604,718,502,724,866,1238,794,452,562,
794,1114,634,688,516,516,602,430,856,642,1052,1226,866,724,866,1042,
698,1304,978,1532,1762,1238,2308,2602,3334,2122,1492,1714,2122,2614,
1642,808,606,956,1138,794,1492,1714,2122,1346,1772,2042,2614,4322,2462,
1084,1282,1642,2462,3578,1858,464,348,348,406,290,568,426,692,818,562,
452,562,698,458,808,606,956,1138,794,1492,1714,2122,1346,796,958,1346,
1678,982,1112,834,1348,1538,1114,1772,2042,2614,1678,3028,3442,4322,
6898,4166,1684,1942,2462,4166,5266,2722,632,474,772,914,634,1084,1282,
1642,982,1684,1942,2462,4166,1966,2588,2974,3578,5266,9902,4822,1172,
1366,1858,2722,4822,8026,3218,320,240,240,280,200,240,180,280,380,260,
200,260,340,220,240,180,180,210,150,280,210,380,530,370,260,370,430,
290,200,150,260,370,230,340,430,670,410,220,290,410,590,310,416,312,
312,364,260,312,234,364,494,338,260,338,442,286,592,444,444,518,370,
712,534,892,1006,718,604,718,866,562,488,366,604,718,502,724,866,1238,
794,452,562,794,1114,634,368,276,276,322,230,488,366,604,718,502,412,
502,614,394,584,438,724,866,614,1076,1238,1874,1214,668,794,1214,1454,
898,376,282,452,562,394,668,794,1214,694,932,1114,1454,2458,1354,548,
634,898,1354,2102,974,544,408,408,476,340,408,306,476,646,442,340,442,
578,374,688,516,516,602,430,856,642,1052,1226,866,724,866,1042,698,584,
438,724,866,614,908,1042,1502,934,596,698,934,1306,778,1072,804,804,
938,670,1304,978,1532,1762,1238,1076,1238,1502,998,1928,1446,2308,2602,
1874,2956,3334,4126,2818,1844,2122,2818,3338,2062,1256,942,1492,1714,
1214,1844,2122,2818,1754,2348,2614,3338,5294,2998,1412,1642,2062,2998,
4538,2342,656,492,492,574,410,808,606,956,1138,794,668,794,934,626,
1256,942,1492,1714,1214,1844,2122,2818,1754,1132,1346,1754,2174,1234,
1528,1146,1772,2042,1454,2348,2614,3338,2174,3868,4322,5294,8434,5098,
2188,2462,2998,5098,6218,3482,872,654,1084,1282,898,1412,1642,2062,
1234,2188,2462,2998,5098,2434,3188,3578,4538,6218,11498,5818,1604,1858,
2342,3482,5818,9602,3826,352,264,264,308,220,264,198,308,418,286,220,
286,374,242,464,348,348,406,290,568,426,692,818,562,452,562,698,458,
376,282,452,562,394,596,698,998,626,388,458,626,878,514,656,492,492,
574,410,808,606,956,1138,794,668,794,934,626,1256,942,1492,1714,1214,
1844,2122,2818,1754,1132,1346,1754,2174,1234,664,498,796,958,694,1132,
1346,1754,1126,1468,1678,2174,3446,1982,844,982,1234,1982,2942,1546,
944,708,708,826,590,1112,834,1348,1538,1114,932,1114,1306,878,1528,
1146,1772,2042,1454,2348,2614,3338,2174,1468,1678,2174,2866,1718,2648,
1986,3028,3442,2458,3868,4322,5294,3446,6092,6898,8434,11246,6518,3676,
4166,5098,6518,8546,4762,1432,1074,1684,1942,1354,2188,2462,2998,1982,
3676,4166,5098,6518,3694,4612,5266,6218,8546,15214,7886,2396,2722,3482,
4762,7886,12226,5498,496,372,372,434,310,632,474,772,914,634,548,634,
778,514,872,654,1084,1282,898,1412,1642,2062,1234,844,982,1234,1718,
1018,1432,1074,1684,1942,1354,2188,2462,2998,1982,3676,4166,5098,6518,
3694,1724,1966,2434,3694,4954,2594,2216,1662,2588,2974,2102,3188,3578,
4538,2942,4612,5266,6218,8546,4954,8884,9902,11498,15214,25526,14386,
4252,4822,5818,7886,14386,18638,8794,1016,762,1172,1366,974,1604,1858,
2342,1546,2396,2722,3482,4762,2594,4252,4822,5818,7886,14386,6002,7148,
8026,9602,12226,18638,39154,17054,2836,3218,3826,5498,8794,17054,30598,
10762,384,288,288,336,240,288,216,336,456,312,240,312,408,264,288,216,
216,252,180,336,252,456,636,444,312,444,516,348,240,180,312,444,276,
408,516,804,492,264,348,492,708,372,288,216,216,252,180,216,162,252,
342,234,180,234,306,198,336,252,252,294,210,456,342,636,786,534,444,
534,642,426,312,234,444,534,366,516,642,978,606,348,426,606,834,474,
240,180,180,210,150,312,234,444,534,366,276,366,438,282,408,306,516,
642,438,804,978,1446,942,492,606,942,1146,654,264,198,348,426,282,492,
606,942,498,708,834,1146,1986,1074,372,474,654,1074,1662,762,288,216,
216,252,180,216,162,252,342,234,180,234,306,198,216,162,162,189,135,
252,189,342,477,333,234,333,387,261,180,135,234,333,207,306,387,603,
369,198,261,369,531,279,336,252,252,294,210,252,189,294,399,273,210,
273,357,231,456,342,342,399,285,636,477,786,933,669,534,669,789,519,
444,333,534,669,453,642,789,1149,717,426,519,717,1011,579,312,234,234,
273,195,444,333,534,669,453,366,453,543,339,516,387,642,789,543,978,
1149,1731,1119,606,717,1119,1329,813,348,261,426,519,339,606,717,1119,
597,834,1011,1329,2271,1263,474,579,813,1263,1941,879,240,180,180,210,
150,180,135,210,285,195,150,195,255,165,312,234,234,273,195,444,333,
534,669,453,366,453,543,339,276,207,366,453,309,438,543,807,501,282,
339,501,699,411,408,306,306,357,255,516,387,642,789,543,438,543,681,
447,804,603,978,1149,807,1446,1731,2217,1383,942,1119,1383,1761,1059,
492,369,606,717,501,942,1119,1383,849,1146,1329,1761,2901,1641,654,813,
1059,1641,2391,1203,264,198,198,231,165,348,261,426,519,339,282,339,
447,291,492,369,606,717,501,942,1119,1383,849,498,597,849,1101,633,708,
531,834,1011,699,1146,1329,1761,1101,1986,2271,2901,4569,2757,1074,
1263,1641,2757,3459,1797,372,279,474,579,411,654,813,1059,633,1074,
1263,1641,2757,1293,1662,1941,2391,3459,6663,3189,762,879,1203,1797,
3189,5361,2127,448,336,336,392,280,336,252,392,532,364,280,364,476,308,
336,252,252,294,210,392,294,532,742,518,364,518,602,406,280,210,364,
518,322,476,602,938,574,308,406,574,826,434,336,252,252,294,210,252,
189,294,399,273,210,273,357,231,392,294,294,343,245,532,399,742,917,
623,518,623,749,497,364,273,518,623,427,602,749,1141,707,406,497,707,
973,553,280,210,210,245,175,364,273,518,623,427,322,427,511,329,476,
357,602,749,511,938,1141,1687,1099,574,707,1099,1337,763,308,231,406,
497,329,574,707,1099,581,826,973,1337,2317,1253,434,553,763,1253,1939,
889,608,456,456,532,380,456,342,532,722,494,380,494,646,418,456,342,
342,399,285,532,399,722,1007,703,494,703,817,551,380,285,494,703,437,
646,817,1273,779,418,551,779,1121,589,848,636,636,742,530,636,477,742,
1007,689,530,689,901,583,1048,786,786,917,655,1244,933,1438,1619,1163,
1006,1163,1423,941,892,669,1006,1163,827,1226,1423,2003,1283,818,941,
1283,1747,1049,712,534,534,623,445,892,669,1006,1163,827,718,827,997,
659,1052,789,1226,1423,997,1762,2003,2939,1949,1138,1283,1949,2311,
1459,692,519,818,941,659,1138,1283,1949,1097,1538,1747,2311,3863,2203,
914,1049,1459,2203,3347,1571,592,444,444,518,370,444,333,518,703,481,
370,481,629,407,712,534,534,623,445,892,669,1006,1163,827,718,827,997,
659,604,453,718,827,593,866,997,1439,911,562,659,911,1249,743,856,642,
642,749,535,1052,789,1226,1423,997,866,997,1193,809,1532,1149,1762,
2003,1439,2602,2939,3767,2393,1714,1949,2393,2969,1861,956,717,1138,
1283,911,1714,1949,2393,1549,2042,2311,2969,4871,2777,1282,1459,1861,
2777,4021,2089,568,426,426,497,355,692,519,818,941,659,562,659,809,541,
956,717,1138,1283,911,1714,1949,2393,1549,958,1097,1549,1907,1123,1348,
1011,1538,1747,1249,2042,2311,2969,1907,3442,3863,4871,7589,4649,1942,
2203,2777,4649,5821,3041,772,579,914,1049,743,1282,1459,1861,1123,1942,
2203,2777,4649,2237,2974,3347,4021,5821,10889,5419,1366,1571,2089,3041,
5419,8893,3631,416,312,312,364,260,312,234,364,494,338,260,338,442,286,
312,234,234,273,195,364,273,494,689,481,338,481,559,377,260,195,338,
481,299,442,559,871,533,286,377,533,767,403,592,444,444,518,370,444,
333,518,703,481,370,481,629,407,712,534,534,623,445,892,669,1006,1163,
827,718,827,997,659,604,453,718,827,593,866,997,1439,911,562,659,911,
1249,743,488,366,366,427,305,604,453,718,827,593,502,593,701,463,724,
543,866,997,701,1238,1439,2111,1399,794,911,1399,1627,1033,452,339,562,
659,463,794,911,1399,787,1114,1249,1627,2753,1559,634,743,1033,1559,
2383,1109,688,516,516,602,430,516,387,602,817,559,430,559,731,473,856,
642,642,749,535,1052,789,1226,1423,997,866,997,1193,809,724,543,866,
997,701,1042,1193,1699,1091,698,809,1091,1493,887,1304,978,978,1141,
815,1532,1149,1762,2003,1439,1238,1439,1699,1151,2308,1731,2602,2939,
2111,3334,3767,4597,3137,2122,2393,3137,3779,2339,1492,1119,1714,1949,
1399,2122,2393,3137,1997,2614,2969,3779,5839,3391,1642,1861,2339,3391,
5023,2663,808,606,606,707,505,956,717,1138,1283,911,794,911,1091,733,
1492,1119,1714,1949,1399,2122,2393,3137,1997,1346,1549,1997,2441,1429,
1772,1329,2042,2311,1627,2614,2969,3779,2441,4322,4871,5839,9323,5659,
2462,2777,3391,5659,6883,3917,1084,813,1282,1459,1033,1642,1861,2339,
1429,2462,2777,3391,5659,2729,3578,4021,5023,6883,12671,6491,1858,2089,
2663,3917,6491,10607,4271,464,348,348,406,290,348,261,406,551,377,290,
377,493,319,568,426,426,497,355,692,519,818,941,659,562,659,809,541,
452,339,562,659,463,698,809,1151,733,458,541,733,1013,601,808,606,606,
707,505,956,717,1138,1283,911,794,911,1091,733,1492,1119,1714,1949,
1399,2122,2393,3137,1997,1346,1549,1997,2441,1429,796,597,958,1097,787,
1346,1549,1997,1277,1678,1907,2441,3881,2243,982,1123,1429,2243,3313,
1759,1112,834,834,973,695,1348,1011,1538,1747,1249,1114,1249,1493,1013,
1772,1329,2042,2311,1627,2614,2969,3779,2441,1678,1907,2441,3209,1973,
3028,2271,3442,3863,2753,4322,4871,5839,3881,6898,7589,9323,12379,7213,
4166,4649,5659,7213,9473,5333,1684,1263,1942,2203,1559,2462,2777,3391,
2243,4166,4649,5659,7213,4111,5266,5821,6883,9473,16729,8779,2722,3041,
3917,5333,8779,13451,6151,632,474,474,553,395,772,579,914,1049,743,634,
743,887,601,1084,813,1282,1459,1033,1642,1861,2339,1429,982,1123,1429,
1973,1181,1684,1263,1942,2203,1559,2462,2777,3391,2243,4166,4649,5659,
7213,4111,1966,2237,2729,4111,5563,2917,2588,1941,2974,3347,2383,3578,
4021,5023,3313,5266,5821,6883,9473,5563,9902,10889,12671,16729,27917,
15761,4822,5419,6491,8779,15761,20407,9719,1172,879,1366,1571,1109,
1858,2089,2663,1759,2722,3041,3917,5333,2917,4822,5419,6491,8779,15761,
6689,8026,8893,10607,13451,20407,42463,18583,3218,3631,4271,6151,9719,
18583,33359,11827,320,240,240,280,200,240,180,280,380,260,200,260,340,
220,240,180,180,210,150,280,210,380,530,370,260,370,430,290,200,150,
260,370,230,340,430,670,410,220,290,410,590,310,240,180,180,210,150,
180,135,210,285,195,150,195,255,165,280,210,210,245,175,380,285,530,
655,445,370,445,535,355,260,195,370,445,305,430,535,815,505,290,355,
505,695,395,200,150,150,175,125,260,195,370,445,305,230,305,365,235,
340,255,430,535,365,670,815,1205,785,410,505,785,955,545,220,165,290,
355,235,410,505,785,415,590,695,955,1655,895,310,395,545,895,1385,635,
416,312,312,364,260,312,234,364,494,338,260,338,442,286,312,234,234,
273,195,364,273,494,689,481,338,481,559,377,260,195,338,481,299,442,
559,871,533,286,377,533,767,403,592,444,444,518,370,444,333,518,703,
481,370,481,629,407,712,534,534,623,445,892,669,1006,1163,827,718,827,
997,659,604,453,718,827,593,866,997,1439,911,562,659,911,1249,743,488,
366,366,427,305,604,453,718,827,593,502,593,701,463,724,543,866,997,
701,1238,1439,2111,1399,794,911,1399,1627,1033,452,339,562,659,463,794,
911,1399,787,1114,1249,1627,2753,1559,634,743,1033,1559,2383,1109,368,
276,276,322,230,276,207,322,437,299,230,299,391,253,488,366,366,427,
305,604,453,718,827,593,502,593,701,463,412,309,502,593,419,614,701,
1019,643,394,463,643,883,523,584,438,438,511,365,724,543,866,997,701,
614,701,853,571,1076,807,1238,1439,1019,1874,2111,2699,1709,1214,1399,
1709,2131,1303,668,501,794,911,643,1214,1399,1709,1093,1454,1627,2131,
3499,1999,898,1033,1303,1999,2879,1489,376,282,282,329,235,452,339,562,
659,463,394,463,571,379,668,501,794,911,643,1214,1399,1709,1093,694,
787,1093,1367,811,932,699,1114,1249,883,1454,1627,2131,1367,2458,2753,
3499,5477,3343,1354,1559,1999,3343,4159,2179,548,411,634,743,523,898,
1033,1303,811,1354,1559,1999,3343,1579,2102,2383,2879,4159,7867,3877,
974,1109,1489,2179,3877,6373,2621,544,408,408,476,340,408,306,476,646,
442,340,442,578,374,408,306,306,357,255,476,357,646,901,629,442,629,
731,493,340,255,442,629,391,578,731,1139,697,374,493,697,1003,527,688,
516,516,602,430,516,387,602,817,559,430,559,731,473,856,642,642,749,
535,1052,789,1226,1423,997,866,997,1193,809,724,543,866,997,701,1042,
1193,1699,1091,698,809,1091,1493,887,584,438,438,511,365,724,543,866,
997,701,614,701,853,571,908,681,1042,1193,853,1502,1699,2539,1637,934,
1091,1637,1993,1237,596,447,698,809,571,934,1091,1637,947,1306,1493,
1993,3329,1873,778,887,1237,1873,2843,1327,1072,804,804,938,670,804,
603,938,1273,871,670,871,1139,737,1304,978,978,1141,815,1532,1149,1762,
2003,1439,1238,1439,1699,1151,1076,807,1238,1439,1019,1502,1699,2437,
1567,998,1151,1567,2141,1289,1928,1446,1446,1687,1205,2308,1731,2602,
2939,2111,1874,2111,2539,1697,2956,2217,3334,3767,2699,4126,4597,5441,
3593,2818,3137,3593,4517,2803,1844,1383,2122,2393,1709,2818,3137,3593,
2417,3338,3779,4517,6841,4133,2062,2339,2803,4133,5851,3229,1256,942,
942,1099,785,1492,1119,1714,1949,1399,1214,1399,1637,1103,1844,1383,
2122,2393,1709,2818,3137,3593,2417,1754,1997,2417,3019,1823,2348,1761,
2614,2969,2131,3338,3779,4517,3019,5294,5839,6841,10663,6653,2998,3391,
4133,6653,8117,4759,1412,1059,1642,1861,1303,2062,2339,2803,1823,2998,
3391,4133,6653,3407,4538,5023,5851,8117,14713,7649,2342,2663,3229,4759,
7649,12457,5107,656,492,492,574,410,492,369,574,779,533,410,533,697,
451,808,606,606,707,505,956,717,1138,1283,911,794,911,1091,733,668,501,
794,911,643,934,1091,1567,1009,626,733,1009,1381,823,1256,942,942,1099,
785,1492,1119,1714,1949,1399,1214,1399,1637,1103,1844,1383,2122,2393,
1709,2818,3137,3593,2417,1754,1997,2417,3019,1823,1132,849,1346,1549,
1093,1754,1997,2417,1597,2174,2441,3019,4567,2719,1234,1429,1823,2719,
4027,2099,1528,1146,1146,1337,955,1772,1329,2042,2311,1627,1454,1627,
1993,1319,2348,1761,2614,2969,2131,3338,3779,4517,3019,2174,2441,3019,
3733,2351,3868,2901,4322,4871,3499,5294,5839,6841,4567,8434,9323,10663,
14159,8513,5098,5659,6653,8513,10723,6311,2188,1641,2462,2777,1999,
2998,3391,4133,2719,5098,5659,6653,8513,5021,6218,6883,8117,10723,
19013,10009,3482,3917,4759,6311,10009,15313,7283,872,654,654,763,545,
1084,813,1282,1459,1033,898,1033,1237,829,1412,1059,1642,1861,1303,
2062,2339,2803,1823,1234,1429,1823,2351,1447,2188,1641,2462,2777,1999,
2998,3391,4133,2719,5098,5659,6653,8513,5021,2434,2729,3407,5021,6469,
3517,3188,2391,3578,4021,2879,4538,5023,5851,4027,6218,6883,8117,10723,
6469,11498,12671,14713,19013,32143,18181,5818,6491,7649,10009,18181,
23669,11257,1604,1203,1858,2089,1489,2342,2663,3229,2099,3482,3917,
4759,6311,3517,5818,6491,7649,10009,18181,7753,9602,10607,12457,15313,
23669,48073,21493,3826,4271,5107,7283,11257,21493,37967,13613,352,264,
264,308,220,264,198,308,418,286,220,286,374,242,264,198,198,231,165,
308,231,418,583,407,286,407,473,319,220,165,286,407,253,374,473,737,
451,242,319,451,649,341,464,348,348,406,290,348,261,406,551,377,290,
377,493,319,568,426,426,497,355,692,519,818,941,659,562,659,809,541,
452,339,562,659,463,698,809,1151,733,458,541,733,1013,601,376,282,282,
329,235,452,339,562,659,463,394,463,571,379,596,447,698,809,571,998,
1151,1697,1103,626,733,1103,1319,829,388,291,458,541,379,626,733,1103,
631,878,1013,1319,2251,1259,514,601,829,1259,1933,907,656,492,492,574,
410,492,369,574,779,533,410,533,697,451,808,606,606,707,505,956,717,
1138,1283,911,794,911,1091,733,668,501,794,911,643,934,1091,1567,1009,
626,733,1009,1381,823,1256,942,942,1099,785,1492,1119,1714,1949,1399,
1214,1399,1637,1103,1844,1383,2122,2393,1709,2818,3137,3593,2417,1754,
1997,2417,3019,1823,1132,849,1346,1549,1093,1754,1997,2417,1597,2174,
2441,3019,4567,2719,1234,1429,1823,2719,4027,2099,664,498,498,581,415,
796,597,958,1097,787,694,787,947,631,1132,849,1346,1549,1093,1754,1997,
2417,1597,1126,1277,1597,2027,1201,1468,1101,1678,1907,1367,2174,2441,
3019,2027,3446,3881,4567,7351,4463,1982,2243,2719,4463,5503,3169,844,
633,982,1123,811,1234,1429,1823,1201,1982,2243,2719,4463,2341,2942,
3313,4027,5503,9973,5059,1546,1759,2099,3169,5059,8389,3469,944,708,
708,826,590,708,531,826,1121,767,590,767,1003,649,1112,834,834,973,695,
1348,1011,1538,1747,1249,1114,1249,1493,1013,932,699,1114,1249,883,
1306,1493,2141,1381,878,1013,1381,1879,1117,1528,1146,1146,1337,955,
1772,1329,2042,2311,1627,1454,1627,1993,1319,2348,1761,2614,2969,2131,
3338,3779,4517,3019,2174,2441,3019,3733,2351,1468,1101,1678,1907,1367,
2174,2441,3019,2027,2866,3209,3733,5701,3319,1718,1973,2351,3319,4877,
2683,2648,1986,1986,2317,1655,3028,2271,3442,3863,2753,2458,2753,3329,
2251,3868,2901,4322,4871,3499,5294,5839,6841,4567,3446,3881,4567,5701,
3559,6092,4569,6898,7589,5477,8434,9323,10663,7351,11246,12379,14159,
17987,11743,6518,7213,8513,11743,14177,8221,3676,2757,4166,4649,3343,
5098,5659,6653,4463,6518,7213,8513,11743,6823,8546,9473,10723,14177,
23801,12547,4762,5333,6311,8221,12547,20063,9461,1432,1074,1074,1253,
895,1684,1263,1942,2203,1559,1354,1559,1873,1259,2188,1641,2462,2777,
1999,2998,3391,4133,2719,1982,2243,2719,3319,2081,3676,2757,4166,4649,
3343,5098,5659,6653,4463,6518,7213,8513,11743,6823,3694,4111,5021,6823,
8719,4549,4612,3459,5266,5821,4159,6218,6883,8117,5503,8546,9473,10723,
14177,8719,15214,16729,19013,23801,40151,22811,7886,8779,10009,12547,
22811,28573,14867,2396,1797,2722,3041,2179,3482,3917,4759,3169,4762,
5333,6311,8221,4549,7886,8779,10009,12547,22811,9859,12226,13451,15313,
20063,28573,56701,26489,5498,6151,7283,9461,14867,26489,46451,16519,
496,372,372,434,310,372,279,434,589,403,310,403,527,341,632,474,474,
553,395,772,579,914,1049,743,634,743,887,601,548,411,634,743,523,778,
887,1289,823,514,601,823,1117,661,872,654,654,763,545,1084,813,1282,
1459,1033,898,1033,1237,829,1412,1059,1642,1861,1303,2062,2339,2803,
1823,1234,1429,1823,2351,1447,844,633,982,1123,811,1234,1429,1823,1201,
1718,1973,2351,3559,2081,1018,1181,1447,2081,3067,1621,1432,1074,1074,
1253,895,1684,1263,1942,2203,1559,1354,1559,1873,1259,2188,1641,2462,
2777,1999,2998,3391,4133,2719,1982,2243,2719,3319,2081,3676,2757,4166,
4649,3343,5098,5659,6653,4463,6518,7213,8513,11743,6823,3694,4111,5021,
6823,8719,4549,1724,1293,1966,2237,1579,2434,2729,3407,2341,3694,4111,
5021,6823,4091,4954,5563,6469,8719,14723,7841,2594,2917,3517,4549,7841,
12301,5869,2216,1662,1662,1939,1385,2588,1941,2974,3347,2383,2102,2383,
2843,1933,3188,2391,3578,4021,2879,4538,5023,5851,4027,2942,3313,4027,
4877,3067,4612,3459,5266,5821,4159,6218,6883,8117,5503,8546,9473,10723,
14177,8719,4954,5563,6469,8719,11953,6661,8884,6663,9902,10889,7867,
11498,12671,14713,9973,15214,16729,19013,23801,14723,25526,27917,32143,
40151,55351,30133,14386,15761,18181,22811,30133,40819,21179,4252,3189,
4822,5419,3877,5818,6491,7649,5059,7886,8779,10009,12547,7841,14386,
15761,18181,22811,30133,15823,18638,20407,23669,28573,40819,77431,
37217,8794,9719,11257,14867,21179,37217,60647,24859,1016,762,762,889,
635,1172,879,1366,1571,1109,974,1109,1327,907,1604,1203,1858,2089,1489,
2342,2663,3229,2099,1546,1759,2099,2683,1621,2396,1797,2722,3041,2179,
3482,3917,4759,3169,4762,5333,6311,8221,4549,2594,2917,3517,4549,6661,
3637,4252,3189,4822,5419,3877,5818,6491,7649,5059,7886,8779,10009,
12547,7841,14386,15761,18181,22811,30133,15823,6002,6689,7753,9859,
15823,22093,10631,7148,5361,8026,8893,6373,9602,10607,12457,8389,12226,
13451,15313,20063,12301,18638,20407,23669,28573,40819,22093,39154,
42463,48073,56701,77431,137077,72727,17054,18583,21493,26489,37217,
72727,96797,42043,2836,2127,3218,3631,2621,3826,4271,5107,3469,5498,
6151,7283,9461,5869,8794,9719,11257,14867,21179,10631,17054,18583,
21493,26489,37217,72727,27457,30598,33359,37967,46451,60647,96797,
219613,87803,10762,11827,13613,16519,24859,42043,87803,167449,52711};

ULI sA129593_up_to6917[6918] =
{1,2,4,3,8,9,9,9,5,16,27,27,6,25,27,25,6,27,25,25,25,25,7,32,81,81,18,
125,81,125,18,18,15,125,15,15,49,81,125,125,15,49,18,15,18,81,125,15,
125,15,49,125,49,15,125,49,15,15,125,49,49,49,49,49,11,64,243,243,54,
625,243,625,54,12,75,625,75,75,343,243,625,625,75,343,54,75,12,54,75,
75,75,10,35,625,343,75,75,35,75,10,75,35,343,35,35,35,121,243,625,625,
75,343,625,343,75,75,35,343,35,35,121,54,75,75,10,35,12,75,54,243,625,
75,625,75,343,75,35,75,625,343,10,75,75,35,35,343,35,35,121,625,343,
343,35,121,75,35,75,625,343,35,343,35,121,75,35,10,75,35,75,75,625,343,
35,35,343,35,121,343,121,35,343,121,35,35,343,121,35,35,35,343,121,121,
121,121,121,121,13,128,729,729,162,3125,729,3125,162,36,375,3125,375,
375,2401,729,3125,3125,375,2401,162,375,36,36,45,375,45,50,245,3125,
2401,375,45,245,375,50,45,245,2401,245,245,245,1331,729,3125,3125,375,
2401,3125,2401,375,45,245,2401,245,245,1331,162,375,375,50,245,36,45,
36,162,375,45,375,50,245,375,245,45,375,245,50,50,50,21,245,245,21,21,
77,3125,2401,2401,245,1331,375,245,45,375,245,245,245,21,77,375,245,50,
50,21,45,50,375,245,245,21,245,21,77,2401,1331,245,245,77,245,21,245,
77,245,21,21,245,77,1331,77,77,77,77,169,729,3125,3125,375,2401,3125,
2401,375,45,245,2401,245,245,1331,3125,2401,2401,245,1331,375,245,45,
375,245,245,245,21,77,2401,1331,245,245,77,245,21,245,77,1331,77,77,77,
169,162,375,375,50,245,375,245,50,50,21,245,21,21,77,36,45,45,50,245,
36,375,162,729,3125,375,3125,375,2401,45,245,375,3125,2401,50,375,45,
245,245,2401,245,245,1331,375,245,245,21,77,45,245,375,3125,2401,245,
2401,245,1331,50,21,50,375,245,50,45,375,245,21,245,245,21,77,245,77,
245,2401,1331,21,245,245,77,21,245,21,245,77,77,1331,77,77,77,169,3125,
2401,2401,245,1331,2401,1331,245,245,77,1331,77,77,169,375,245,245,21,
77,45,245,375,3125,2401,245,2401,245,1331,245,77,245,2401,1331,21,245,
245,77,77,1331,77,77,169,375,245,245,21,77,50,21,50,375,245,21,245,21,
77,45,245,50,45,245,375,375,3125,2401,245,245,2401,245,1331,245,77,21,
245,77,245,245,2401,1331,21,21,245,245,77,77,77,1331,77,77,169,2401,
1331,1331,77,169,245,77,245,2401,1331,77,1331,77,169,245,77,21,245,77,
245,245,2401,1331,77,77,1331,77,169,245,77,21,245,77,21,21,245,77,245,
245,245,2401,1331,77,77,77,1331,77,169,1331,169,77,1331,169,77,77,1331,
169,77,77,77,1331,169,77,77,77,77,1331,169,169,169,169,169,169,169,17,
256,2187,2187,486,15625,2187,15625,486,108,1875,15625,1875,1875,16807,
2187,15625,15625,1875,16807,486,1875,108,24,225,1875,225,250,1715,
15625,16807,1875,225,1715,1875,250,225,1715,16807,1715,1715,1715,14641,
2187,15625,15625,1875,16807,15625,16807,1875,225,1715,16807,1715,1715,
14641,486,1875,1875,250,1715,108,225,24,108,225,225,225,30,175,1875,
1715,225,225,175,250,30,30,147,1715,175,147,147,847,15625,16807,16807,
1715,14641,1875,1715,225,225,175,1715,175,147,847,1875,1715,250,30,147,
225,30,225,175,1715,147,175,147,847,16807,14641,1715,175,847,1715,147,
175,847,1715,147,147,175,847,14641,847,847,847,847,2197,2187,15625,
15625,1875,16807,15625,16807,1875,225,1715,16807,1715,1715,14641,15625,
16807,16807,1715,14641,1875,1715,225,225,175,1715,175,147,847,16807,
14641,1715,175,847,1715,147,175,847,14641,847,847,847,2197,486,1875,
1875,250,1715,1875,1715,250,30,147,1715,147,147,847,108,225,225,30,175,
24,225,108,486,1875,225,1875,250,1715,225,175,225,1875,1715,30,250,30,
147,175,1715,147,147,847,1875,1715,1715,147,847,225,175,225,1875,1715,
175,1715,147,847,250,147,30,250,147,30,30,250,147,147,147,147,14,55,
1715,847,175,1715,847,147,147,147,55,147,147,14,147,55,847,847,55,55,
55,143,15625,16807,16807,1715,14641,16807,14641,1715,175,847,14641,847,
847,2197,1875,1715,1715,147,847,225,175,225,1875,1715,175,1715,147,847,
1715,847,175,1715,847,147,147,147,55,847,847,55,55,143,1875,1715,1715,
147,847,250,147,30,250,147,147,147,14,55,225,175,30,30,147,225,250,
1875,1715,175,147,1715,147,847,1715,847,147,147,55,175,147,1715,847,
147,14,147,147,55,847,55,847,55,55,143,16807,14641,14641,847,2197,1715,
847,175,1715,847,847,847,55,143,1715,847,147,147,55,175,147,1715,847,
847,55,847,55,143,1715,847,147,147,55,147,14,147,55,175,147,147,1715,
847,847,55,55,847,55,143,14641,2197,847,847,143,847,55,847,143,847,55,
55,847,143,847,55,55,55,847,143,2197,143,143,143,143,143,289,2187,
15625,15625,1875,16807,15625,16807,1875,225,1715,16807,1715,1715,14641,
15625,16807,16807,1715,14641,1875,1715,225,225,175,1715,175,147,847,
16807,14641,1715,175,847,1715,147,175,847,14641,847,847,847,2197,15625,
16807,16807,1715,14641,16807,14641,1715,175,847,14641,847,847,2197,
1875,1715,1715,147,847,225,175,225,1875,1715,175,1715,147,847,1715,847,
175,1715,847,147,147,147,55,847,847,55,55,143,16807,14641,14641,847,
2197,1715,847,175,1715,847,847,847,55,143,1715,847,147,147,55,175,147,
1715,847,847,55,847,55,143,14641,2197,847,847,143,847,55,847,143,847,
55,55,847,143,2197,143,143,143,143,289,486,1875,1875,250,1715,1875,
1715,250,30,147,1715,147,147,847,1875,1715,1715,147,847,250,147,30,250,
147,147,147,14,55,1715,847,147,147,55,147,14,147,55,847,55,55,55,143,
108,225,225,30,175,225,175,30,30,147,175,147,147,847,24,225,225,250,
1715,108,1875,486,2187,15625,1875,15625,1875,16807,225,1715,1875,15625,
16807,250,1875,225,1715,1715,16807,1715,1715,14641,225,175,175,147,847,
225,1715,1875,15625,16807,1715,16807,1715,14641,30,147,250,1875,1715,
30,225,225,175,147,1715,175,147,847,175,847,1715,16807,14641,147,1715,
175,847,147,1715,147,175,847,847,14641,847,847,847,2197,1875,1715,1715,
147,847,1715,847,147,147,55,847,55,55,143,225,175,175,147,847,225,1715,
1875,15625,16807,1715,16807,1715,14641,175,847,1715,16807,14641,147,
1715,175,847,847,14641,847,847,2197,250,147,147,14,55,30,147,250,1875,
1715,147,1715,147,847,30,147,30,225,175,250,225,1875,1715,147,175,1715,
147,847,147,55,147,1715,847,147,175,1715,847,14,147,147,147,55,55,847,
847,55,55,143,1715,847,847,55,143,175,847,1715,16807,14641,847,14641,
847,2197,147,55,147,1715,847,147,175,1715,847,55,847,847,55,143,147,55,
147,1715,847,14,147,147,55,147,175,147,1715,847,55,847,55,847,55,143,
847,143,847,14641,2197,55,847,847,143,55,847,55,847,143,55,847,55,55,
847,143,143,2197,143,143,143,143,289,15625,16807,16807,1715,14641,
16807,14641,1715,175,847,14641,847,847,2197,16807,14641,14641,847,2197,
1715,847,175,1715,847,847,847,55,143,14641,2197,847,847,143,847,55,847,
143,2197,143,143,143,289,1875,1715,1715,147,847,1715,847,147,147,55,
847,55,55,143,225,175,175,147,847,225,1715,1875,15625,16807,1715,16807,
1715,14641,175,847,1715,16807,14641,147,1715,175,847,847,14641,847,847,
2197,1715,847,847,55,143,175,847,1715,16807,14641,847,14641,847,2197,
147,55,147,1715,847,147,175,1715,847,55,847,847,55,143,847,143,847,
14641,2197,55,847,847,143,55,847,55,847,143,143,2197,143,143,143,289,
1875,1715,1715,147,847,1715,847,147,147,55,847,55,55,143,250,147,147,
14,55,30,147,250,1875,1715,147,1715,147,847,147,55,147,1715,847,14,147,
147,55,55,847,55,55,143,225,175,175,147,847,30,147,30,225,175,147,175,
147,847,225,1715,250,225,1715,1875,1875,15625,16807,1715,1715,16807,
1715,14641,175,847,147,175,847,1715,1715,16807,14641,147,147,1715,175,
847,847,847,14641,847,847,2197,1715,847,847,55,143,147,55,147,1715,847,
55,847,55,143,175,847,147,175,847,1715,1715,16807,14641,847,847,14641,
847,2197,147,55,14,147,55,147,147,1715,847,147,147,175,1715,847,55,55,
847,847,55,143,847,143,55,847,143,847,847,14641,2197,55,55,847,847,143,
55,55,847,55,847,143,143,143,2197,143,143,143,289,16807,14641,14641,
847,2197,14641,2197,847,847,143,2197,143,143,289,1715,847,847,55,143,
175,847,1715,16807,14641,847,14641,847,2197,847,143,847,14641,2197,55,
847,847,143,143,2197,143,143,289,1715,847,847,55,143,147,55,147,1715,
847,55,847,55,143,175,847,147,175,847,1715,1715,16807,14641,847,847,
14641,847,2197,847,143,55,847,143,847,847,14641,2197,55,55,847,847,143,
143,143,2197,143,143,289,1715,847,847,55,143,147,55,147,1715,847,55,
847,55,143,147,55,14,147,55,147,147,1715,847,55,55,847,55,143,175,847,
147,175,847,147,147,175,847,1715,1715,1715,16807,14641,847,847,847,
14641,847,2197,847,143,55,847,143,55,55,847,143,847,847,847,14641,2197,
55,55,55,847,847,143,143,143,143,2197,143,143,289,14641,2197,2197,143,
289,847,143,847,14641,2197,143,2197,143,289,847,143,55,847,143,847,847,
14641,2197,143,143,2197,143,289,847,143,55,847,143,55,55,847,143,847,
847,847,14641,2197,143,143,143,2197,143,289,847,143,55,847,143,55,55,
847,143,55,55,55,847,143,847,847,847,847,14641,2197,143,143,143,143,
2197,143,289,2197,289,143,2197,289,143,143,2197,289,143,143,143,2197,
289,143,143,143,143,2197,289,143,143,143,143,143,2197,289,289,289,289,
289,289,289,289,19,512,6561,6561,1458,78125,6561,78125,1458,324,9375,
78125,9375,9375,117649,6561,78125,78125,9375,117649,1458,9375,324,72,
1125,9375,1125,1250,12005,78125,117649,9375,1125,12005,9375,1250,1125,
12005,117649,12005,12005,12005,161051,6561,78125,78125,9375,117649,
78125,117649,9375,1125,12005,117649,12005,12005,161051,1458,9375,9375,
1250,12005,324,1125,72,72,135,1125,135,150,1225,9375,12005,1125,135,
1225,1250,150,150,1029,12005,1225,1029,1029,9317,78125,117649,117649,
12005,161051,9375,12005,1125,135,1225,12005,1225,1029,9317,9375,12005,
1250,150,1029,1125,150,135,1225,12005,1029,1225,1029,9317,117649,
161051,12005,1225,9317,12005,1029,1225,9317,12005,1029,1029,1225,9317,
161051,9317,9317,9317,9317,28561,6561,78125,78125,9375,117649,78125,
117649,9375,1125,12005,117649,12005,12005,161051,78125,117649,117649,
12005,161051,9375,12005,1125,135,1225,12005,1225,1029,9317,117649,
161051,12005,1225,9317,12005,1029,1225,9317,161051,9317,9317,9317,
28561,1458,9375,9375,1250,12005,9375,12005,1250,150,1029,12005,1029,
1029,9317,324,1125,1125,150,1225,72,135,72,324,1125,135,1125,150,1225,
1125,1225,135,1125,1225,150,150,20,105,1225,1225,105,105,539,9375,
12005,12005,1029,9317,1125,1225,135,1125,1225,1225,1225,105,539,1250,
1029,150,150,105,150,20,150,105,1029,105,105,98,605,12005,9317,1225,
1225,539,1029,105,105,605,1029,105,98,105,605,9317,539,605,605,605,
1859,78125,117649,117649,12005,161051,117649,161051,12005,1225,9317,
161051,9317,9317,28561,9375,12005,12005,1029,9317,1125,1225,135,1125,
1225,1225,1225,105,539,12005,9317,1225,1225,539,1029,105,105,605,9317,
539,605,605,1859,9375,12005,12005,1029,9317,1250,1029,150,150,105,1029,
105,98,605,1125,1225,150,20,105,135,150,1125,1225,1225,105,1225,105,
539,12005,9317,1029,105,605,1225,105,1225,539,1029,98,105,105,605,9317,
605,539,605,605,1859,117649,161051,161051,9317,28561,12005,9317,1225,
1225,539,9317,539,605,1859,12005,9317,1029,105,605,1225,105,1225,539,
9317,605,539,605,1859,12005,9317,1029,105,605,1029,98,105,605,1225,105,
105,1225,539,9317,605,605,539,605,1859,161051,28561,9317,539,1859,9317,
605,539,1859,9317,605,605,539,1859,9317,605,605,605,539,1859,28561,
1859,1859,1859,1859,1859,4913,6561,78125,78125,9375,117649,78125,
117649,9375,1125,12005,117649,12005,12005,161051,78125,117649,117649,
12005,161051,9375,12005,1125,135,1225,12005,1225,1029,9317,117649,
161051,12005,1225,9317,12005,1029,1225,9317,161051,9317,9317,9317,
28561,78125,117649,117649,12005,161051,117649,161051,12005,1225,9317,
161051,9317,9317,28561,9375,12005,12005,1029,9317,1125,1225,135,1125,
1225,1225,1225,105,539,12005,9317,1225,1225,539,1029,105,105,605,9317,
539,605,605,1859,117649,161051,161051,9317,28561,12005,9317,1225,1225,
539,9317,539,605,1859,12005,9317,1029,105,605,1225,105,1225,539,9317,
605,539,605,1859,161051,28561,9317,539,1859,9317,605,539,1859,9317,605,
605,539,1859,28561,1859,1859,1859,1859,4913,1458,9375,9375,1250,12005,
9375,12005,1250,150,1029,12005,1029,1029,9317,9375,12005,12005,1029,
9317,1250,1029,150,150,105,1029,105,98,605,12005,9317,1029,105,605,
1029,98,105,605,9317,605,605,605,1859,324,1125,1125,150,1225,1125,1225,
150,20,105,1225,105,105,539,72,135,135,150,1225,72,1125,324,1458,9375,
1125,9375,1250,12005,135,1225,1125,9375,12005,150,1250,150,1029,1225,
12005,1029,1029,9317,1125,1225,1225,105,539,135,1225,1125,9375,12005,
1225,12005,1029,9317,150,105,150,1250,1029,20,150,150,105,105,1029,105,
98,605,1225,539,1225,12005,9317,105,1029,105,605,105,1029,98,105,605,
539,9317,605,605,605,1859,9375,12005,12005,1029,9317,12005,9317,1029,
105,605,9317,605,605,1859,1125,1225,1225,105,539,135,1225,1125,9375,
12005,1225,12005,1029,9317,1225,539,1225,12005,9317,105,1029,105,605,
539,9317,605,605,1859,1250,1029,1029,98,605,150,105,150,1250,1029,105,
1029,98,605,150,105,20,150,105,150,150,1250,1029,105,105,1029,98,605,
1029,605,105,1029,605,105,105,1029,605,98,98,98,98,33,605,605,605,33,
33,91,12005,9317,9317,605,1859,1225,539,1225,12005,9317,539,9317,605,
1859,1029,605,105,1029,605,105,105,1029,605,605,605,605,33,91,1029,605,
105,1029,605,98,98,98,33,105,105,98,1029,605,605,605,33,605,33,91,9317,
1859,539,9317,1859,605,605,605,91,605,605,33,605,91,605,605,33,33,605,
91,1859,1859,91,91,91,91,221,78125,117649,117649,12005,161051,117649,
161051,12005,1225,9317,161051,9317,9317,28561,117649,161051,161051,
9317,28561,12005,9317,1225,1225,539,9317,539,605,1859,161051,28561,
9317,539,1859,9317,605,539,1859,28561,1859,1859,1859,4913,9375,12005,
12005,1029,9317,12005,9317,1029,105,605,9317,605,605,1859,1125,1225,
1225,105,539,135,1225,1125,9375,12005,1225,12005,1029,9317,1225,539,
1225,12005,9317,105,1029,105,605,539,9317,605,605,1859,12005,9317,9317,
605,1859,1225,539,1225,12005,9317,539,9317,605,1859,1029,605,105,1029,
605,105,105,1029,605,605,605,605,33,91,9317,1859,539,9317,1859,605,605,
605,91,605,605,33,605,91,1859,1859,91,91,91,221,9375,12005,12005,1029,
9317,12005,9317,1029,105,605,9317,605,605,1859,1250,1029,1029,98,605,
150,105,150,1250,1029,105,1029,98,605,1029,605,105,1029,605,98,98,98,
33,605,605,33,33,91,1125,1225,1225,105,539,150,105,20,150,105,105,105,
98,605,135,1225,150,150,1029,1125,1250,9375,12005,1225,1029,12005,1029,
9317,1225,539,105,105,605,1225,1029,12005,9317,105,98,1029,105,605,539,
605,9317,605,605,1859,12005,9317,9317,605,1859,1029,605,105,1029,605,
605,605,33,91,1225,539,105,105,605,1225,1029,12005,9317,539,605,9317,
605,1859,1029,605,98,98,33,105,98,1029,605,105,98,105,1029,605,605,33,
605,605,33,91,9317,1859,605,605,91,539,605,9317,1859,605,33,605,605,91,
605,33,605,33,605,91,1859,91,1859,91,91,91,221,117649,161051,161051,
9317,28561,161051,28561,9317,539,1859,28561,1859,1859,4913,12005,9317,
9317,605,1859,1225,539,1225,12005,9317,539,9317,605,1859,9317,1859,539,
9317,1859,605,605,605,91,1859,1859,91,91,221,12005,9317,9317,605,1859,
1029,605,105,1029,605,605,605,33,91,1225,539,105,105,605,1225,1029,
12005,9317,539,605,9317,605,1859,9317,1859,605,605,91,539,605,9317,
1859,605,33,605,605,91,1859,91,1859,91,91,221,12005,9317,9317,605,1859,
1029,605,105,1029,605,605,605,33,91,1029,605,98,98,33,105,98,1029,605,
605,33,605,33,91,1225,539,105,105,605,105,98,105,605,1225,1029,1029,
12005,9317,539,605,605,9317,605,1859,9317,1859,605,605,91,605,33,605,
91,539,605,605,9317,1859,605,33,33,605,605,91,1859,91,91,1859,91,91,
221,161051,28561,28561,1859,4913,9317,1859,539,9317,1859,1859,1859,91,
221,9317,1859,605,605,91,539,605,9317,1859,1859,91,1859,91,221,9317,
1859,605,605,91,605,33,605,91,539,605,605,9317,1859,1859,91,91,1859,91,
221,9317,1859,605,605,91,605,33,605,91,605,33,33,605,91,539,605,605,
605,9317,1859,1859,91,91,91,1859,91,221,28561,4913,1859,1859,221,1859,
91,1859,221,1859,91,91,1859,221,1859,91,91,91,1859,221,1859,91,91,91,
91,1859,221,4913,221,221,221,221,221,221,361,6561,78125,78125,9375,
117649,78125,117649,9375,1125,12005,117649,12005,12005,161051,78125,
117649,117649,12005,161051,9375,12005,1125,135,1225,12005,1225,1029,
9317,117649,161051,12005,1225,9317,12005,1029,1225,9317,161051,9317,
9317,9317,28561,78125,117649,117649,12005,161051,117649,161051,12005,
1225,9317,161051,9317,9317,28561,9375,12005,12005,1029,9317,1125,1225,
135,1125,1225,1225,1225,105,539,12005,9317,1225,1225,539,1029,105,105,
605,9317,539,605,605,1859,117649,161051,161051,9317,28561,12005,9317,
1225,1225,539,9317,539,605,1859,12005,9317,1029,105,605,1225,105,1225,
539,9317,605,539,605,1859,161051,28561,9317,539,1859,9317,605,539,1859,
9317,605,605,539,1859,28561,1859,1859,1859,1859,4913,78125,117649,
117649,12005,161051,117649,161051,12005,1225,9317,161051,9317,9317,
28561,117649,161051,161051,9317,28561,12005,9317,1225,1225,539,9317,
539,605,1859,161051,28561,9317,539,1859,9317,605,539,1859,28561,1859,
1859,1859,4913,9375,12005,12005,1029,9317,12005,9317,1029,105,605,9317,
605,605,1859,1125,1225,1225,105,539,135,1225,1125,9375,12005,1225,
12005,1029,9317,1225,539,1225,12005,9317,105,1029,105,605,539,9317,605,
605,1859,12005,9317,9317,605,1859,1225,539,1225,12005,9317,539,9317,
605,1859,1029,605,105,1029,605,105,105,1029,605,605,605,605,33,91,9317,
1859,539,9317,1859,605,605,605,91,605,605,33,605,91,1859,1859,91,91,91,
221,117649,161051,161051,9317,28561,161051,28561,9317,539,1859,28561,
1859,1859,4913,12005,9317,9317,605,1859,1225,539,1225,12005,9317,539,
9317,605,1859,9317,1859,539,9317,1859,605,605,605,91,1859,1859,91,91,
221,12005,9317,9317,605,1859,1029,605,105,1029,605,605,605,33,91,1225,
539,105,105,605,1225,1029,12005,9317,539,605,9317,605,1859,9317,1859,
605,605,91,539,605,9317,1859,605,33,605,605,91,1859,91,1859,91,91,221,
161051,28561,28561,1859,4913,9317,1859,539,9317,1859,1859,1859,91,221,
9317,1859,605,605,91,539,605,9317,1859,1859,91,1859,91,221,9317,1859,
605,605,91,605,33,605,91,539,605,605,9317,1859,1859,91,91,1859,91,221,
28561,4913,1859,1859,221,1859,91,1859,221,1859,91,91,1859,221,1859,91,
91,91,1859,221,4913,221,221,221,221,221,361,1458,9375,9375,1250,12005,
9375,12005,1250,150,1029,12005,1029,1029,9317,9375,12005,12005,1029,
9317,1250,1029,150,150,105,1029,105,98,605,12005,9317,1029,105,605,
1029,98,105,605,9317,605,605,605,1859,9375,12005,12005,1029,9317,12005,
9317,1029,105,605,9317,605,605,1859,1250,1029,1029,98,605,150,105,150,
1250,1029,105,1029,98,605,1029,605,105,1029,605,98,98,98,33,605,605,33,
33,91,12005,9317,9317,605,1859,1029,605,105,1029,605,605,605,33,91,
1029,605,98,98,33,105,98,1029,605,605,33,605,33,91,9317,1859,605,605,
91,605,33,605,91,605,33,33,605,91,1859,91,91,91,91,221,324,1125,1125,
150,1225,1125,1225,150,20,105,1225,105,105,539,1125,1225,1225,105,539,
150,105,20,150,105,105,105,98,605,1225,539,105,105,605,105,98,105,605,
539,605,605,605,1859,72,135,135,150,1225,135,1225,150,150,1029,1225,
1029,1029,9317,72,1125,1125,1250,12005,324,9375,1458,6561,78125,9375,
78125,9375,117649,1125,12005,9375,78125,117649,1250,9375,1125,12005,
12005,117649,12005,12005,161051,135,1225,1225,1029,9317,1125,12005,
9375,78125,117649,12005,117649,12005,161051,150,1029,1250,9375,12005,
150,1125,135,1225,1029,12005,1225,1029,9317,1225,9317,12005,117649,
161051,1029,12005,1225,9317,1029,12005,1029,1225,9317,9317,161051,9317,
9317,9317,28561,1125,1225,1225,105,539,1225,539,105,105,605,539,605,
605,1859,135,1225,1225,1029,9317,1125,12005,9375,78125,117649,12005,
117649,12005,161051,1225,9317,12005,117649,161051,1029,12005,1225,9317,
9317,161051,9317,9317,28561,150,105,105,98,605,150,1029,1250,9375,
12005,1029,12005,1029,9317,20,105,150,1125,1225,150,135,1125,1225,105,
1225,1225,105,539,105,605,1029,12005,9317,105,1225,1225,539,98,1029,
105,105,605,605,9317,539,605,605,1859,1225,539,539,605,1859,1225,9317,
12005,117649,161051,9317,161051,9317,28561,105,605,1029,12005,9317,105,
1225,1225,539,605,9317,539,605,1859,105,605,1029,12005,9317,98,1029,
105,605,105,1225,105,1225,539,605,9317,605,539,605,1859,539,1859,9317,
161051,28561,605,9317,539,1859,605,9317,605,539,1859,605,9317,605,605,
539,1859,1859,28561,1859,1859,1859,1859,4913,9375,12005,12005,1029,
9317,12005,9317,1029,105,605,9317,605,605,1859,12005,9317,9317,605,
1859,1029,605,105,1029,605,605,605,33,91,9317,1859,605,605,91,605,33,
605,91,1859,91,91,91,221,1125,1225,1225,105,539,1225,539,105,105,605,
539,605,605,1859,135,1225,1225,1029,9317,1125,12005,9375,78125,117649,
12005,117649,12005,161051,1225,9317,12005,117649,161051,1029,12005,
1225,9317,9317,161051,9317,9317,28561,1225,539,539,605,1859,1225,9317,
12005,117649,161051,9317,161051,9317,28561,105,605,1029,12005,9317,105,
1225,1225,539,605,9317,539,605,1859,539,1859,9317,161051,28561,605,
9317,539,1859,605,9317,605,539,1859,1859,28561,1859,1859,1859,4913,
1250,1029,1029,98,605,1029,605,98,98,33,605,33,33,91,150,105,105,98,
605,150,1029,1250,9375,12005,1029,12005,1029,9317,105,605,1029,12005,
9317,98,1029,105,605,605,9317,605,605,1859,150,105,105,98,605,20,105,
150,1125,1225,105,1225,105,539,150,1029,150,135,1225,1250,1125,9375,
12005,1029,1225,12005,1029,9317,105,605,105,1225,539,1029,1225,12005,
9317,98,105,1029,105,605,605,539,9317,605,605,1859,1029,605,605,33,91,
105,605,1029,12005,9317,605,9317,605,1859,105,605,105,1225,539,1029,
1225,12005,9317,605,539,9317,605,1859,98,33,98,1029,605,98,105,1029,
605,98,105,105,1029,605,33,605,605,605,33,91,605,91,605,9317,1859,605,
539,9317,1859,33,605,605,605,91,33,605,605,33,605,91,91,1859,1859,91,
91,91,221,12005,9317,9317,605,1859,9317,1859,605,605,91,1859,91,91,221,
1225,539,539,605,1859,1225,9317,12005,117649,161051,9317,161051,9317,
28561,539,1859,9317,161051,28561,605,9317,539,1859,1859,28561,1859,
1859,4913,1029,605,605,33,91,105,605,1029,12005,9317,605,9317,605,1859,
105,605,105,1225,539,1029,1225,12005,9317,605,539,9317,605,1859,605,91,
605,9317,1859,605,539,9317,1859,33,605,605,605,91,91,1859,1859,91,91,
221,1029,605,605,33,91,105,605,1029,12005,9317,605,9317,605,1859,98,33,
98,1029,605,98,105,1029,605,33,605,605,33,91,105,605,105,1225,539,98,
105,105,605,1029,1225,1029,12005,9317,605,539,605,9317,605,1859,605,91,
605,9317,1859,33,605,605,91,605,539,605,9317,1859,33,605,33,605,605,91,
91,1859,91,1859,91,91,221,9317,1859,1859,91,221,539,1859,9317,161051,
28561,1859,28561,1859,4913,605,91,605,9317,1859,605,539,9317,1859,91,
1859,1859,91,221,605,91,605,9317,1859,33,605,605,91,605,539,605,9317,
1859,91,1859,91,1859,91,221,605,91,605,9317,1859,33,605,605,91,33,605,
33,605,91,605,539,605,605,9317,1859,91,1859,91,91,1859,91,221,1859,221,
1859,28561,4913,91,1859,1859,221,91,1859,91,1859,221,91,1859,91,91,
1859,221,91,1859,91,91,91,1859,221,221,4913,221,221,221,221,221,361,
78125,117649,117649,12005,161051,117649,161051,12005,1225,9317,161051,
9317,9317,28561,117649,161051,161051,9317,28561,12005,9317,1225,1225,
539,9317,539,605,1859,161051,28561,9317,539,1859,9317,605,539,1859,
28561,1859,1859,1859,4913,117649,161051,161051,9317,28561,161051,28561,
9317,539,1859,28561,1859,1859,4913,12005,9317,9317,605,1859,1225,539,
1225,12005,9317,539,9317,605,1859,9317,1859,539,9317,1859,605,605,605,
91,1859,1859,91,91,221,161051,28561,28561,1859,4913,9317,1859,539,9317,
1859,1859,1859,91,221,9317,1859,605,605,91,539,605,9317,1859,1859,91,
1859,91,221,28561,4913,1859,1859,221,1859,91,1859,221,1859,91,91,1859,
221,4913,221,221,221,221,361,9375,12005,12005,1029,9317,12005,9317,
1029,105,605,9317,605,605,1859,12005,9317,9317,605,1859,1029,605,105,
1029,605,605,605,33,91,9317,1859,605,605,91,605,33,605,91,1859,91,91,
91,221,1125,1225,1225,105,539,1225,539,105,105,605,539,605,605,1859,
135,1225,1225,1029,9317,1125,12005,9375,78125,117649,12005,117649,
12005,161051,1225,9317,12005,117649,161051,1029,12005,1225,9317,9317,
161051,9317,9317,28561,1225,539,539,605,1859,1225,9317,12005,117649,
161051,9317,161051,9317,28561,105,605,1029,12005,9317,105,1225,1225,
539,605,9317,539,605,1859,539,1859,9317,161051,28561,605,9317,539,1859,
605,9317,605,539,1859,1859,28561,1859,1859,1859,4913,12005,9317,9317,
605,1859,9317,1859,605,605,91,1859,91,91,221,1225,539,539,605,1859,
1225,9317,12005,117649,161051,9317,161051,9317,28561,539,1859,9317,
161051,28561,605,9317,539,1859,1859,28561,1859,1859,4913,1029,605,605,
33,91,105,605,1029,12005,9317,605,9317,605,1859,105,605,105,1225,539,
1029,1225,12005,9317,605,539,9317,605,1859,605,91,605,9317,1859,605,
539,9317,1859,33,605,605,605,91,91,1859,1859,91,91,221,9317,1859,1859,
91,221,539,1859,9317,161051,28561,1859,28561,1859,4913,605,91,605,9317,
1859,605,539,9317,1859,91,1859,1859,91,221,605,91,605,9317,1859,33,605,
605,91,605,539,605,9317,1859,91,1859,91,1859,91,221,1859,221,1859,
28561,4913,91,1859,1859,221,91,1859,91,1859,221,91,1859,91,91,1859,221,
221,4913,221,221,221,221,361,9375,12005,12005,1029,9317,12005,9317,
1029,105,605,9317,605,605,1859,12005,9317,9317,605,1859,1029,605,105,
1029,605,605,605,33,91,9317,1859,605,605,91,605,33,605,91,1859,91,91,
91,221,1250,1029,1029,98,605,1029,605,98,98,33,605,33,33,91,150,105,
105,98,605,150,1029,1250,9375,12005,1029,12005,1029,9317,105,605,1029,
12005,9317,98,1029,105,605,605,9317,605,605,1859,1029,605,605,33,91,
105,605,1029,12005,9317,605,9317,605,1859,98,33,98,1029,605,98,105,
1029,605,33,605,605,33,91,605,91,605,9317,1859,33,605,605,91,33,605,33,
605,91,91,1859,91,91,91,221,1125,1225,1225,105,539,1225,539,105,105,
605,539,605,605,1859,150,105,105,98,605,20,105,150,1125,1225,105,1225,
105,539,105,605,105,1225,539,98,105,105,605,605,539,605,605,1859,135,
1225,1225,1029,9317,150,1029,150,135,1225,1029,1225,1029,9317,1125,
12005,1250,1125,12005,9375,9375,78125,117649,12005,12005,117649,12005,
161051,1225,9317,1029,1225,9317,12005,12005,117649,161051,1029,1029,
12005,1225,9317,9317,9317,161051,9317,9317,28561,1225,539,539,605,1859,
105,605,105,1225,539,605,539,605,1859,1225,9317,1029,1225,9317,12005,
12005,117649,161051,9317,9317,161051,9317,28561,105,605,98,105,605,
1029,1029,12005,9317,105,105,1225,1225,539,605,605,9317,539,605,1859,
539,1859,605,539,1859,9317,9317,161051,28561,605,605,9317,539,1859,605,
605,9317,605,539,1859,1859,1859,28561,1859,1859,1859,4913,12005,9317,
9317,605,1859,9317,1859,605,605,91,1859,91,91,221,1029,605,605,33,91,
105,605,1029,12005,9317,605,9317,605,1859,605,91,605,9317,1859,33,605,
605,91,91,1859,91,91,221,1225,539,539,605,1859,105,605,105,1225,539,
605,539,605,1859,1225,9317,1029,1225,9317,12005,12005,117649,161051,
9317,9317,161051,9317,28561,539,1859,605,539,1859,9317,9317,161051,
28561,605,605,9317,539,1859,1859,1859,28561,1859,1859,4913,1029,605,
605,33,91,98,33,98,1029,605,33,605,33,91,105,605,98,105,605,1029,1029,
12005,9317,605,605,9317,605,1859,105,605,98,105,605,105,105,1225,539,
1029,1029,1225,12005,9317,605,605,539,9317,605,1859,605,91,33,605,91,
605,605,9317,1859,605,605,539,9317,1859,33,33,605,605,605,91,91,91,
1859,1859,91,91,221,9317,1859,1859,91,221,605,91,605,9317,1859,91,1859,
91,221,539,1859,605,539,1859,9317,9317,161051,28561,1859,1859,28561,
1859,4913,605,91,33,605,91,605,605,9317,1859,605,605,539,9317,1859,91,
91,1859,1859,91,221,605,91,33,605,91,605,605,9317,1859,33,33,605,605,
91,605,605,539,605,9317,1859,91,91,1859,91,1859,91,221,1859,221,91,
1859,221,1859,1859,28561,4913,91,91,1859,1859,221,91,91,1859,91,1859,
221,91,91,1859,91,91,1859,221,221,221,4913,221,221,221,221,361,117649,
161051,161051,9317,28561,161051,28561,9317,539,1859,28561,1859,1859,
4913,161051,28561,28561,1859,4913,9317,1859,539,9317,1859,1859,1859,91,
221,28561,4913,1859,1859,221,1859,91,1859,221,4913,221,221,221,361,
12005,9317,9317,605,1859,9317,1859,605,605,91,1859,91,91,221,1225,539,
539,605,1859,1225,9317,12005,117649,161051,9317,161051,9317,28561,539,
1859,9317,161051,28561,605,9317,539,1859,1859,28561,1859,1859,4913,
9317,1859,1859,91,221,539,1859,9317,161051,28561,1859,28561,1859,4913,
605,91,605,9317,1859,605,539,9317,1859,91,1859,1859,91,221,1859,221,
1859,28561,4913,91,1859,1859,221,91,1859,91,1859,221,221,4913,221,221,
221,361,12005,9317,9317,605,1859,9317,1859,605,605,91,1859,91,91,221,
1029,605,605,33,91,105,605,1029,12005,9317,605,9317,605,1859,605,91,
605,9317,1859,33,605,605,91,91,1859,91,91,221,1225,539,539,605,1859,
105,605,105,1225,539,605,539,605,1859,1225,9317,1029,1225,9317,12005,
12005,117649,161051,9317,9317,161051,9317,28561,539,1859,605,539,1859,
9317,9317,161051,28561,605,605,9317,539,1859,1859,1859,28561,1859,1859,
4913,9317,1859,1859,91,221,605,91,605,9317,1859,91,1859,91,221,539,
1859,605,539,1859,9317,9317,161051,28561,1859,1859,28561,1859,4913,605,
91,33,605,91,605,605,9317,1859,605,605,539,9317,1859,91,91,1859,1859,
91,221,1859,221,91,1859,221,1859,1859,28561,4913,91,91,1859,1859,221,
91,91,1859,91,1859,221,221,221,4913,221,221,221,361,12005,9317,9317,
605,1859,9317,1859,605,605,91,1859,91,91,221,1029,605,605,33,91,105,
605,1029,12005,9317,605,9317,605,1859,605,91,605,9317,1859,33,605,605,
91,91,1859,91,91,221,1029,605,605,33,91,98,33,98,1029,605,33,605,33,91,
105,605,98,105,605,1029,1029,12005,9317,605,605,9317,605,1859,605,91,
33,605,91,605,605,9317,1859,33,33,605,605,91,91,91,1859,91,91,221,1225,
539,539,605,1859,105,605,105,1225,539,605,539,605,1859,105,605,98,105,
605,105,105,1225,539,605,605,539,605,1859,1225,9317,1029,1225,9317,
1029,1029,1225,9317,12005,12005,12005,117649,161051,9317,9317,9317,
161051,9317,28561,539,1859,605,539,1859,605,605,539,1859,9317,9317,
9317,161051,28561,605,605,605,9317,539,1859,1859,1859,1859,28561,1859,
1859,4913,9317,1859,1859,91,221,605,91,605,9317,1859,91,1859,91,221,
605,91,33,605,91,605,605,9317,1859,91,91,1859,91,221,539,1859,605,539,
1859,605,605,539,1859,9317,9317,9317,161051,28561,1859,1859,1859,28561,
1859,4913,605,91,33,605,91,33,33,605,91,605,605,605,9317,1859,605,605,
605,539,9317,1859,91,91,91,1859,1859,91,221,1859,221,91,1859,221,91,91,
1859,221,1859,1859,1859,28561,4913,91,91,91,1859,1859,221,91,91,91,
1859,91,1859,221,221,221,221,4913,221,221,221,361,161051,28561,28561,
1859,4913,28561,4913,1859,1859,221,4913,221,221,361,9317,1859,1859,91,
221,539,1859,9317,161051,28561,1859,28561,1859,4913,1859,221,1859,
28561,4913,91,1859,1859,221,221,4913,221,221,361,9317,1859,1859,91,221,
605,91,605,9317,1859,91,1859,91,221,539,1859,605,539,1859,9317,9317,
161051,28561,1859,1859,28561,1859,4913,1859,221,91,1859,221,1859,1859,
28561,4913,91,91,1859,1859,221,221,221,4913,221,221,361,9317,1859,1859,
91,221,605,91,605,9317,1859,91,1859,91,221,605,91,33,605,91,605,605,
9317,1859,91,91,1859,91,221,539,1859,605,539,1859,605,605,539,1859,
9317,9317,9317,161051,28561,1859,1859,1859,28561,1859,4913,1859,221,91,
1859,221,91,91,1859,221,1859,1859,1859,28561,4913,91,91,91,1859,1859,
221,221,221,221,4913,221,221,361,9317,1859,1859,91,221,605,91,605,9317,
1859,91,1859,91,221,605,91,33,605,91,605,605,9317,1859,91,91,1859,91,
221,605,91,33,605,91,33,33,605,91,605,605,605,9317,1859,91,91,91,1859,
91,221,539,1859,605,539,1859,605,605,539,1859,605,605,605,539,1859,
9317,9317,9317,9317,161051,28561,1859,1859,1859,1859,28561,1859,4913,
1859,221,91,1859,221,91,91,1859,221,91,91,91,1859,221,1859,1859,1859,
1859,28561,4913,91,91,91,91,1859,1859,221,221,221,221,221,4913,221,221,
361,28561,4913,4913,221,361,1859,221,1859,28561,4913,221,4913,221,361,
1859,221,91,1859,221,1859,1859,28561,4913,221,221,4913,221,361,1859,
221,91,1859,221,91,91,1859,221,1859,1859,1859,28561,4913,221,221,221,
4913,221,361,1859,221,91,1859,221,91,91,1859,221,91,91,91,1859,221,
1859,1859,1859,1859,28561,4913,221,221,221,221,4913,221,361,1859,221,
91,1859,221,91,91,1859,221,91,91,91,1859,221,91,91,91,91,1859,221,1859,
1859,1859,1859,1859,28561,4913,221,221,221,221,221,4913,221,361,4913,
361,221,4913,361,221,221,4913,361,221,221,221,4913,361,221,221,221,221,
4913,361,221,221,221,221,221,4913,361,221,221,221,221,221,221,4913,361,
361,361,361,361,361,361,361,361,23};

ULI sA153835_up_to6917[6918] =
{0,1,2,2,4,4,6,4,4,9,9,11,9,9,14,14,14,9,9,14,11,9,9,23,23,25,23,23,28,
28,28,23,23,28,25,23,23,37,37,39,37,37,42,42,37,23,23,37,25,23,23,42,
42,39,28,28,37,28,23,23,37,28,25,23,23,65,65,67,65,65,70,70,70,65,65,
70,67,65,65,79,79,81,79,79,84,84,79,65,65,79,67,65,65,84,84,81,70,70,
79,70,65,65,79,70,67,65,65,107,107,109,107,107,112,112,112,107,107,112,
109,107,107,121,121,123,121,121,121,121,107,65,65,107,67,65,65,121,121,
109,70,70,107,70,65,65,107,70,67,65,65,121,121,123,121,121,123,123,112,
79,79,112,81,79,79,121,121,112,84,84,107,79,65,65,107,79,67,65,65,121,
121,112,84,84,109,81,70,70,107,79,70,65,65,107,79,70,67,65,65,197,197,
199,197,197,202,202,202,197,197,202,199,197,197,211,211,213,211,211,
216,216,211,197,197,211,199,197,197,216,216,213,202,202,211,202,197,
197,211,202,199,197,197,239,239,241,239,239,244,244,244,239,239,244,
241,239,239,253,253,255,253,253,253,253,239,197,197,239,199,197,197,
253,253,241,202,202,239,202,197,197,239,202,199,197,197,253,253,255,
253,253,255,255,244,211,211,244,213,211,211,253,253,244,216,216,239,
211,197,197,239,211,199,197,197,253,253,244,216,216,241,213,202,202,
239,211,202,197,197,239,211,202,199,197,197,329,329,331,329,329,334,
334,334,329,329,334,331,329,329,343,343,345,343,343,348,348,343,329,
329,343,331,329,329,348,348,345,334,334,343,334,329,329,343,334,331,
329,329,371,371,373,371,371,376,376,376,371,371,376,373,371,371,385,
385,387,385,385,371,371,329,197,197,329,199,197,197,371,371,331,202,
202,329,202,197,197,329,202,199,197,197,385,385,387,385,385,373,373,
334,211,211,334,213,211,211,371,371,334,216,216,329,211,197,197,329,
211,199,197,197,371,371,334,216,216,331,213,202,202,329,211,202,197,
197,329,211,202,199,197,197,371,371,373,371,371,376,376,376,371,371,
376,373,371,371,387,387,477,387,387,376,376,343,239,239,343,241,239,
239,376,376,345,244,244,343,244,239,239,343,244,241,239,239,385,385,
387,385,385,376,376,348,253,253,348,255,253,253,371,371,343,253,253,
329,239,197,197,329,239,199,197,197,371,371,343,253,253,331,241,202,
202,329,239,202,197,197,329,239,202,199,197,197,385,385,387,385,385,
376,376,348,253,253,348,255,253,253,373,373,345,255,255,334,244,211,
211,334,244,213,211,211,371,371,343,253,253,334,244,216,216,329,239,
211,197,197,329,239,211,199,197,197,371,371,343,253,253,334,244,216,
216,331,241,213,202,202,329,239,211,202,197,197,329,239,211,202,199,
197,197,626,626,628,626,626,631,631,631,626,626,631,628,626,626,640,
640,642,640,640,645,645,640,626,626,640,628,626,626,645,645,642,631,
631,640,631,626,626,640,631,628,626,626,668,668,670,668,668,673,673,
673,668,668,673,670,668,668,682,682,684,682,682,682,682,668,626,626,
668,628,626,626,682,682,670,631,631,668,631,626,626,668,631,628,626,
626,682,682,684,682,682,684,684,673,640,640,673,642,640,640,682,682,
673,645,645,668,640,626,626,668,640,628,626,626,682,682,673,645,645,
670,642,631,631,668,640,631,626,626,668,640,631,628,626,626,758,758,
760,758,758,763,763,763,758,758,763,760,758,758,772,772,774,772,772,
777,777,772,758,758,772,760,758,758,777,777,774,763,763,772,763,758,
758,772,763,760,758,758,800,800,802,800,800,805,805,805,800,800,805,
802,800,800,814,814,816,814,814,800,800,758,626,626,758,628,626,626,
800,800,760,631,631,758,631,626,626,758,631,628,626,626,814,814,816,
814,814,802,802,763,640,640,763,642,640,640,800,800,763,645,645,758,
640,626,626,758,640,628,626,626,800,800,763,645,645,760,642,631,631,
758,640,631,626,626,758,640,631,628,626,626,800,800,802,800,800,805,
805,805,800,800,805,802,800,800,816,816,906,816,816,805,805,772,668,
668,772,670,668,668,805,805,774,673,673,772,673,668,668,772,673,670,
668,668,814,814,816,814,814,805,805,777,682,682,777,684,682,682,800,
800,772,682,682,758,668,626,626,758,668,628,626,626,800,800,772,682,
682,760,670,631,631,758,668,631,626,626,758,668,631,628,626,626,814,
814,816,814,814,805,805,777,682,682,777,684,682,682,802,802,774,684,
684,763,673,640,640,763,673,642,640,640,800,800,772,682,682,763,673,
645,645,758,668,640,626,626,758,668,640,628,626,626,800,800,772,682,
682,763,673,645,645,760,670,642,631,631,758,668,640,631,626,626,758,
668,640,631,628,626,626,1055,1055,1057,1055,1055,1060,1060,1060,1055,
1055,1060,1057,1055,1055,1069,1069,1071,1069,1069,1074,1074,1069,1055,
1055,1069,1057,1055,1055,1074,1074,1071,1060,1060,1069,1060,1055,1055,
1069,1060,1057,1055,1055,1097,1097,1099,1097,1097,1102,1102,1102,1097,
1097,1102,1099,1097,1097,1111,1111,1113,1111,1111,1111,1111,1097,1055,
1055,1097,1057,1055,1055,1111,1111,1099,1060,1060,1097,1060,1055,1055,
1097,1060,1057,1055,1055,1111,1111,1113,1111,1111,1113,1113,1102,1069,
1069,1102,1071,1069,1069,1111,1111,1102,1074,1074,1097,1069,1055,1055,
1097,1069,1057,1055,1055,1111,1111,1102,1074,1074,1099,1071,1060,1060,
1097,1069,1060,1055,1055,1097,1069,1060,1057,1055,1055,1187,1187,1189,
1187,1187,1192,1192,1192,1187,1187,1192,1189,1187,1187,1201,1201,1203,
1201,1201,1206,1206,1201,1187,1187,1201,1189,1187,1187,1206,1206,1203,
1192,1192,1201,1192,1187,1187,1201,1192,1189,1187,1187,1229,1229,1231,
1229,1229,1234,1234,1234,1229,1229,1234,1231,1229,1229,1229,1229,1245,
1229,1229,1187,1187,1055,626,626,1055,628,626,626,1187,1187,1057,631,
631,1055,631,626,626,1055,631,628,626,626,1229,1229,1245,1229,1229,
1189,1189,1060,640,640,1060,642,640,640,1187,1187,1060,645,645,1055,
640,626,626,1055,640,628,626,626,1187,1187,1060,645,645,1057,642,631,
631,1055,640,631,626,626,1055,640,631,628,626,626,1229,1229,1231,1229,
1229,1234,1234,1234,1229,1229,1234,1231,1229,1229,1231,1231,1335,1231,
1231,1192,1192,1069,668,668,1069,670,668,668,1192,1192,1071,673,673,
1069,673,668,668,1069,673,670,668,668,1229,1229,1245,1229,1229,1192,
1192,1074,682,682,1074,684,682,682,1187,1187,1069,682,682,1055,668,626,
626,1055,668,628,626,626,1187,1187,1069,682,682,1057,670,631,631,1055,
668,631,626,626,1055,668,631,628,626,626,1229,1229,1245,1229,1229,1192,
1192,1074,682,682,1074,684,682,682,1189,1189,1071,684,684,1060,673,640,
640,1060,673,642,640,640,1187,1187,1069,682,682,1060,673,645,645,1055,
668,640,626,626,1055,668,640,628,626,626,1187,1187,1069,682,682,1060,
673,645,645,1057,670,642,631,631,1055,668,640,631,626,626,1055,668,640,
631,628,626,626,1187,1187,1189,1187,1187,1192,1192,1192,1187,1187,1192,
1189,1187,1187,1201,1201,1203,1201,1201,1206,1206,1201,1187,1187,1201,
1189,1187,1187,1206,1206,1203,1192,1192,1201,1192,1187,1187,1201,1192,
1189,1187,1187,1245,1245,1335,1245,1245,1531,1531,1531,1245,1245,1531,
1335,1245,1245,1234,1234,1531,1234,1234,1201,1201,1097,758,758,1097,
760,758,758,1201,1201,1099,763,763,1097,763,758,758,1097,763,760,758,
758,1234,1234,1531,1234,1234,1203,1203,1102,772,772,1102,774,772,772,
1201,1201,1102,777,777,1097,772,758,758,1097,772,760,758,758,1201,1201,
1102,777,777,1099,774,763,763,1097,772,763,758,758,1097,772,763,760,
758,758,1229,1229,1231,1229,1229,1234,1234,1234,1229,1229,1234,1231,
1229,1229,1234,1234,1531,1234,1234,1206,1206,1111,800,800,1111,802,800,
800,1206,1206,1113,805,805,1111,805,800,800,1111,805,802,800,800,1229,
1229,1245,1229,1229,1201,1201,1111,814,814,1111,816,814,814,1187,1187,
1097,800,800,1055,758,626,626,1055,758,628,626,626,1187,1187,1097,800,
800,1057,760,631,631,1055,758,631,626,626,1055,758,631,628,626,626,
1229,1229,1245,1229,1229,1201,1201,1111,814,814,1111,816,814,814,1189,
1189,1099,802,802,1060,763,640,640,1060,763,642,640,640,1187,1187,1097,
800,800,1060,763,645,645,1055,758,640,626,626,1055,758,640,628,626,626,
1187,1187,1097,800,800,1060,763,645,645,1057,760,642,631,631,1055,758,
640,631,626,626,1055,758,640,631,628,626,626,1229,1229,1231,1229,1229,
1234,1234,1234,1229,1229,1234,1231,1229,1229,1234,1234,1531,1234,1234,
1206,1206,1111,800,800,1111,802,800,800,1206,1206,1113,805,805,1111,
805,800,800,1111,805,802,800,800,1231,1231,1335,1231,1231,1203,1203,
1113,816,816,1113,906,816,816,1192,1192,1102,805,805,1069,772,668,668,
1069,772,670,668,668,1192,1192,1102,805,805,1071,774,673,673,1069,772,
673,668,668,1069,772,673,670,668,668,1229,1229,1245,1229,1229,1201,
1201,1111,814,814,1111,816,814,814,1192,1192,1102,805,805,1074,777,682,
682,1074,777,684,682,682,1187,1187,1097,800,800,1069,772,682,682,1055,
758,668,626,626,1055,758,668,628,626,626,1187,1187,1097,800,800,1069,
772,682,682,1057,760,670,631,631,1055,758,668,631,626,626,1055,758,668,
631,628,626,626,1229,1229,1245,1229,1229,1201,1201,1111,814,814,1111,
816,814,814,1192,1192,1102,805,805,1074,777,682,682,1074,777,684,682,
682,1189,1189,1099,802,802,1071,774,684,684,1060,763,673,640,640,1060,
763,673,642,640,640,1187,1187,1097,800,800,1069,772,682,682,1060,763,
673,645,645,1055,758,668,640,626,626,1055,758,668,640,628,626,626,1187,
1187,1097,800,800,1069,772,682,682,1060,763,673,645,645,1057,760,670,
642,631,631,1055,758,668,640,631,626,626,1055,758,668,640,631,628,626,
626,2056,2056,2058,2056,2056,2061,2061,2061,2056,2056,2061,2058,2056,
2056,2070,2070,2072,2070,2070,2075,2075,2070,2056,2056,2070,2058,2056,
2056,2075,2075,2072,2061,2061,2070,2061,2056,2056,2070,2061,2058,2056,
2056,2098,2098,2100,2098,2098,2103,2103,2103,2098,2098,2103,2100,2098,
2098,2112,2112,2114,2112,2112,2112,2112,2098,2056,2056,2098,2058,2056,
2056,2112,2112,2100,2061,2061,2098,2061,2056,2056,2098,2061,2058,2056,
2056,2112,2112,2114,2112,2112,2114,2114,2103,2070,2070,2103,2072,2070,
2070,2112,2112,2103,2075,2075,2098,2070,2056,2056,2098,2070,2058,2056,
2056,2112,2112,2103,2075,2075,2100,2072,2061,2061,2098,2070,2061,2056,
2056,2098,2070,2061,2058,2056,2056,2188,2188,2190,2188,2188,2193,2193,
2193,2188,2188,2193,2190,2188,2188,2202,2202,2204,2202,2202,2207,2207,
2202,2188,2188,2202,2190,2188,2188,2207,2207,2204,2193,2193,2202,2193,
2188,2188,2202,2193,2190,2188,2188,2230,2230,2232,2230,2230,2235,2235,
2235,2230,2230,2235,2232,2230,2230,2244,2244,2246,2244,2244,2230,2230,
2188,2056,2056,2188,2058,2056,2056,2230,2230,2190,2061,2061,2188,2061,
2056,2056,2188,2061,2058,2056,2056,2244,2244,2246,2244,2244,2232,2232,
2193,2070,2070,2193,2072,2070,2070,2230,2230,2193,2075,2075,2188,2070,
2056,2056,2188,2070,2058,2056,2056,2230,2230,2193,2075,2075,2190,2072,
2061,2061,2188,2070,2061,2056,2056,2188,2070,2061,2058,2056,2056,2230,
2230,2232,2230,2230,2235,2235,2235,2230,2230,2235,2232,2230,2230,2246,
2246,2336,2246,2246,2235,2235,2202,2098,2098,2202,2100,2098,2098,2235,
2235,2204,2103,2103,2202,2103,2098,2098,2202,2103,2100,2098,2098,2244,
2244,2246,2244,2244,2235,2235,2207,2112,2112,2207,2114,2112,2112,2230,
2230,2202,2112,2112,2188,2098,2056,2056,2188,2098,2058,2056,2056,2230,
2230,2202,2112,2112,2190,2100,2061,2061,2188,2098,2061,2056,2056,2188,
2098,2061,2058,2056,2056,2244,2244,2246,2244,2244,2235,2235,2207,2112,
2112,2207,2114,2112,2112,2232,2232,2204,2114,2114,2193,2103,2070,2070,
2193,2103,2072,2070,2070,2230,2230,2202,2112,2112,2193,2103,2075,2075,
2188,2098,2070,2056,2056,2188,2098,2070,2058,2056,2056,2230,2230,2202,
2112,2112,2193,2103,2075,2075,2190,2100,2072,2061,2061,2188,2098,2070,
2061,2056,2056,2188,2098,2070,2061,2058,2056,2056,2485,2485,2487,2485,
2485,2490,2490,2490,2485,2485,2490,2487,2485,2485,2499,2499,2501,2499,
2499,2504,2504,2499,2485,2485,2499,2487,2485,2485,2504,2504,2501,2490,
2490,2499,2490,2485,2485,2499,2490,2487,2485,2485,2527,2527,2529,2527,
2527,2532,2532,2532,2527,2527,2532,2529,2527,2527,2541,2541,2543,2541,
2541,2541,2541,2527,2485,2485,2527,2487,2485,2485,2541,2541,2529,2490,
2490,2527,2490,2485,2485,2527,2490,2487,2485,2485,2541,2541,2543,2541,
2541,2543,2543,2532,2499,2499,2532,2501,2499,2499,2541,2541,2532,2504,
2504,2527,2499,2485,2485,2527,2499,2487,2485,2485,2541,2541,2532,2504,
2504,2529,2501,2490,2490,2527,2499,2490,2485,2485,2527,2499,2490,2487,
2485,2485,2617,2617,2619,2617,2617,2622,2622,2622,2617,2617,2622,2619,
2617,2617,2631,2631,2633,2631,2631,2636,2636,2631,2617,2617,2631,2619,
2617,2617,2636,2636,2633,2622,2622,2631,2622,2617,2617,2631,2622,2619,
2617,2617,2659,2659,2661,2659,2659,2664,2664,2664,2659,2659,2664,2661,
2659,2659,2659,2659,2675,2659,2659,2617,2617,2485,2056,2056,2485,2058,
2056,2056,2617,2617,2487,2061,2061,2485,2061,2056,2056,2485,2061,2058,
2056,2056,2659,2659,2675,2659,2659,2619,2619,2490,2070,2070,2490,2072,
2070,2070,2617,2617,2490,2075,2075,2485,2070,2056,2056,2485,2070,2058,
2056,2056,2617,2617,2490,2075,2075,2487,2072,2061,2061,2485,2070,2061,
2056,2056,2485,2070,2061,2058,2056,2056,2659,2659,2661,2659,2659,2664,
2664,2664,2659,2659,2664,2661,2659,2659,2661,2661,2765,2661,2661,2622,
2622,2499,2098,2098,2499,2100,2098,2098,2622,2622,2501,2103,2103,2499,
2103,2098,2098,2499,2103,2100,2098,2098,2659,2659,2675,2659,2659,2622,
2622,2504,2112,2112,2504,2114,2112,2112,2617,2617,2499,2112,2112,2485,
2098,2056,2056,2485,2098,2058,2056,2056,2617,2617,2499,2112,2112,2487,
2100,2061,2061,2485,2098,2061,2056,2056,2485,2098,2061,2058,2056,2056,
2659,2659,2675,2659,2659,2622,2622,2504,2112,2112,2504,2114,2112,2112,
2619,2619,2501,2114,2114,2490,2103,2070,2070,2490,2103,2072,2070,2070,
2617,2617,2499,2112,2112,2490,2103,2075,2075,2485,2098,2070,2056,2056,
2485,2098,2070,2058,2056,2056,2617,2617,2499,2112,2112,2490,2103,2075,
2075,2487,2100,2072,2061,2061,2485,2098,2070,2061,2056,2056,2485,2098,
2070,2061,2058,2056,2056,2617,2617,2619,2617,2617,2622,2622,2622,2617,
2617,2622,2619,2617,2617,2631,2631,2633,2631,2631,2636,2636,2631,2617,
2617,2631,2619,2617,2617,2636,2636,2633,2622,2622,2631,2622,2617,2617,
2631,2622,2619,2617,2617,2675,2675,2765,2675,2675,2961,2961,2961,2675,
2675,2961,2765,2675,2675,2664,2664,2961,2664,2664,2631,2631,2527,2188,
2188,2527,2190,2188,2188,2631,2631,2529,2193,2193,2527,2193,2188,2188,
2527,2193,2190,2188,2188,2664,2664,2961,2664,2664,2633,2633,2532,2202,
2202,2532,2204,2202,2202,2631,2631,2532,2207,2207,2527,2202,2188,2188,
2527,2202,2190,2188,2188,2631,2631,2532,2207,2207,2529,2204,2193,2193,
2527,2202,2193,2188,2188,2527,2202,2193,2190,2188,2188,2659,2659,2661,
2659,2659,2664,2664,2664,2659,2659,2664,2661,2659,2659,2664,2664,2961,
2664,2664,2636,2636,2541,2230,2230,2541,2232,2230,2230,2636,2636,2543,
2235,2235,2541,2235,2230,2230,2541,2235,2232,2230,2230,2659,2659,2675,
2659,2659,2631,2631,2541,2244,2244,2541,2246,2244,2244,2617,2617,2527,
2230,2230,2485,2188,2056,2056,2485,2188,2058,2056,2056,2617,2617,2527,
2230,2230,2487,2190,2061,2061,2485,2188,2061,2056,2056,2485,2188,2061,
2058,2056,2056,2659,2659,2675,2659,2659,2631,2631,2541,2244,2244,2541,
2246,2244,2244,2619,2619,2529,2232,2232,2490,2193,2070,2070,2490,2193,
2072,2070,2070,2617,2617,2527,2230,2230,2490,2193,2075,2075,2485,2188,
2070,2056,2056,2485,2188,2070,2058,2056,2056,2617,2617,2527,2230,2230,
2490,2193,2075,2075,2487,2190,2072,2061,2061,2485,2188,2070,2061,2056,
2056,2485,2188,2070,2061,2058,2056,2056,2659,2659,2661,2659,2659,2664,
2664,2664,2659,2659,2664,2661,2659,2659,2664,2664,2961,2664,2664,2636,
2636,2541,2230,2230,2541,2232,2230,2230,2636,2636,2543,2235,2235,2541,
2235,2230,2230,2541,2235,2232,2230,2230,2661,2661,2765,2661,2661,2633,
2633,2543,2246,2246,2543,2336,2246,2246,2622,2622,2532,2235,2235,2499,
2202,2098,2098,2499,2202,2100,2098,2098,2622,2622,2532,2235,2235,2501,
2204,2103,2103,2499,2202,2103,2098,2098,2499,2202,2103,2100,2098,2098,
2659,2659,2675,2659,2659,2631,2631,2541,2244,2244,2541,2246,2244,2244,
2622,2622,2532,2235,2235,2504,2207,2112,2112,2504,2207,2114,2112,2112,
2617,2617,2527,2230,2230,2499,2202,2112,2112,2485,2188,2098,2056,2056,
2485,2188,2098,2058,2056,2056,2617,2617,2527,2230,2230,2499,2202,2112,
2112,2487,2190,2100,2061,2061,2485,2188,2098,2061,2056,2056,2485,2188,
2098,2061,2058,2056,2056,2659,2659,2675,2659,2659,2631,2631,2541,2244,
2244,2541,2246,2244,2244,2622,2622,2532,2235,2235,2504,2207,2112,2112,
2504,2207,2114,2112,2112,2619,2619,2529,2232,2232,2501,2204,2114,2114,
2490,2193,2103,2070,2070,2490,2193,2103,2072,2070,2070,2617,2617,2527,
2230,2230,2499,2202,2112,2112,2490,2193,2103,2075,2075,2485,2188,2098,
2070,2056,2056,2485,2188,2098,2070,2058,2056,2056,2617,2617,2527,2230,
2230,2499,2202,2112,2112,2490,2193,2103,2075,2075,2487,2190,2100,2072,
2061,2061,2485,2188,2098,2070,2061,2056,2056,2485,2188,2098,2070,2061,
2058,2056,2056,3486,3486,3488,3486,3486,3491,3491,3491,3486,3486,3491,
3488,3486,3486,3500,3500,3502,3500,3500,3505,3505,3500,3486,3486,3500,
3488,3486,3486,3505,3505,3502,3491,3491,3500,3491,3486,3486,3500,3491,
3488,3486,3486,3528,3528,3530,3528,3528,3533,3533,3533,3528,3528,3533,
3530,3528,3528,3542,3542,3544,3542,3542,3542,3542,3528,3486,3486,3528,
3488,3486,3486,3542,3542,3530,3491,3491,3528,3491,3486,3486,3528,3491,
3488,3486,3486,3542,3542,3544,3542,3542,3544,3544,3533,3500,3500,3533,
3502,3500,3500,3542,3542,3533,3505,3505,3528,3500,3486,3486,3528,3500,
3488,3486,3486,3542,3542,3533,3505,3505,3530,3502,3491,3491,3528,3500,
3491,3486,3486,3528,3500,3491,3488,3486,3486,3618,3618,3620,3618,3618,
3623,3623,3623,3618,3618,3623,3620,3618,3618,3632,3632,3634,3632,3632,
3637,3637,3632,3618,3618,3632,3620,3618,3618,3637,3637,3634,3623,3623,
3632,3623,3618,3618,3632,3623,3620,3618,3618,3660,3660,3662,3660,3660,
3665,3665,3665,3660,3660,3665,3662,3660,3660,3674,3674,3676,3674,3674,
3660,3660,3618,3486,3486,3618,3488,3486,3486,3660,3660,3620,3491,3491,
3618,3491,3486,3486,3618,3491,3488,3486,3486,3674,3674,3676,3674,3674,
3662,3662,3623,3500,3500,3623,3502,3500,3500,3660,3660,3623,3505,3505,
3618,3500,3486,3486,3618,3500,3488,3486,3486,3660,3660,3623,3505,3505,
3620,3502,3491,3491,3618,3500,3491,3486,3486,3618,3500,3491,3488,3486,
3486,3660,3660,3662,3660,3660,3665,3665,3665,3660,3660,3665,3662,3660,
3660,3676,3676,3766,3676,3676,3665,3665,3632,3528,3528,3632,3530,3528,
3528,3665,3665,3634,3533,3533,3632,3533,3528,3528,3632,3533,3530,3528,
3528,3674,3674,3676,3674,3674,3665,3665,3637,3542,3542,3637,3544,3542,
3542,3660,3660,3632,3542,3542,3618,3528,3486,3486,3618,3528,3488,3486,
3486,3660,3660,3632,3542,3542,3620,3530,3491,3491,3618,3528,3491,3486,
3486,3618,3528,3491,3488,3486,3486,3674,3674,3676,3674,3674,3665,3665,
3637,3542,3542,3637,3544,3542,3542,3662,3662,3634,3544,3544,3623,3533,
3500,3500,3623,3533,3502,3500,3500,3660,3660,3632,3542,3542,3623,3533,
3505,3505,3618,3528,3500,3486,3486,3618,3528,3500,3488,3486,3486,3660,
3660,3632,3542,3542,3623,3533,3505,3505,3620,3530,3502,3491,3491,3618,
3528,3500,3491,3486,3486,3618,3528,3500,3491,3488,3486,3486,3915,3915,
3917,3915,3915,3920,3920,3920,3915,3915,3920,3917,3915,3915,3929,3929,
3931,3929,3929,3934,3934,3929,3915,3915,3929,3917,3915,3915,3934,3934,
3931,3920,3920,3929,3920,3915,3915,3929,3920,3917,3915,3915,3957,3957,
3959,3957,3957,3962,3962,3962,3957,3957,3962,3959,3957,3957,3971,3971,
3973,3971,3971,3971,3971,3957,3915,3915,3957,3917,3915,3915,3971,3971,
3959,3920,3920,3957,3920,3915,3915,3957,3920,3917,3915,3915,3971,3971,
3973,3971,3971,3973,3973,3962,3929,3929,3962,3931,3929,3929,3971,3971,
3962,3934,3934,3957,3929,3915,3915,3957,3929,3917,3915,3915,3971,3971,
3962,3934,3934,3959,3931,3920,3920,3957,3929,3920,3915,3915,3957,3929,
3920,3917,3915,3915,4047,4047,4049,4047,4047,4052,4052,4052,4047,4047,
4052,4049,4047,4047,4061,4061,4063,4061,4061,4066,4066,4061,4047,4047,
4061,4049,4047,4047,4066,4066,4063,4052,4052,4061,4052,4047,4047,4061,
4052,4049,4047,4047,4089,4089,4091,4089,4089,4094,4094,4094,4089,4089,
4094,4091,4089,4089,4047,4047,4105,4047,4047,3915,3915,3486,2056,2056,
3486,2058,2056,2056,3915,3915,3488,2061,2061,3486,2061,2056,2056,3486,
2061,2058,2056,2056,4047,4047,4105,4047,4047,3917,3917,3491,2070,2070,
3491,2072,2070,2070,3915,3915,3491,2075,2075,3486,2070,2056,2056,3486,
2070,2058,2056,2056,3915,3915,3491,2075,2075,3488,2072,2061,2061,3486,
2070,2061,2056,2056,3486,2070,2061,2058,2056,2056,4089,4089,4091,4089,
4089,4094,4094,4094,4089,4089,4094,4091,4089,4089,4049,4049,4195,4049,
4049,3920,3920,3500,2098,2098,3500,2100,2098,2098,3920,3920,3502,2103,
2103,3500,2103,2098,2098,3500,2103,2100,2098,2098,4047,4047,4105,4047,
4047,3920,3920,3505,2112,2112,3505,2114,2112,2112,3915,3915,3500,2112,
2112,3486,2098,2056,2056,3486,2098,2058,2056,2056,3915,3915,3500,2112,
2112,3488,2100,2061,2061,3486,2098,2061,2056,2056,3486,2098,2061,2058,
2056,2056,4047,4047,4105,4047,4047,3920,3920,3505,2112,2112,3505,2114,
2112,2112,3917,3917,3502,2114,2114,3491,2103,2070,2070,3491,2103,2072,
2070,2070,3915,3915,3500,2112,2112,3491,2103,2075,2075,3486,2098,2070,
2056,2056,3486,2098,2070,2058,2056,2056,3915,3915,3500,2112,2112,3491,
2103,2075,2075,3488,2100,2072,2061,2061,3486,2098,2070,2061,2056,2056,
3486,2098,2070,2061,2058,2056,2056,4047,4047,4049,4047,4047,4052,4052,
4052,4047,4047,4052,4049,4047,4047,4061,4061,4063,4061,4061,4066,4066,
4061,4047,4047,4061,4049,4047,4047,4066,4066,4063,4052,4052,4061,4052,
4047,4047,4061,4052,4049,4047,4047,4091,4091,4388,4091,4091,4391,4391,
4391,4091,4091,4391,4388,4091,4091,4052,4052,4402,4052,4052,3929,3929,
3528,2188,2188,3528,2190,2188,2188,3929,3929,3530,2193,2193,3528,2193,
2188,2188,3528,2193,2190,2188,2188,4052,4052,4402,4052,4052,3931,3931,
3533,2202,2202,3533,2204,2202,2202,3929,3929,3533,2207,2207,3528,2202,
2188,2188,3528,2202,2190,2188,2188,3929,3929,3533,2207,2207,3530,2204,
2193,2193,3528,2202,2193,2188,2188,3528,2202,2193,2190,2188,2188,4089,
4089,4091,4089,4089,4094,4094,4094,4089,4089,4094,4091,4089,4089,4052,
4052,4402,4052,4052,3934,3934,3542,2230,2230,3542,2232,2230,2230,3934,
3934,3544,2235,2235,3542,2235,2230,2230,3542,2235,2232,2230,2230,4047,
4047,4105,4047,4047,3929,3929,3542,2244,2244,3542,2246,2244,2244,3915,
3915,3528,2230,2230,3486,2188,2056,2056,3486,2188,2058,2056,2056,3915,
3915,3528,2230,2230,3488,2190,2061,2061,3486,2188,2061,2056,2056,3486,
2188,2061,2058,2056,2056,4047,4047,4105,4047,4047,3929,3929,3542,2244,
2244,3542,2246,2244,2244,3917,3917,3530,2232,2232,3491,2193,2070,2070,
3491,2193,2072,2070,2070,3915,3915,3528,2230,2230,3491,2193,2075,2075,
3486,2188,2070,2056,2056,3486,2188,2070,2058,2056,2056,3915,3915,3528,
2230,2230,3491,2193,2075,2075,3488,2190,2072,2061,2061,3486,2188,2070,
2061,2056,2056,3486,2188,2070,2061,2058,2056,2056,4089,4089,4091,4089,
4089,4094,4094,4094,4089,4089,4094,4091,4089,4089,4052,4052,4402,4052,
4052,3934,3934,3542,2230,2230,3542,2232,2230,2230,3934,3934,3544,2235,
2235,3542,2235,2230,2230,3542,2235,2232,2230,2230,4049,4049,4195,4049,
4049,3931,3931,3544,2246,2246,3544,2336,2246,2246,3920,3920,3533,2235,
2235,3500,2202,2098,2098,3500,2202,2100,2098,2098,3920,3920,3533,2235,
2235,3502,2204,2103,2103,3500,2202,2103,2098,2098,3500,2202,2103,2100,
2098,2098,4047,4047,4105,4047,4047,3929,3929,3542,2244,2244,3542,2246,
2244,2244,3920,3920,3533,2235,2235,3505,2207,2112,2112,3505,2207,2114,
2112,2112,3915,3915,3528,2230,2230,3500,2202,2112,2112,3486,2188,2098,
2056,2056,3486,2188,2098,2058,2056,2056,3915,3915,3528,2230,2230,3500,
2202,2112,2112,3488,2190,2100,2061,2061,3486,2188,2098,2061,2056,2056,
3486,2188,2098,2061,2058,2056,2056,4047,4047,4105,4047,4047,3929,3929,
3542,2244,2244,3542,2246,2244,2244,3920,3920,3533,2235,2235,3505,2207,
2112,2112,3505,2207,2114,2112,2112,3917,3917,3530,2232,2232,3502,2204,
2114,2114,3491,2193,2103,2070,2070,3491,2193,2103,2072,2070,2070,3915,
3915,3528,2230,2230,3500,2202,2112,2112,3491,2193,2103,2075,2075,3486,
2188,2098,2070,2056,2056,3486,2188,2098,2070,2058,2056,2056,3915,3915,
3528,2230,2230,3500,2202,2112,2112,3491,2193,2103,2075,2075,3488,2190,
2100,2072,2061,2061,3486,2188,2098,2070,2061,2056,2056,3486,2188,2098,
2070,2061,2058,2056,2056,3915,3915,3917,3915,3915,3920,3920,3920,3915,
3915,3920,3917,3915,3915,3929,3929,3931,3929,3929,3934,3934,3929,3915,
3915,3929,3917,3915,3915,3934,3934,3931,3920,3920,3929,3920,3915,3915,
3929,3920,3917,3915,3915,3957,3957,3959,3957,3957,3962,3962,3962,3957,
3957,3962,3959,3957,3957,3971,3971,3973,3971,3971,3971,3971,3957,3915,
3915,3957,3917,3915,3915,3971,3971,3959,3920,3920,3957,3920,3915,3915,
3957,3920,3917,3915,3915,3971,3971,3973,3971,3971,3973,3973,3962,3929,
3929,3962,3931,3929,3929,3971,3971,3962,3934,3934,3957,3929,3915,3915,
3957,3929,3917,3915,3915,3971,3971,3962,3934,3934,3959,3931,3920,3920,
3957,3929,3920,3915,3915,3957,3929,3920,3917,3915,3915,4105,4105,4195,
4105,4105,4402,4402,4402,4105,4105,4402,4195,4105,4105,5062,5062,5064,
5062,5062,5067,5067,5062,4105,4105,5062,4195,4105,4105,5067,5067,5064,
4402,4402,5062,4402,4105,4105,5062,4402,4195,4105,4105,4094,4094,4391,
4094,4094,5095,5095,5095,4094,4094,5095,4391,4094,4094,4061,4061,5062,
4061,4061,3957,3957,3618,2485,2485,3618,2487,2485,2485,3957,3957,3620,
2490,2490,3618,2490,2485,2485,3618,2490,2487,2485,2485,4061,4061,5062,
4061,4061,3959,3959,3623,2499,2499,3623,2501,2499,2499,3957,3957,3623,
2504,2504,3618,2499,2485,2485,3618,2499,2487,2485,2485,3957,3957,3623,
2504,2504,3620,2501,2490,2490,3618,2499,2490,2485,2485,3618,2499,2490,
2487,2485,2485,4094,4094,4391,4094,4094,5095,5095,5095,4094,4094,5095,
4391,4094,4094,4063,4063,5064,4063,4063,3962,3962,3632,2527,2527,3632,
2529,2527,2527,3962,3962,3634,2532,2532,3632,2532,2527,2527,3632,2532,
2529,2527,2527,4061,4061,5062,4061,4061,3962,3962,3637,2541,2541,3637,
2543,2541,2541,3957,3957,3632,2541,2541,3618,2527,2485,2485,3618,2527,
2487,2485,2485,3957,3957,3632,2541,2541,3620,2529,2490,2490,3618,2527,
2490,2485,2485,3618,2527,2490,2487,2485,2485,4061,4061,5062,4061,4061,
3962,3962,3637,2541,2541,3637,2543,2541,2541,3959,3959,3634,2543,2543,
3623,2532,2499,2499,3623,2532,2501,2499,2499,3957,3957,3632,2541,2541,
3623,2532,2504,2504,3618,2527,2499,2485,2485,3618,2527,2499,2487,2485,
2485,3957,3957,3632,2541,2541,3623,2532,2504,2504,3620,2529,2501,2490,
2490,3618,2527,2499,2490,2485,2485,3618,2527,2499,2490,2487,2485,2485,
4047,4047,4049,4047,4047,4052,4052,4052,4047,4047,4052,4049,4047,4047,
4061,4061,4063,4061,4061,4066,4066,4061,4047,4047,4061,4049,4047,4047,
4066,4066,4063,4052,4052,4061,4052,4047,4047,4061,4052,4049,4047,4047,
4094,4094,4391,4094,4094,5095,5095,5095,4094,4094,5095,4391,4094,4094,
4066,4066,5067,4066,4066,3971,3971,3660,2617,2617,3660,2619,2617,2617,
3971,3971,3662,2622,2622,3660,2622,2617,2617,3660,2622,2619,2617,2617,
4066,4066,5067,4066,4066,3973,3973,3665,2631,2631,3665,2633,2631,2631,
3971,3971,3665,2636,2636,3660,2631,2617,2617,3660,2631,2619,2617,2617,
3971,3971,3665,2636,2636,3662,2633,2622,2622,3660,2631,2622,2617,2617,
3660,2631,2622,2619,2617,2617,4089,4089,4091,4089,4089,4094,4094,4094,
4089,4089,4094,4091,4089,4089,4061,4061,5062,4061,4061,3971,3971,3674,
2659,2659,3674,2661,2659,2659,3971,3971,3676,2664,2664,3674,2664,2659,
2659,3674,2664,2661,2659,2659,4047,4047,4105,4047,4047,3957,3957,3660,
2659,2659,3660,2675,2659,2659,3915,3915,3618,2617,2617,3486,2485,2056,
2056,3486,2485,2058,2056,2056,3915,3915,3618,2617,2617,3488,2487,2061,
2061,3486,2485,2061,2056,2056,3486,2485,2061,2058,2056,2056,4047,4047,
4105,4047,4047,3957,3957,3660,2659,2659,3660,2675,2659,2659,3917,3917,
3620,2619,2619,3491,2490,2070,2070,3491,2490,2072,2070,2070,3915,3915,
3618,2617,2617,3491,2490,2075,2075,3486,2485,2070,2056,2056,3486,2485,
2070,2058,2056,2056,3915,3915,3618,2617,2617,3491,2490,2075,2075,3488,
2487,2072,2061,2061,3486,2485,2070,2061,2056,2056,3486,2485,2070,2061,
2058,2056,2056,4089,4089,4091,4089,4089,4094,4094,4094,4089,4089,4094,
4091,4089,4089,4061,4061,5062,4061,4061,3971,3971,3674,2659,2659,3674,
2661,2659,2659,3971,3971,3676,2664,2664,3674,2664,2659,2659,3674,2664,
2661,2659,2659,4049,4049,4195,4049,4049,3959,3959,3662,2661,2661,3662,
2765,2661,2661,3920,3920,3623,2622,2622,3500,2499,2098,2098,3500,2499,
2100,2098,2098,3920,3920,3623,2622,2622,3502,2501,2103,2103,3500,2499,
2103,2098,2098,3500,2499,2103,2100,2098,2098,4047,4047,4105,4047,4047,
3957,3957,3660,2659,2659,3660,2675,2659,2659,3920,3920,3623,2622,2622,
3505,2504,2112,2112,3505,2504,2114,2112,2112,3915,3915,3618,2617,2617,
3500,2499,2112,2112,3486,2485,2098,2056,2056,3486,2485,2098,2058,2056,
2056,3915,3915,3618,2617,2617,3500,2499,2112,2112,3488,2487,2100,2061,
2061,3486,2485,2098,2061,2056,2056,3486,2485,2098,2061,2058,2056,2056,
4047,4047,4105,4047,4047,3957,3957,3660,2659,2659,3660,2675,2659,2659,
3920,3920,3623,2622,2622,3505,2504,2112,2112,3505,2504,2114,2112,2112,
3917,3917,3620,2619,2619,3502,2501,2114,2114,3491,2490,2103,2070,2070,
3491,2490,2103,2072,2070,2070,3915,3915,3618,2617,2617,3500,2499,2112,
2112,3491,2490,2103,2075,2075,3486,2485,2098,2070,2056,2056,3486,2485,
2098,2070,2058,2056,2056,3915,3915,3618,2617,2617,3500,2499,2112,2112,
3491,2490,2103,2075,2075,3488,2487,2100,2072,2061,2061,3486,2485,2098,
2070,2061,2056,2056,3486,2485,2098,2070,2061,2058,2056,2056,4047,4047,
4049,4047,4047,4052,4052,4052,4047,4047,4052,4049,4047,4047,4061,4061,
4063,4061,4061,4066,4066,4061,4047,4047,4061,4049,4047,4047,4066,4066,
4063,4052,4052,4061,4052,4047,4047,4061,4052,4049,4047,4047,4094,4094,
4391,4094,4094,5095,5095,5095,4094,4094,5095,4391,4094,4094,4066,4066,
5067,4066,4066,3971,3971,3660,2617,2617,3660,2619,2617,2617,3971,3971,
3662,2622,2622,3660,2622,2617,2617,3660,2622,2619,2617,2617,4066,4066,
5067,4066,4066,3973,3973,3665,2631,2631,3665,2633,2631,2631,3971,3971,
3665,2636,2636,3660,2631,2617,2617,3660,2631,2619,2617,2617,3971,3971,
3665,2636,2636,3662,2633,2622,2622,3660,2631,2622,2617,2617,3660,2631,
2622,2619,2617,2617,4091,4091,4388,4091,4091,4391,4391,4391,4091,4091,
4391,4388,4091,4091,4063,4063,5064,4063,4063,3973,3973,3676,2675,2675,
3676,2765,2675,2675,3973,3973,3766,2961,2961,3676,2961,2675,2675,3676,
2961,2765,2675,2675,4052,4052,4402,4052,4052,3962,3962,3665,2664,2664,
3665,2961,2664,2664,3929,3929,3632,2631,2631,3528,2527,2188,2188,3528,
2527,2190,2188,2188,3929,3929,3632,2631,2631,3530,2529,2193,2193,3528,
2527,2193,2188,2188,3528,2527,2193,2190,2188,2188,4052,4052,4402,4052,
4052,3962,3962,3665,2664,2664,3665,2961,2664,2664,3931,3931,3634,2633,
2633,3533,2532,2202,2202,3533,2532,2204,2202,2202,3929,3929,3632,2631,
2631,3533,2532,2207,2207,3528,2527,2202,2188,2188,3528,2527,2202,2190,
2188,2188,3929,3929,3632,2631,2631,3533,2532,2207,2207,3530,2529,2204,
2193,2193,3528,2527,2202,2193,2188,2188,3528,2527,2202,2193,2190,2188,
2188,4089,4089,4091,4089,4089,4094,4094,4094,4089,4089,4094,4091,4089,
4089,4061,4061,5062,4061,4061,3971,3971,3674,2659,2659,3674,2661,2659,
2659,3971,3971,3676,2664,2664,3674,2664,2659,2659,3674,2664,2661,2659,
2659,4052,4052,4402,4052,4052,3962,3962,3665,2664,2664,3665,2961,2664,
2664,3934,3934,3637,2636,2636,3542,2541,2230,2230,3542,2541,2232,2230,
2230,3934,3934,3637,2636,2636,3544,2543,2235,2235,3542,2541,2235,2230,
2230,3542,2541,2235,2232,2230,2230,4047,4047,4105,4047,4047,3957,3957,
3660,2659,2659,3660,2675,2659,2659,3929,3929,3632,2631,2631,3542,2541,
2244,2244,3542,2541,2246,2244,2244,3915,3915,3618,2617,2617,3528,2527,
2230,2230,3486,2485,2188,2056,2056,3486,2485,2188,2058,2056,2056,3915,
3915,3618,2617,2617,3528,2527,2230,2230,3488,2487,2190,2061,2061,3486,
2485,2188,2061,2056,2056,3486,2485,2188,2061,2058,2056,2056,4047,4047,
4105,4047,4047,3957,3957,3660,2659,2659,3660,2675,2659,2659,3929,3929,
3632,2631,2631,3542,2541,2244,2244,3542,2541,2246,2244,2244,3917,3917,
3620,2619,2619,3530,2529,2232,2232,3491,2490,2193,2070,2070,3491,2490,
2193,2072,2070,2070,3915,3915,3618,2617,2617,3528,2527,2230,2230,3491,
2490,2193,2075,2075,3486,2485,2188,2070,2056,2056,3486,2485,2188,2070,
2058,2056,2056,3915,3915,3618,2617,2617,3528,2527,2230,2230,3491,2490,
2193,2075,2075,3488,2487,2190,2072,2061,2061,3486,2485,2188,2070,2061,
2056,2056,3486,2485,2188,2070,2061,2058,2056,2056,4089,4089,4091,4089,
4089,4094,4094,4094,4089,4089,4094,4091,4089,4089,4061,4061,5062,4061,
4061,3971,3971,3674,2659,2659,3674,2661,2659,2659,3971,3971,3676,2664,
2664,3674,2664,2659,2659,3674,2664,2661,2659,2659,4052,4052,4402,4052,
4052,3962,3962,3665,2664,2664,3665,2961,2664,2664,3934,3934,3637,2636,
2636,3542,2541,2230,2230,3542,2541,2232,2230,2230,3934,3934,3637,2636,
2636,3544,2543,2235,2235,3542,2541,2235,2230,2230,3542,2541,2235,2232,
2230,2230,4049,4049,4195,4049,4049,3959,3959,3662,2661,2661,3662,2765,
2661,2661,3931,3931,3634,2633,2633,3544,2543,2246,2246,3544,2543,2336,
2246,2246,3920,3920,3623,2622,2622,3533,2532,2235,2235,3500,2499,2202,
2098,2098,3500,2499,2202,2100,2098,2098,3920,3920,3623,2622,2622,3533,
2532,2235,2235,3502,2501,2204,2103,2103,3500,2499,2202,2103,2098,2098,
3500,2499,2202,2103,2100,2098,2098,4047,4047,4105,4047,4047,3957,3957,
3660,2659,2659,3660,2675,2659,2659,3929,3929,3632,2631,2631,3542,2541,
2244,2244,3542,2541,2246,2244,2244,3920,3920,3623,2622,2622,3533,2532,
2235,2235,3505,2504,2207,2112,2112,3505,2504,2207,2114,2112,2112,3915,
3915,3618,2617,2617,3528,2527,2230,2230,3500,2499,2202,2112,2112,3486,
2485,2188,2098,2056,2056,3486,2485,2188,2098,2058,2056,2056,3915,3915,
3618,2617,2617,3528,2527,2230,2230,3500,2499,2202,2112,2112,3488,2487,
2190,2100,2061,2061,3486,2485,2188,2098,2061,2056,2056,3486,2485,2188,
2098,2061,2058,2056,2056,4047,4047,4105,4047,4047,3957,3957,3660,2659,
2659,3660,2675,2659,2659,3929,3929,3632,2631,2631,3542,2541,2244,2244,
3542,2541,2246,2244,2244,3920,3920,3623,2622,2622,3533,2532,2235,2235,
3505,2504,2207,2112,2112,3505,2504,2207,2114,2112,2112,3917,3917,3620,
2619,2619,3530,2529,2232,2232,3502,2501,2204,2114,2114,3491,2490,2193,
2103,2070,2070,3491,2490,2193,2103,2072,2070,2070,3915,3915,3618,2617,
2617,3528,2527,2230,2230,3500,2499,2202,2112,2112,3491,2490,2193,2103,
2075,2075,3486,2485,2188,2098,2070,2056,2056,3486,2485,2188,2098,2070,
2058,2056,2056,3915,3915,3618,2617,2617,3528,2527,2230,2230,3500,2499,
2202,2112,2112,3491,2490,2193,2103,2075,2075,3488,2487,2190,2100,2072,
2061,2061,3486,2485,2188,2098,2070,2061,2056,2056,3486,2485,2188,2098,
2070,2061,2058,2056,2056};
