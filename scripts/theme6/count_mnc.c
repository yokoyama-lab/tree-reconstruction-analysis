/* Comparison COUNTER + cross-check for M, N, and Algorithm C.
 *
 * Extends count_v2.c with Algorithm C (algorithm_c.tex, Fig. 1): the
 * single-stack, single-loop algorithm that pushes only genuine future
 * parents (right-child condition) and grafts each right child with ONE pop.
 *
 * Conventions (identical to count_v2.c so totals are comparable):
 *   - i-p sequence ip[] holds inorder labels 1..n; TERM = 0; sentinel n+1.
 *   - EVERY test an algorithm evaluates is counted (label comparisons +
 *     end/structural tests + the loop guard the algorithm actually pays).
 *     M and C use a for-loop and pay the i<n guard; N uses while(1)+break
 *     and does not -- this is intrinsic to each algorithm as published.
 *
 * For C we also report cC_db, the data-dependent count that excludes the
 * input-independent for-guard (the figure algorithm_c.tex quotes as 2n-2,
 * reachable by unrolling the guard).
 *
 * C's reconstructed tree is cross-checked against N's on every input
 * (CvsN = OK/FAIL), an empirical complement to the Rocq proof.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned long long rng_s;
static inline unsigned long long rng_next(void){unsigned long long z=(rng_s+=0x9E3779B97F4A7C15ULL);z=(z^(z>>30))*0xBF58476D1CE4E5B9ULL;z=(z^(z>>27))*0x94D049BB133111EBULL;return z^(z>>31);}
static inline unsigned long long rng_below(unsigned long long m){return rng_next()%m;}

static int *Lc,*Rc,*inlbl,*ip,ip_len,*estk;
static int *slot_owner,*slot_side,*slot_val,root_child;
static int *cL,*cR,*nL,*nR;

static void gen_remy(int n){
    int ns=0; slot_owner[0]=0;slot_side[0]=0;slot_val[0]=0;ns=1; root_child=0;
    for(int k=1;k<=n;k++){ int x=(int)rng_below((unsigned long long)ns); int sub=slot_val[x],owner=slot_owner[x],oside=slot_side[x]; int newid=k,coin=(int)rng_below(2ULL);
        slot_val[x]=newid; if(owner==0)root_child=newid; else if(oside==0)Lc[owner]=newid; else Rc[owner]=newid;
        if(coin==0){Lc[newid]=sub;Rc[newid]=0; slot_owner[ns]=newid;slot_side[ns]=0;slot_val[ns]=sub;ns++; slot_owner[ns]=newid;slot_side[ns]=1;slot_val[ns]=0;ns++;}
        else{Lc[newid]=0;Rc[newid]=sub; slot_owner[ns]=newid;slot_side[ns]=0;slot_val[ns]=0;ns++; slot_owner[ns]=newid;slot_side[ns]=1;slot_val[ns]=sub;ns++;} }
    int sp=0,cur=root_child,lbl=1; for(;;){while(cur>0){estk[sp++]=cur;cur=Lc[cur];}if(sp==0)break;cur=estk[--sp];inlbl[cur]=lbl++;cur=Rc[cur];}
    ip_len=0;sp=0;estk[sp++]=root_child; while(sp){int v=estk[--sp];ip[ip_len++]=inlbl[v];if(Rc[v]>0)estk[sp++]=Rc[v];if(Lc[v]>0)estk[sp++]=Lc[v];}
}
static void gen_best(int n){for(int i=0;i<n;i++)ip[i]=n-i;ip_len=n;}
static void gen_mworst(int n){for(int i=0;i<n;i++)ip[i]=i+1;ip_len=n;}
static void gen_nworst(int n){int i=0;for(;i+1<n;i+=2){ip[i]=i+2;ip[i+1]=i+1;}if(i<n)ip[i]=n;ip_len=n;}

/* --- Makinen M (count_v2.c, verbatim) --- */
static void count_M(int n,long*plbl,long*pend){
    int *stk=estk,sp=0; long lbl=0,end=0; int X=n+1;
    stk[sp++]=X; stk[sp++]=ip[0]; int index=1;
    while(end++, index<n){
        int cur=ip[index];
        lbl++;
        if(cur<stk[sp-1]){ stk[sp++]=cur; }
        else { int prev; do{ prev=stk[--sp]; lbl++; }while(cur>=stk[sp-1]);
               stk[sp++]=cur; (void)prev; }
        index++;
    }
    *plbl=lbl; *pend=end;
}
/* --- Improved N (count_v2.c, verbatim) --- */
static void count_N(int n,long*plbl,long*pend){
    int *stk=estk,sp=0; long lbl=0,end=0; int NV=n+1;
    ip[n]=NV; stk[sp++]=NV; stk[sp++]=ip[0]; int i=1;
    while(1){
        if(end++, ip[i]<stk[sp-1]){
            stk[sp++]=ip[i];
        } else {
            sp--;
            if(end++, ip[i]>=stk[sp-1]){
                if(lbl++, i>=n) break;
                do { sp--; } while(end++, ip[i]>=stk[sp-1]);
            }
            stk[sp++]=ip[i];
        }
        i++;
    }
    *plbl=lbl; *pend=end;
}
/* N's reconstructed tree (trusted reference), label-indexed. */
static void build_N(int n){
    for(int k=0;k<=n+1;k++){nL[k]=0;nR[k]=0;}
    int *stk=estk,sp=0; int X=n+1;
    stk[sp++]=X; stk[sp++]=ip[0];
    for(int i=1;i<n;i++){
        if(stk[sp-1] > ip[i]){ nL[stk[sp-1]]=ip[i]; }
        else { int prev; do{ prev=stk[--sp]; }while(stk[sp-1] <= ip[i]); nR[prev]=ip[i]; }
        stk[sp++]=ip[i];
    }
}

/* --- Algorithm C (algorithm_c.tex, Fig. 1) --- builds cL/cR and counts.
 * lbl = order comparisons ip[i-1]>ip[i]; end = loop guard + structural test.
 * Total = 3n-2; data-dependent (no guard) = 2n-2. */
static void count_C(int n,long*plbl,long*pend){
    long lbl=0,end=0;
    for(int k=0;k<=n+1;k++){cL[k]=0;cR[k]=0;}
    int *stk=estk,sp=0;
    stk[sp++]=ip[0];                       /* PUSH(ip[0]) */
    int i=1;
    while(end++, i<n){                      /* loop guard i<n */
        if(lbl++, ip[i-1] > ip[i]){         /* order comparison */
            cL[ip[i-1]] = ip[i];            /* left child */
        } else {
            cR[stk[--sp]] = ip[i];          /* right child: single POP */
        }
        if(end++, cL[ip[i]+1]==0){          /* structural test: a[ip[i]+1].l==TERM */
            stk[sp++]=ip[i];                /* PUSH(ip[i]) */
        }
        i++;
    }
    *plbl=lbl; *pend=end;
}

int main(int argc,char**argv){
    int n=atoi(argv[1]); const char*mode=argc>2?argv[2]:"rand"; rng_s=argc>3?strtoull(argv[3],0,10):12345ULL;
    int csv=getenv("CSV")!=NULL;
    size_t sz=n+8; Lc=calloc(sz,4);Rc=calloc(sz,4);inlbl=malloc(sz*4);ip=malloc(sz*4);estk=malloc(sz*4);
    cL=malloc(sz*4);cR=malloc(sz*4);nL=malloc(sz*4);nR=malloc(sz*4);
    slot_owner=malloc((2*n+8)*4);slot_side=malloc((2*n+8)*4);slot_val=malloc((2*n+8)*4);
    if(!strcmp(mode,"best"))gen_best(n); else if(!strcmp(mode,"mworst"))gen_mworst(n); else if(!strcmp(mode,"nworst"))gen_nworst(n); else gen_remy(n);

    long lM,eM,lN,eN,lC,eC; count_M(n,&lM,&eM); count_N(n,&lN,&eN); count_C(n,&lC,&eC);
    long cM=lM+eM, cN=lN+eN, cC=lC+eC, cC_db=lC+(eC-n); /* drop the n loop-guard tests */

    /* cross-check C's tree against N's */
    build_N(n);
    int ok=1; for(int k=1;k<=n;k++){ if(cL[k]!=nL[k]||cR[k]!=nR[k]){ok=0;break;} }

    if(csv) printf("%s,%d,%ld,%ld,%ld,%ld,%.4f,%.4f,%.4f,%.4f,%s\n",
                   mode,n,cM,cN,cC,cC_db,(double)cM/n,(double)cN/n,(double)cC/n,(double)cC_db/n,ok?"OK":"FAIL");
    else printf("%-7s n=%-8d  M=%ld (%.3fn)  N=%ld (%.3fn)  C=%ld (%.3fn)  C_db=%ld (%.3fn)  CvsN=%s\n",
                mode,n,cM,(double)cM/n,cN,(double)cN/n,cC,(double)cC/n,cC_db,(double)cC_db/n,ok?"OK":"FAIL");
    return 0;
}
