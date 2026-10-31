// LHC clock: for driver word w (periodic, phase offset ph), starts with leftmost black at depth W,
// the driven left half (positions -1..-(W+t)), mask: at black driver times t, col(-1,t) = !c(t+1).
// Report max over starts and phases of the first violation time.
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
int main(int argc,char**argv){
  const char*w=argv[1]; int P=strlen(w); int Wmax=atoi(argv[2]);
  for(int W=2;W<=Wmax;W++){
    int worst=-1; long surv=0;
    for(int ph=0;ph<P;ph++)
    for(uint64_t m=0;m<(1ull<<(W-1));m++){
      // bit i of x = cell at depth i+1 (position -(i+1)); depth W is black, deeper white
      u128 x=((u128)m) | ((u128)1<<(W-1));
      int t; int bad=-1;
      for(t=0;t<4*W+40;t++){
        int ct=w[(t+ph)%P]-'0', cn=w[(t+1+ph)%P]-'0';
        int col=(int)(x&1);
        if(ct && col!=!cn){bad=t;break;}
        // step: new depth d cell = cell(d+1) ^ (cell(d) | cell(d-1)), depth 0 = driver c(t)
        u128 left=x>>1;              // cell at depth d+1 placed at d
        u128 right=(x<<1)|(u128)ct;  // cell at depth d-1
        x=left^(x|right);
        if(W+t+2>127) break;
      }
      if(bad<0){surv++;} else if(bad>worst) worst=bad;
    }
    printf("%s W=%d max_first_violation=%d survivors=%ld\n",w,W,worst,surv);
    fflush(stdout);
  }
}
